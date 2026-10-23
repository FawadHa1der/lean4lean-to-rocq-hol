#!/usr/bin/env python3
# Copyright (c) 2026 Fawad Haider. All rights reserved.
"""Run any standalone checker against a pinned, language-neutral Arena manifest."""

import argparse
from collections import Counter
from datetime import datetime, timezone
import errno
import fnmatch
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import traceback


DEFAULT_MANIFEST = Path(__file__).resolve().parents[1] / "arena/manifest.json"
VERDICTS = {0: "accept", 1: "reject", 2: "decline", 3: "fault"}
FAILURES = {"wrong_accept", "wrong_reject", "fault", "timeout", "input_error", "execution_error"}
GAPS = {"declined", "skipped", "missing_download", "missing_generated"}
CLEANUP_REAP_SECONDS = 10


def utc_now():
    return datetime.now(timezone.utc).isoformat()


def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def checker_fingerprint(checker):
    """Bind the command's executable and explicit file arguments, not its whole closure."""
    command = shlex.split(checker)
    artifacts = []
    for index, argument in enumerate(command):
        if "$IN" in argument or "${IN}" in argument:
            continue
        candidate = shutil.which(argument) if index == 0 else argument
        if candidate is None:
            continue
        try:
            path = Path(candidate)
            if path.is_file():
                artifacts.append({"argument_index": index, "argument": argument,
                                  "resolved_path": str(path.resolve()),
                                  "size": path.stat().st_size, "sha256": digest(path)})
        except OSError as exc:
            artifacts.append({"argument_index": index, "argument": argument,
                              "error": str(exc)})
    return artifacts


def relative_path(root, value):
    if not isinstance(value, str) or not value or "\\" in value:
        raise ValueError("input path must be a nonempty relative POSIX path")
    path = Path(value)
    if path.is_absolute() or ".." in path.parts:
        raise ValueError("input path must stay within the manifest directory")
    resolved = (root / path).resolve()
    if not resolved.is_relative_to(root.resolve()):
        raise ValueError("input path escapes the manifest directory through a symlink")
    return resolved


def positive_seconds(value):
    value = float(value)
    if not math.isfinite(value) or value <= 0:
        raise ValueError("timeout must be finite and positive")
    return value


def load_manifest(path):
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict) or data.get("manifest_version") != 1:
        raise ValueError("unsupported manifest_version (expected 1)")
    cases = data.get("cases")
    if not isinstance(cases, list) or not cases:
        raise ValueError("manifest cases must be a nonempty array")
    seen = set()
    for case in cases:
        if not isinstance(case, dict):
            raise ValueError("each case must be an object")
        name = case.get("id")
        if not isinstance(name, str) or not name or name in seen:
            raise ValueError(f"invalid or duplicate case id: {name!r}")
        seen.add(name)
        if case.get("expected") not in {"accept", "reject", "either"}:
            raise ValueError(f"{name}: expected must be accept, reject, or either")
        if case.get("availability") not in {"available", "missing_download", "missing_generated"}:
            raise ValueError(f"{name}: invalid availability")
        relative_path(path.parent, case.get("path"))
        if case.get("availability") == "available":
            if not re.fullmatch(r"[a-f0-9]{64}", case.get("sha256", "")):
                raise ValueError(f"{name}: available input needs a SHA-256")
            if type(case.get("size")) is not int or case["size"] < 0:
                raise ValueError(f"{name}: available input needs a byte size")
        if "timeout_seconds" in case:
            positive_seconds(case["timeout_seconds"])
        if "skip_reason" in case and not isinstance(case["skip_reason"], str):
            raise ValueError(f"{name}: skip_reason must be a string")
    return data


def classify(code, expected):
    if code == 2:
        return "declined"
    if code not in (0, 1):
        return "fault"
    if expected == "either":
        return "acceptable_either"
    verdict = VERDICTS[code]
    return ("correct_" if verdict == expected else "wrong_") + verdict


def make_command(checker, path, input_mode):
    command = shlex.split(checker)
    if not command:
        raise ValueError("--checker must not be empty")
    placeholder = any("$IN" in arg or "${IN}" in arg for arg in command)
    command = [arg.replace("${IN}", str(path)).replace("$IN", str(path)) for arg in command]
    if input_mode == "file" and not placeholder:
        command.append(str(path))
    return command


class ProcessExecutionError(OSError):
    """An operational failure with the evidence collected before it occurred."""

    def __init__(self, cause, evidence):
        super().__init__(str(cause))
        self.evidence = evidence


def error_evidence(operation, exc):
    return {"operation": operation, "type": type(exc).__name__,
            "errno": getattr(exc, "errno", None), "message": str(exc),
            "traceback": "".join(traceback.format_exception(exc))}


class ProcessCleanupError(Exception):
    def __init__(self, receipt, failures):
        super().__init__("owned process cleanup not verified")
        self.receipt = receipt
        self.failures = failures


def require_default_sigchld():
    """Never reset a caller's handler or spawn with automatic/external reaping."""
    handler = signal.getsignal(signal.SIGCHLD)
    if handler is not signal.SIG_DFL:
        raise OSError(errno.EINVAL, f"sole-reaper ownership requires SIGCHLD SIG_DFL; observed {handler!r}")


def stop_group(proc, observe=lambda operation, action: action()):
    """Sole reaper of a start_new_session child; no competing waitpid/handler.

    Adapted from the reviewed cleanup_owned_process helper: reserve the numeric
    group by its unreaped leader, then only observe after reaping. A surviving
    or reused PID/group is a failure, never permission to signal it again.
    """
    failures = []
    actions = []

    def attempt(operation, action):
        try:
            return observe(operation, action)
        except BaseException as exc:
            failures.append((operation, exc))
            return None

    def poll_unreaped():
        return proc.poll() is None

    def signal_owned_group():
        # No poll/wait or concurrent reaper may intervene before this signal.
        try:
            os.killpg(proc.pid, signal.SIGKILL)
            actions.append("owned_unreaped_group_kill")
            return True
        except ProcessLookupError:
            actions.append("owned_group_already_absent")
            return False

    def kill_direct_handle():
        try:
            proc.kill()
            actions.append("direct_handle_kill")
        except ProcessLookupError:
            actions.append("direct_handle_already_absent")

    unreaped = attempt("poll_process", poll_unreaped)
    group_signalled = False
    if unreaped and os.name == "posix":
        group_signalled = attempt("kill_process_group", signal_owned_group)
    if proc.returncode is None:
        if not group_signalled:
            attempt("kill_direct_handle", kill_direct_handle)
        attempt("reap_process", lambda: proc.wait(timeout=CLEANUP_REAP_SECONDS))

    presence = {}
    if os.name == "posix":
        for name, probe in (("pid_absent", os.kill), ("process_group_absent", os.killpg)):
            def absent(probe=probe):
                try:
                    probe(proc.pid, 0)
                    return False
                except ProcessLookupError:
                    return True
            presence[name] = attempt(name, absent)

    reaped = proc.returncode is not None
    verified = reaped and all(value is True for value in presence.values()) and not failures
    if not verified and not failures:
        failures.append(("verify_cleanup", OSError(errno.EBUSY, "child not reaped or PID/group still present")))
    receipt = dict(presence, pid=proc.pid, reaped=reaped, actions=actions,
                   reap_timeout_seconds=CLEANUP_REAP_SECONDS,
                   absence_scope="posix_pid_and_group" if os.name == "posix" else "direct_child_only",
                   verified=verified,
                   errors=[error_evidence(operation, exc) for operation, exc in failures])
    if not verified:
        raise ProcessCleanupError(receipt, failures)
    return receipt


def run_process(command, path, timeout, input_mode, max_log_bytes):
    env = os.environ.copy()
    env["IN"] = str(path)
    start = time.monotonic()
    # Drain both streams continuously while keeping only bounded diagnostic prefixes.
    # Pipes avoid unbounded on-disk logs from a faulty checker.
    import threading

    logs = {"stdout": bytearray(), "stderr": bytearray()}
    totals = {"stdout": 0, "stderr": 0}
    errors = []
    observed_errors = {}
    observed_actions = set()
    error_lock = threading.Lock()
    proc = source = None
    threads = []
    pending = None
    timed_out = False
    group_stop_returned = False
    cleanup = None
    wait_timeout = None
    sigchld_default_verified = None

    def record_error(operation, exc, *, propagation=False):
        # Reader threads can report simultaneously. Retain the objects, not only
        # their ids; distinguish new actions from propagation through wrappers.
        with error_lock:
            identity = id(exc)
            if propagation and identity in observed_errors:
                return
            key = (operation, identity)
            if key in observed_actions:
                return
            errors.append(error_evidence(operation, exc))
            observed_errors[identity] = exc
            observed_actions.add(key)

    def observe(operation, action):
        try:
            return action()
        except Exception as exc:
            if operation == "wait_process" and isinstance(exc, subprocess.TimeoutExpired):
                raise  # The caller distinguishes the case deadline from cleanup failure.
            record_error(operation, exc)
            raise

    def drain(stream, key):
        try:
            while chunk := observe(f"read_{key}", lambda: stream.read(65536)):
                totals[key] += len(chunk)
                remaining = max_log_bytes - len(logs[key])
                if remaining > 0:
                    logs[key].extend(chunk[:remaining])
        except Exception as exc:
            record_error(f"read_{key}", exc, propagation=True)
        finally:
            try:
                observe(f"close_{key}", stream.close)
            except Exception:
                pass

    try:
        source = observe("open_input", lambda: path.open("rb"))
        if os.name == "posix":
            sigchld_default_verified = False
            observe("verify_sigchld_default", require_default_sigchld)
            sigchld_default_verified = True
        # This call path is the sole wait/poll owner. Readers only drain pipes;
        # no other reaper or SIGCHLD disposition change is permitted after here.
        proc = observe("spawn_process", lambda: subprocess.Popen(
            command, env=env, stdin=source if input_mode == "stdin" else subprocess.DEVNULL,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=os.name == "posix",
        ))
        threads = [threading.Thread(target=drain, args=(stream, key), daemon=True)
                   for stream, key in ((proc.stdout, "stdout"), (proc.stderr, "stderr"))]
        for thread in threads:
            observe("start_log_reader", thread.start)
        try:
            observe("wait_process", lambda: proc.wait(timeout=timeout))
            # Children may inherit pipes after the leader exits. Bound that wait too.
            for thread in threads:
                observe("wait_log_reader", lambda: thread.join(max(0, timeout - (time.monotonic() - start))))
            timed_out = any(thread.is_alive() for thread in threads)
        except subprocess.TimeoutExpired as exc:
            timed_out = True
            wait_timeout = error_evidence("wait_process", exc)
    except BaseException as exc:
        pending = exc
        record_error("process_setup_or_wait", exc, propagation=True)
    finally:
        # Preserve the original error even if cleanup encounters another one.
        if proc is not None:
            try:
                cleanup = stop_group(proc, observe)
                group_stop_returned = True
                if not isinstance(cleanup, dict) or cleanup.get("verified") is not True:
                    raise OSError(errno.EIO, "cleanup returned no verified receipt")
            except ProcessCleanupError as exc:
                cleanup = exc.receipt
                for operation, failure in exc.failures:
                    record_error(operation, failure)
                if pending is None:
                    pending = next((failure for _, failure in exc.failures
                                    if not isinstance(failure, Exception)), exc)
            except BaseException as exc:
                record_error("stop_group", exc, propagation=True)
                if pending is None:
                    pending = exc
        for thread in threads:
            if thread.ident is not None:
                try:
                    observe("finish_log_reader", lambda: thread.join(1))
                except BaseException as exc:
                    record_error("finish_log_reader", exc, propagation=True)
                    if pending is None:
                        pending = exc
        readers_stopped = all(thread.ident is None or not thread.is_alive() for thread in threads)
        if not readers_stopped:
            record_error("finish_log_readers", OSError(errno.EBUSY, "log reader still active after bounded joins"))
        if proc is not None:
            for index, stream in enumerate((proc.stdout, proc.stderr)):
                if index >= len(threads) or threads[index].ident is None:
                    try:
                        observe("close_unstarted_reader", stream.close)
                    except BaseException as exc:
                        record_error("close_unstarted_reader", exc, propagation=True)
                        if pending is None:
                            pending = exc
        if source is not None:
            try:
                observe("close_input", source.close)
            except BaseException as exc:
                record_error("close_input", exc, propagation=True)
                if pending is None:
                    pending = exc
    if pending is not None and isinstance(pending, Exception):
        record_error("process_execution", pending, propagation=True)
    with error_lock:
        error_snapshot = list(errors)
    code = proc.returncode if proc is not None else None
    result = {
        "exit_code": code,
        "verdict": VERDICTS.get(code, "fault") if code is not None else None,
        "process_id": proc.pid if proc is not None else None,
        "sigchld_default_verified": sigchld_default_verified,
        "group_stop_returned": group_stop_returned,
        "cleanup": cleanup,
        "cleanup_verified": (proc is None or (isinstance(cleanup, dict) and cleanup.get("verified") is True)) and readers_stopped,
        "capture_complete": (len(threads) == 2
                             and all(thread.ident is not None and not thread.is_alive() for thread in threads)
                             and not any(e["operation"].startswith("read_") for e in error_snapshot)),
        "elapsed_seconds": round(time.monotonic() - start, 6),
        "timed_out": timed_out,
        "wait_timeout": wait_timeout,
        **{key: bytes(logs[key]).decode("utf-8", errors="replace") for key in logs},
        **{f"{key}_bytes": totals[key] for key in logs},
        **{f"{key}_truncated": totals[key] > max_log_bytes for key in logs},
    }
    if pending is not None and not isinstance(pending, Exception):
        result["execution_errors"] = error_snapshot
        pending.arena_evidence = result
        pending.add_note("Arena process/cleanup evidence attached as arena_evidence")
        raise pending
    if pending is not None or error_snapshot:
        result["execution_errors"] = error_snapshot
        raise ProcessExecutionError(pending or error_snapshot[0]["message"], result) from pending
    return result


def run_case(case, root, args):
    result = {key: case[key] for key in ("id", "expected", "availability")}
    result["source_kind"] = case.get("source_kind", "unknown")
    result["exit_code"] = None
    if args.select and not any(fnmatch.fnmatchcase(case["id"], pat) for pat in args.select):
        return {**result, "status": "skipped", "reason": "not selected"}
    for pattern, reason in args.skip:
        if fnmatch.fnmatchcase(case["id"], pattern):
            return {**result, "status": "skipped", "reason": reason}
    if case.get("skip_reason"):
        return {**result, "status": "skipped", "reason": case["skip_reason"]}
    if case["availability"] != "available":
        return {**result, "status": case["availability"], "reason": case.get("missing_reason", "unavailable")}
    operation = "resolve_input"
    try:
        path = relative_path(root, case["path"])
        operation = "verify_input_before_execution"
        if not path.is_file():
            return {**result, "status": "input_error", "reason": "manifest says available but input is absent"}
        if path.stat().st_size != case["size"] or digest(path) != case["sha256"]:
            return {**result, "status": "input_error", "reason": "input size/SHA-256 differs from manifest"}
        timeout = args.timeout if args.timeout is not None else case.get("timeout_seconds", args.default_timeout)
        result["timeout_seconds"] = timeout
        result["input_sha256"] = case["sha256"]
        command = make_command(args.checker, path, args.input_mode)
        operation = "run_process"
        result.update(run_process(command, path, timeout, args.input_mode, args.max_log_bytes))
        result["status"] = "timeout" if result["timed_out"] else classify(result["exit_code"], case["expected"])
        operation = "verify_input_after_execution"
        if not path.is_file() or path.stat().st_size != case["size"] or digest(path) != case["sha256"]:
            return {**result, "status": "input_error", "reason": "input changed during checker execution"}
        if result["status"] == "declined":
            result["decline_kind"] = "checker_declared"
            result["reason"] = "exit 2: unsupported input or resource decline; not a proof verdict"
    except ProcessExecutionError as exc:
        result.update(exc.evidence)
        result.update(status="execution_error", reason=str(exc))
    except OSError as exc:
        result.update(status="execution_error", reason=str(exc))
        result.setdefault("execution_errors", []).append(error_evidence(operation, exc))
    return result


def summary(results):
    counts = Counter(item["status"] for item in results)
    return {
        "total": len(results), "statuses": dict(sorted(counts.items())),
        "executed": sum(item.get("exit_code") is not None for item in results),
        "failures": sum(counts[key] for key in FAILURES),
        "gaps": sum(counts[key] for key in GAPS),
        "expected": dict(sorted(Counter(item["expected"] for item in results).items())),
        "complete": not any(counts[key] for key in FAILURES | GAPS),
    }


def write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent, delete=False) as stream:
        temp = Path(stream.name)
        json.dump(data, stream, indent=2, sort_keys=True)
        stream.write("\n")
    temp.replace(path)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--checker", help="shell-quoted argv, NOT a shell command; filename appended by default")
    parser.add_argument("--input-mode", choices=("file", "env", "stdin"), default="file")
    parser.add_argument("--timeout", type=float, help="explicit per-test override, including upstream large-test limits")
    parser.add_argument("--default-timeout", type=float, default=30, help="fallback when a case has no limit")
    parser.add_argument("--max-log-bytes", type=int, default=16384, help="maximum captured bytes per stream per case")
    parser.add_argument("--select", action="append", default=[], help="case-id glob; unselected cases remain visible as skipped")
    parser.add_argument("--skip", action="append", default=[], metavar="GLOB=REASON")
    parser.add_argument("--report", type=Path, help="atomic JSON report, updated after every test")
    parser.add_argument("--inventory", action="store_true", help="print full inventory; do not invoke a checker")
    args = parser.parse_args(argv)
    try:
        positive_seconds(args.default_timeout)
        if args.timeout is not None:
            positive_seconds(args.timeout)
        if args.max_log_bytes < 0:
            raise ValueError("--max-log-bytes must be nonnegative")
        skip = []
        for item in args.skip:
            pattern, separator, reason = item.partition("=")
            if not separator or not pattern or not reason.strip():
                raise ValueError("--skip requires GLOB=REASON")
            skip.append((pattern, reason))
        args.skip = skip
        manifest_path = args.manifest.resolve()
        manifest = load_manifest(manifest_path)
        if args.inventory:
            print(json.dumps(manifest, indent=2))
            return 0
        if not args.checker:
            raise ValueError("--checker is required unless --inventory is used")
        make_command(args.checker, Path("input.ndjson"), args.input_mode)
    except (OSError, ValueError, TypeError) as exc:
        parser.error(str(exc))
    report = {
        "report_version": 1, "started_at": utc_now(), "finished_at": None,
        "manifest": str(manifest_path), "manifest_sha256": digest(manifest_path),
        "checker": args.checker, "input_mode": args.input_mode,
        "checker_artifacts_before": checker_fingerprint(args.checker),
        "integrity_verified": False, "integrity_errors": [],
        "provenance": manifest.get("provenance", {}), "results": [],
    }
    cleanup_blocker = None
    for case in manifest["cases"]:
        if cleanup_blocker is not None and case["availability"] == "available":
            item = {key: case[key] for key in ("id", "expected", "availability")}
            item.update(source_kind=case.get("source_kind", "unknown"), exit_code=None,
                        status="skipped", reason=f"not attempted: cleanup unverified after {cleanup_blocker}")
        else:
            item = run_case(case, manifest_path.parent, args)
        if item.get("cleanup_verified") is False:
            cleanup_blocker = case["id"]
        report["results"].append(item)
        report["summary"] = summary(report["results"])
        print(f"{item['status']:20s} {case['id']}", flush=True)
        if args.report:
            write_json(args.report, report)
    report["finished_at"] = utc_now()
    report["checker_artifacts_after"] = checker_fingerprint(args.checker)
    if report["checker_artifacts_before"] != report["checker_artifacts_after"]:
        report["integrity_errors"].append("checker command artifacts changed during this run")
    if digest(manifest_path) != report["manifest_sha256"]:
        report["integrity_errors"].append("manifest changed during this run")
    report["integrity_verified"] = not report["integrity_errors"]
    report["summary"]["integrity_failures"] = len(report["integrity_errors"])
    report["summary"]["failures"] += len(report["integrity_errors"])
    report["summary"]["complete"] = report["summary"]["complete"] and report["integrity_verified"]
    if args.report:
        write_json(args.report, report)
    print(json.dumps(report["summary"], sort_keys=True))
    return 1 if report["summary"]["failures"] else 2 if report["summary"]["gaps"] else 0


if __name__ == "__main__":
    sys.exit(main())
