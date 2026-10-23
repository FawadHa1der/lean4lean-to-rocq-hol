#!/usr/bin/env python3
# Copyright (c) 2026 Fawad Haider. All rights reserved.
"""Run any standalone checker against a pinned, language-neutral Arena manifest."""

import argparse
from collections import Counter
from datetime import datetime, timezone
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


DEFAULT_MANIFEST = Path(__file__).resolve().parents[1] / "arena/manifest.json"
VERDICTS = {0: "accept", 1: "reject", 2: "decline", 3: "fault"}
FAILURES = {"wrong_accept", "wrong_reject", "fault", "timeout", "input_error", "execution_error"}
GAPS = {"declined", "skipped", "missing_download", "missing_generated"}


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


def stop_group(proc):
    try:
        if os.name == "posix":
            os.killpg(proc.pid, signal.SIGKILL)
        else:
            proc.kill()
    except ProcessLookupError:
        pass
    proc.wait()


def run_process(command, path, timeout, input_mode, max_log_bytes):
    env = os.environ.copy()
    env["IN"] = str(path)
    start = time.monotonic()
    # Drain both streams continuously while keeping only bounded diagnostic prefixes.
    # Pipes avoid unbounded on-disk logs from a faulty checker.
    import threading

    logs = {"stdout": bytearray(), "stderr": bytearray()}
    totals = {"stdout": 0, "stderr": 0}

    def drain(stream, key):
        try:
            while chunk := stream.read(65536):
                totals[key] += len(chunk)
                remaining = max_log_bytes - len(logs[key])
                if remaining > 0:
                    logs[key].extend(chunk[:remaining])
        finally:
            stream.close()

    with path.open("rb") as source:
        proc = subprocess.Popen(
            command, env=env, stdin=source if input_mode == "stdin" else subprocess.DEVNULL,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=os.name == "posix",
        )
        threads = [threading.Thread(target=drain, args=(stream, key), daemon=True)
                   for stream, key in ((proc.stdout, "stdout"), (proc.stderr, "stderr"))]
        for thread in threads:
            thread.start()
        timed_out = False
        try:
            proc.wait(timeout=timeout)
            # Children may inherit pipes after the leader exits. Bound that wait too.
            for thread in threads:
                thread.join(max(0, timeout - (time.monotonic() - start)))
            timed_out = any(thread.is_alive() for thread in threads)
        except subprocess.TimeoutExpired:
            timed_out = True
        except BaseException:
            stop_group(proc)
            raise
        finally:
            # Also reap lingering descendants of a normally exiting checker.
            stop_group(proc)
        for thread in threads:
            thread.join(1)
    return {
        "exit_code": proc.returncode,
        "verdict": VERDICTS.get(proc.returncode, "fault"),
        "elapsed_seconds": round(time.monotonic() - start, 6),
        "timed_out": timed_out,
        **{key: bytes(logs[key]).decode("utf-8", errors="replace") for key in logs},
        **{f"{key}_bytes": totals[key] for key in logs},
        **{f"{key}_truncated": totals[key] > max_log_bytes for key in logs},
    }


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
    try:
        path = relative_path(root, case["path"])
        if not path.is_file():
            return {**result, "status": "input_error", "reason": "manifest says available but input is absent"}
        if path.stat().st_size != case["size"] or digest(path) != case["sha256"]:
            return {**result, "status": "input_error", "reason": "input size/SHA-256 differs from manifest"}
        timeout = args.timeout if args.timeout is not None else case.get("timeout_seconds", args.default_timeout)
        result["timeout_seconds"] = timeout
        result["input_sha256"] = case["sha256"]
        command = make_command(args.checker, path, args.input_mode)
        result.update(run_process(command, path, timeout, args.input_mode, args.max_log_bytes))
        result["status"] = "timeout" if result["timed_out"] else classify(result["exit_code"], case["expected"])
        if not path.is_file() or path.stat().st_size != case["size"] or digest(path) != case["sha256"]:
            return {**result, "status": "input_error", "reason": "input changed during checker execution"}
        if result["status"] == "declined":
            result["decline_kind"] = "checker_declared"
            result["reason"] = "exit 2: unsupported input or resource decline; not a proof verdict"
    except OSError as exc:
        result.update(status="execution_error", reason=str(exc))
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
    for case in manifest["cases"]:
        item = run_case(case, manifest_path.parent, args)
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
