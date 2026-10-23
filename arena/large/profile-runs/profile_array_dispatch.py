#!/usr/bin/env python3
"""One pinned Array prefix attempt, sampling only a stable target declaration."""

import argparse
import json
import os
from pathlib import Path
import selectors
import shutil
import signal
import subprocess
import time

from profile_init import STAGE, fingerprint, interrupted, stop_process, utc_now, write_json
from profile_prefixes import classify_exit, declaration_index, sample_correlation


BINARY_SHA256 = "3ef3328088cc6f91a4113947ffb6d97196e840bcb4f6d9445512fa9e5ef86be3"
INPUT_SHA256 = "dce08f76af5892eda7110dc6b5d382d2a1a8cc07bcd8a0116b7e4b5d50a23877"
TARGET_LINE = 120590
TARGET_NAME = "Array.foldlM_toList.aux._unary"
TIMEOUT_SECONDS = 149.0
QUIET_SECONDS = 10.0
LOG_LIMIT = 8 * 1024 * 1024


def sample_eligible(events, elapsed, remaining):
    if not events or remaining < 6.0:
        return False
    last = events[-1]
    return (last["stage"] == "declaration" and last["line"] == TARGET_LINE and
            last["checked"] == 1703 and
            last.get("declaration", {}).get("names") == [TARGET_NAME] and
            elapsed - last["observed_wall_seconds"] >= QUIET_SECONDS)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-dir", required=True, type=Path)
    args = parser.parse_args()
    script = Path(__file__).resolve()
    parent = script.parent
    root = script.parents[3]
    run_dir = args.run_dir.resolve()
    if run_dir.parent != parent:
        parser.error("run directory must be a new direct child of profile-runs")
    origin = parent / "20260929T192930Z-delayed-beta"
    original_binary = root / "build/rocq-check-dispatch-checkpoint"
    original_input = origin / "init-through-line-120590.ndjson"
    audit_path = origin / "init-through-line-120590.json"
    originals_before = {"binary": fingerprint(original_binary), "input": fingerprint(original_input)}
    if (originals_before["binary"]["sha256"] != BINARY_SHA256 or
            originals_before["input"]["sha256"] != INPUT_SHA256):
        raise ValueError("pinned binary/input hash mismatch; no checker started")
    audit = json.loads(audit_path.read_text())
    if not (audit["prefix_sha256"] == INPUT_SHA256 and audit["dependency_closed_in_input_order"] and
            audit["observed_full_run_batch_order_matches_prefix"]):
        raise ValueError("prefix audit mismatch; no checker started")
    names = declaration_index(original_input)
    if names[TARGET_LINE]["names"] != [TARGET_NAME]:
        raise ValueError("target name mismatch")
    run_dir.mkdir(exist_ok=False)
    binary = run_dir / "rocq-check"
    source = run_dir / "init-through-line-120590.ndjson"
    for old, new in ((original_binary, binary), (original_input, source)):
        shutil.copyfile(old, new)
        new.chmod(0o555 if new == binary else 0o444)
    snapshots_before = {"binary": fingerprint(binary), "input": fingerprint(source)}
    originals_after_copy = {"binary": fingerprint(original_binary), "input": fingerprint(original_input)}
    for key in originals_before:
        if not (originals_before[key]["sha256"] == snapshots_before[key]["sha256"] ==
                originals_after_copy[key]["sha256"]):
            raise ValueError("source changed during snapshot; no checker started")
    shutil.copyfile(audit_path, run_dir / "prefix-audit.snapshot.json")
    helpers = [script, parent / "profile_init.py", parent / "profile_prefixes.py"]
    for helper in helpers:
        shutil.copyfile(helper, run_dir / helper.name.replace(".py", ".snapshot.py"))
    observed_paths = [root / name for name in (
        "frontend/wire.ml", "frontend/replay.ml", "frontend/rocq_adapter.ml",
        "frontend/rocq_main.ml", "rocq/Checker.v", "rocq/Syntax.v", "rocq/lean_arena.ml")]
    observed_before = {str(path.relative_to(root)): fingerprint(path) for path in observed_paths if path.exists()}
    command = [str(binary), "--fuel", "512", "--progress", "1", str(source)]
    write_json(run_dir / "provenance.json", {
        "created_utc": utc_now(), "command": command, "fuel": 512,
        "authorized_max_seconds": 150, "enforced_timeout_seconds": TIMEOUT_SECONDS,
        "sample_target_line": TARGET_LINE, "sample_target_name": TARGET_NAME,
        "sample_quiet_seconds": QUIET_SECONDS, "sample_duration_seconds": 5,
        "maximum_sample_invocations": 1, "originals_before": originals_before,
        "originals_after_copy": originals_after_copy, "snapshots_before": snapshots_before,
        "prefix_audit": fingerprint(audit_path), "helpers": [fingerprint(path) for path in helpers],
        "observed_sources_before": observed_before,
        "source_caveat": "Observed shared source hashes are context only, not build provenance for the checkpoint. No frontend equivalence to the private 82a binary is assumed.",
    })
    checker = sampler = None
    sample_info = None
    failure = None
    timed_out = False
    events = []
    pending = b""
    totals = {"stdout": 0, "stderr": 0}
    logs = {}
    selector = selectors.DefaultSelector()
    event_log = (run_dir / "progress.jsonl").open("w")
    sample_log = (run_dir / "sample-driver.log").open("wb")
    started_utc = utc_now()
    started = time.monotonic()
    deadline = started + TIMEOUT_SECONDS

    def consume(raw):
        match = STAGE.fullmatch(raw.decode("utf-8", errors="replace").strip())
        if match is None:
            return
        stage, line, checked, cpu = match.groups()
        event = {"stage": stage, "line": int(line), "checked": int(checked),
                 "cpu_seconds": float(cpu), "observed_wall_seconds": time.monotonic() - started}
        if event["line"] in names:
            event["declaration"] = names[event["line"]]
        events.append(event)
        event_log.write(json.dumps(event, sort_keys=True) + "\n")
        event_log.flush()
        if stage != "declaration" or event["line"] == TARGET_LINE:
            print(json.dumps({"event": "progress", **event}), flush=True)

    try:
        checker = subprocess.Popen(command, cwd=root, stdin=subprocess.DEVNULL,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
        print(json.dumps({"event": "checker_started", "pid": checker.pid, "started_utc": started_utc,
                          "binary_sha256": BINARY_SHA256, "input_sha256": INPUT_SHA256}), flush=True)
        for name in ("stdout", "stderr"):
            pipe = getattr(checker, name)
            os.set_blocking(pipe.fileno(), False)
            selector.register(pipe, selectors.EVENT_READ, name)
            logs[name] = (run_dir / f"checker.{name}.log").open("wb")
        while selector.get_map() or checker.poll() is None:
            if time.monotonic() >= deadline and checker.poll() is None:
                timed_out = True
                stop_process(checker)
            for key, _ in selector.select(timeout=0.025):
                block = os.read(key.fileobj.fileno(), 65536)
                if not block:
                    selector.unregister(key.fileobj)
                    key.fileobj.close()
                    continue
                name = key.data
                logs[name].write(block[:max(0, LOG_LIMIT - totals[name])])
                logs[name].flush()
                totals[name] += len(block)
                if name == "stderr":
                    pending += block
                    while b"\n" in pending:
                        raw, pending = pending.split(b"\n", 1)
                        consume(raw)
            now = time.monotonic()
            if sampler is not None and sampler.poll() is None and (
                    now - started - sample_info["started_wall_seconds"] >= 20 or checker.poll() is not None):
                stop_process(sampler)
                sample_info["stopped_by_driver"] = True
            if sampler is not None and sampler.poll() is not None and "exit_code" not in sample_info:
                sample_info.update(exit_code=sampler.wait(), ended_wall_seconds=now - started)
                sample_info["correlation"] = sample_correlation(sample_info, events)
                write_json(run_dir / "sample-context.json", sample_info)
                print(json.dumps({"event": "sample_finished", **sample_info}), flush=True)
            if (sample_info is None and checker.poll() is None and
                    sample_eligible(events, now - started, deadline - now)):
                sample_command = ["/usr/bin/sample", str(checker.pid), "5", "1", "-mayDie",
                                  "-file", str(run_dir / "sample.txt")]
                sample_info = {"command": sample_command, "checker_pid": checker.pid,
                               "started_wall_seconds": now - started, "progress_at_trigger": events[-1],
                               "quiet_seconds_at_trigger": now - started - events[-1]["observed_wall_seconds"]}
                write_json(run_dir / "sample-context.json", sample_info)
                print(json.dumps({"event": "sample_started", **sample_info}), flush=True)
                try:
                    sampler = subprocess.Popen(sample_command, stdout=sample_log,
                                               stderr=subprocess.STDOUT, start_new_session=True)
                    sample_info["sampler_pid"] = sampler.pid
                except OSError as error:
                    sample_info.update(error=str(error), ended_wall_seconds=time.monotonic() - started)
        if pending:
            consume(pending)
    except BaseException as error:
        failure = f"{type(error).__name__}: {error}"
    finally:
        stop_process(checker)
        stop_process(sampler)
        elapsed = time.monotonic() - started
        for key in list(selector.get_map().values()):
            selector.unregister(key.fileobj)
            key.fileobj.close()
        selector.close()
        for log in logs.values():
            log.close()
        event_log.close()
        sample_log.close()
    if sample_info is not None:
        if sampler is not None:
            sample_info.setdefault("exit_code", sampler.returncode)
        sample_info.setdefault("ended_wall_seconds", elapsed)
        sample_info["correlation"] = sample_correlation(sample_info, events)
        write_json(run_dir / "sample-context.json", sample_info)
    snapshots_after = {"binary": fingerprint(binary), "input": fingerprint(source)}
    originals_after = {"binary": fingerprint(original_binary), "input": fingerprint(original_input)}
    target_events = [e for e in events if e["stage"] == "declaration" and e["line"] == TARGET_LINE]
    reference_events = [json.loads(line) for line in (origin / "progress.jsonl").read_text().splitlines()]
    sequence = [(e["line"], e["checked"]) for e in events if e["stage"] == "declaration"]
    reference = [(e["line"], e["checked"]) for e in reference_events if e["stage"] == "declaration"]
    code = checker.returncode if checker is not None else None
    report = {
        "started_utc": started_utc, "finished_utc": utc_now(), "command": command,
        "checker_pid": checker.pid if checker is not None else None, "driver_pid": os.getpid(),
        "elapsed_seconds": elapsed, "timeout_seconds": TIMEOUT_SECONDS, "fuel": 512,
        "exit_code": code, "timed_out": timed_out, "classification": classify_exit(code, timed_out),
        "driver_error": failure, "sample": sample_info,
        "sample_not_taken_reason": "target did not remain active for ten seconds with six seconds left in budget" if sample_info is None else None,
        "target_events": target_events, "last_progress": events[-1] if events else None,
        "target_to_process_end_wall_seconds": elapsed - target_events[-1]["observed_wall_seconds"] if target_events else None,
        "phase_events": [e for e in events if e["stage"] != "declaration"],
        "declaration_events": len(sequence), "matches_prior_full_run_order": sequence == reference[:len(sequence)],
        "reference_progress": fingerprint(origin / "progress.jsonl"),
        "snapshots_after": snapshots_after, "originals_after": originals_after,
        "observed_sources_after": {str(path.relative_to(root)): fingerprint(path) for path in observed_paths if path.exists()},
        "integrity_verified": all(snapshots_after[k]["sha256"] == snapshots_before[k]["sha256"] ==
                                  originals_before[k]["sha256"] == originals_after[k]["sha256"] for k in snapshots_before),
        "log_bytes": totals, "log_truncated": {k: v > LOG_LIMIT for k, v in totals.items()},
        "processes_reaped": all(p is None or p.returncode is not None for p in (checker, sampler)),
        "scope_note": "One diagnostic prefix, not full Init, not a new Arena case. A deadline kill is not a logical verdict.",
    }
    write_json(run_dir / "report.json", report)
    print(json.dumps({"event": "finished", "run_dir": str(run_dir), "classification": report["classification"],
                      "elapsed_seconds": elapsed, "exit_code": code, "integrity_verified": report["integrity_verified"],
                      "processes_reaped": report["processes_reaped"]}), flush=True)
    if failure or not report["integrity_verified"]:
        raise RuntimeError("profiling failed; inspect preserved report")


if __name__ == "__main__":
    for signum in (signal.SIGINT, signal.SIGTERM):
        signal.signal(signum, interrupted)
    main()
