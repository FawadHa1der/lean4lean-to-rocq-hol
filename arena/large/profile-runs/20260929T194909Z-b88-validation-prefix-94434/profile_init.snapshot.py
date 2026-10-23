#!/usr/bin/env python3
"""One immutable Init checker attempt and at most one macOS CPU sample."""

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import selectors
import shutil
import signal
import subprocess
import sys
import time


STAGE = re.compile(
    r"^stage=(\w+) line=(\d+) checked=(\d+) cpu_seconds=([0-9.]+)$"
)
LOG_LIMIT = 8 * 1024 * 1024


def utc_now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def fingerprint(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return {"path": str(path), "size": path.stat().st_size,
            "sha256": digest.hexdigest()}


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def stop_process(process):
    if process is not None:
        if process.poll() is None:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        process.wait()


def interrupted(signum, frame):
    raise KeyboardInterrupt(f"signal {signum}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-dir", required=True, type=Path,
                        help="new, nonexistent directory under this script's directory")
    args = parser.parse_args()
    script = Path(__file__).resolve()
    root = script.parents[3]
    run_dir = args.run_dir.resolve()
    if run_dir.parent != script.parent:
        parser.error("--run-dir must be a direct child of arena/large/profile-runs")
    run_dir.mkdir(exist_ok=False)
    manifest_path = root / "arena/large/manifest.json"
    manifest_bytes = manifest_path.read_bytes()
    manifest = json.loads(manifest_bytes)
    case, = [case for case in manifest["cases"] if case["id"] == "init"]
    cap = case["timeout_seconds"]
    if not 300 <= cap <= 500:
        raise ValueError("Init cap must be within the authorized 300-500 seconds")
    input_path = (manifest_path.parent / case["path"]).resolve()
    source_binary = root / "build/rocq-check"
    original_before = fingerprint(source_binary)
    binary_path = run_dir / "rocq-check"
    shutil.copyfile(source_binary, binary_path)
    binary_path.chmod(0o555)
    binary_before = fingerprint(binary_path)
    original_after = fingerprint(source_binary)
    if not (original_before["sha256"] == binary_before["sha256"] ==
            original_after["sha256"]):
        raise ValueError("binary changed during snapshot")
    input_before = fingerprint(input_path)
    if (input_before["sha256"] != case["sha256"] or
            input_before["size"] != case["size"]):
        raise ValueError("Init input does not match stable subset manifest")
    (run_dir / "manifest.snapshot.json").write_bytes(manifest_bytes)
    shutil.copyfile(script, run_dir / "profile_init.snapshot.py")
    source_paths = [
        "frontend/rocq_main.ml", "frontend/rocq_adapter.ml",
        "frontend/wire.ml", "frontend/replay.ml",
        "rocq/lean_arena.ml", "rocq/lean_arena.mli",
        "rocq/Checker.v", "rocq/Inductive.v", "rocq/InductiveUtils.v",
        "rocq/Primitives.v", "rocq/NestedAdmission.v",
    ]
    sources_before = {name: fingerprint(root / name) for name in source_paths}
    command = [str(binary_path), "--progress", "1", "--fuel", "512", str(input_path)]
    provenance = {
        "snapshot_utc": utc_now(), "command": command,
        "fuel": 512, "timeout_seconds": cap, "case": case,
        "original_binary_before_copy": original_before,
        "original_binary_after_copy": original_after,
        "binary_before": binary_before, "input_before": input_before,
        "manifest_before": fingerprint(manifest_path),
        "driver": fingerprint(script), "sources_before": sources_before,
        "sample_policy": {"duration_seconds": 5, "interval_ms": 1,
                          "declaration_stall_seconds": 15,
                          "fallback_seconds_before_deadline": 30,
                          "sampler_timeout_seconds": 20,
                          "maximum_invocations": 1},
        "provenance_note": "Source hashes are observed build inputs, not a reproducible-build attestation.",
    }
    write_json(run_dir / "provenance.json", provenance)
    print(json.dumps({"event": "snapshot_ready", "binary": binary_before,
                      "input": input_before, "cap": cap}), flush=True)

    for signum in (signal.SIGTERM, signal.SIGINT):
        signal.signal(signum, interrupted)
    checker = None
    sampler = None
    sample_info = None
    events = []
    pending = b""
    timed_out = False
    failure = None
    started_utc = utc_now()
    started = time.monotonic()
    deadline = started + cap
    last_event_time = started
    sample_started = None
    logs = {}
    totals = {"stdout": 0, "stderr": 0}
    selector = selectors.DefaultSelector()
    event_log = (run_dir / "progress.jsonl").open("w")
    sample_log = (run_dir / "sample-driver.log").open("wb")

    def progress_line(raw):
        nonlocal last_event_time
        match = STAGE.fullmatch(raw.decode("utf-8", errors="replace").strip())
        if match is None:
            return
        label, line, checked, cpu = match.groups()
        last_event_time = time.monotonic()
        event = {"stage": label, "line": int(line), "checked": int(checked),
                 "cpu_seconds": float(cpu),
                 "observed_wall_seconds": last_event_time - started}
        events.append(event)
        event_log.write(json.dumps(event, sort_keys=True) + "\n")
        event_log.flush()
        if label != "declaration":
            print(json.dumps({"event": "phase", **event}), flush=True)

    try:
        checker = subprocess.Popen(command, cwd=root, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, start_new_session=True)
        print(json.dumps({"event": "checker_started", "pid": checker.pid,
                          "started_utc": started_utc}), flush=True)
        for name in ("stdout", "stderr"):
            pipe = getattr(checker, name)
            os.set_blocking(pipe.fileno(), False)
            selector.register(pipe, selectors.EVENT_READ, name)
            logs[name] = (run_dir / f"checker.{name}.log").open("wb")
        while selector.get_map() or checker.poll() is None:
            now = time.monotonic()
            if now >= deadline and checker.poll() is None:
                timed_out = True
                stop_process(checker)
            if sampler is not None and sampler.poll() is None:
                if now - sample_started >= 20 or checker.poll() is not None:
                    stop_process(sampler)
                    sample_info["stopped_by_driver"] = True
            if sampler is not None and sampler.poll() is not None and "exit_code" not in sample_info:
                sample_info.update(exit_code=sampler.wait(),
                                   ended_wall_seconds=time.monotonic() - started,
                                   progress_after=events[-1] if events else None)
                print(json.dumps({"event": "sample_finished", **sample_info}), flush=True)
            active = events[-1] if events else None
            checking = active is not None and active["stage"] in ("check", "declaration")
            stalled = checking and active["stage"] == "declaration" and now - last_event_time >= 15
            fallback = checking and deadline - now <= 30
            if sample_info is None and checker.poll() is None and (stalled or fallback):
                sample_command = ["/usr/bin/sample", str(checker.pid), "5", "1", "-mayDie",
                                  "-file", str(run_dir / "sample.txt")]
                sample_started = time.monotonic()
                sample_info = {"command": sample_command, "pid": checker.pid,
                               "trigger": "declaration_stall" if stalled else "deadline_fallback",
                               "started_wall_seconds": sample_started - started,
                               "progress_before": active}
                write_json(run_dir / "sample-context.json", sample_info)
                print(json.dumps({"event": "sample_started", **sample_info}), flush=True)
                try:
                    sampler = subprocess.Popen(sample_command, stdout=sample_log,
                                               stderr=subprocess.STDOUT, start_new_session=True)
                except OSError as error:
                    sample_info["error"] = str(error)
            for key, _ in selector.select(timeout=0.2):
                block = os.read(key.fileobj.fileno(), 65536)
                name = key.data
                if not block:
                    selector.unregister(key.fileobj)
                    key.fileobj.close()
                    continue
                remaining = max(0, LOG_LIMIT - totals[name])
                logs[name].write(block[:remaining])
                logs[name].flush()
                totals[name] += len(block)
                if name == "stderr":
                    pending += block
                    while b"\n" in pending:
                        raw, pending = pending.split(b"\n", 1)
                        progress_line(raw)
        if pending:
            progress_line(pending)
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
        write_json(run_dir / "sample-context.json", sample_info)
    binary_after = fingerprint(binary_path)
    input_after = fingerprint(input_path)
    source_changes = [name for name, before in sources_before.items()
                      if fingerprint(root / name)["sha256"] != before["sha256"]]
    intervals = []
    for previous, following in zip(events, events[1:]):
        if previous["stage"] == "declaration":
            intervals.append({"line": previous["line"], "checked_before": previous["checked"],
                              "checked_after": following["checked"],
                              "cpu_seconds": following["cpu_seconds"] - previous["cpu_seconds"],
                              "observed_wall_seconds": following["observed_wall_seconds"] -
                                                       previous["observed_wall_seconds"]})
    code = checker.returncode if checker is not None else None
    verdict = "timeout" if timed_out else {0: "accept", 1: "reject", 2: "decline", 3: "fault"}.get(code, "fault")
    report = {
        "started_utc": started_utc, "finished_utc": utc_now(),
        "command": command, "timeout_seconds": cap, "fuel": 512,
        "elapsed_seconds": elapsed, "timed_out": timed_out,
        "exit_code": code, "classification": verdict,
        "driver_error": failure, "sample": sample_info,
        "last_progress": events[-1] if events else None,
        "last_progress_note": "Declaration progress is emitted before admission of that batch, not after it.",
        "phase_events": [event for event in events if event["stage"] != "declaration"],
        "declaration_events": sum(event["stage"] == "declaration" for event in events),
        "slowest_completed_batches": sorted(intervals, key=lambda item: item["cpu_seconds"], reverse=True)[:20],
        "log_bytes": totals,
        "log_truncated": {name: total > LOG_LIMIT for name, total in totals.items()},
        "binary_after": binary_after, "input_after": input_after,
        "manifest_after": fingerprint(manifest_path),
        "shared_binary_after": fingerprint(source_binary),
        "observed_source_changes": source_changes,
        "integrity_verified": binary_after["sha256"] == binary_before["sha256"] and
                              input_after["sha256"] == input_before["sha256"],
        "processes_reaped": all(process is None or process.returncode is not None
                                for process in (checker, sampler)),
    }
    write_json(run_dir / "report.json", report)
    print(json.dumps({"event": "finished", **report}), flush=True)
    return 0 if failure is None and report["integrity_verified"] else 3


if __name__ == "__main__":
    sys.exit(main())
