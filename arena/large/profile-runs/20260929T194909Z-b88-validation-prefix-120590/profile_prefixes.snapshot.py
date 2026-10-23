#!/usr/bin/env python3
"""Run the two saved prefixes once each against the pinned b88 checker snapshot."""

import argparse
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

from profile_init import STAGE, fingerprint, interrupted, stop_process, utc_now, write_json


SNAPSHOT = "20260929T192930Z-delayed-beta"
BINARY_SHA256 = "b88c4a832285060dc6a41cc0ccacf4f175b3e0a6f02b6014943575abfc0fb209"
PREFIXES = (
    (94434, "846760ab10763b75c62570405d6704377e2ae107d5fb189464edbfb0dea3922a"),
    (120590, "dce08f76af5892eda7110dc6b5d382d2a1a8cc07bcd8a0116b7e4b5d50a23877"),
)
# Leave headroom for deadline detection and reaping within the 120-second budget.
TIMEOUT_SECONDS = 119.0
SAMPLE_AFTER_SECONDS = 30.0
LOG_LIMIT = 8 * 1024 * 1024


def classify_exit(code, timed_out):
    if timed_out:
        return "timeout"
    return {0: "accept", 1: "reject", 2: "decline", 3: "fault"}.get(code, "fault")


def declaration_index(path):
    names = {0: "<anonymous>"}
    declarations = {}
    with path.open("rb") as stream:
        for line, raw in enumerate(stream, 1):
            record = json.loads(raw)
            if "in" in record:
                part = record.get("str", record.get("num"))
                suffix = part["str"] if "str" in part else f'[{part["i"]}]'
                names[record["in"]] = (names[part["pre"]] + "." if part["pre"] else "") + suffix
            elif len(record) == 1:
                tag, value = next(iter(record.items()))
                if tag == "inductive":
                    headers = [*value["types"], *value["ctors"], *value["recs"]]
                elif tag in {"axiom", "def", "thm", "opaque", "quot"}:
                    headers = [value]
                else:
                    continue
                declarations[line] = {"tag": tag, "names": [names[header["name"]] for header in headers]}
    return declarations


def sample_correlation(info, events):
    if info is None:
        return None
    begin = info["started_wall_seconds"]
    end = info.get("ended_wall_seconds", begin)
    before = [event for event in events if event["observed_wall_seconds"] <= begin]
    during = [event for event in events if begin < event["observed_wall_seconds"] <= end]
    previous = before[-1] if before else None
    stable = (previous is not None and previous["stage"] == "declaration" and not during and
              info.get("exit_code") == 0 and not info.get("stopped_by_driver") and not info.get("error"))
    return {"progress_before": previous, "progress_events_during": during,
            "progress_after": during[-1] if during else previous,
            "no_observed_progress_events_across_sample": not during,
            "single_observed_active_declaration": stable,
            "interpretation": ("No progress events were observed across the sample window; the preceding declaration remained active."
                               if stable else "Progress is a lower bound only; do not attribute this sample to one declaration.")}


def run_prefix(parent, label, line, expected_hash):
    root = parent.parents[2]
    origin = parent / SNAPSHOT
    binary = origin / "rocq-check"
    source = origin / f"init-through-line-{line}.ndjson"
    audit_path = origin / f"init-through-line-{line}.json"
    run_dir = parent / f"{label}-prefix-{line}"
    binary_before = fingerprint(binary)
    input_before = fingerprint(source)
    if binary_before["sha256"] != BINARY_SHA256 or input_before["sha256"] != expected_hash:
        raise ValueError("pinned binary or prefix changed; no checker started")
    audit = json.loads(audit_path.read_text())
    if not (audit["prefix_sha256"] == expected_hash and audit["dependency_closed_in_input_order"] and
            audit["observed_full_run_batch_order_matches_prefix"]):
        raise ValueError("saved prefix audit does not establish the required transport closure")
    names = declaration_index(source)
    run_dir.mkdir(exist_ok=False)
    shutil.copyfile(audit_path, run_dir / "prefix-audit.snapshot.json")
    for name in ("profile_prefixes.py", "profile_init.py"):
        shutil.copyfile(parent / name, run_dir / name.replace(".py", ".snapshot.py"))
    command = [str(binary), "--progress", "1", "--fuel", "512", str(source)]
    write_json(run_dir / "provenance.json", {
        "created_utc": utc_now(), "command": command, "fuel": 512,
        "authorized_max_seconds": 120, "enforced_timeout_seconds": TIMEOUT_SECONDS,
        "sample_after_seconds": SAMPLE_AFTER_SECONDS, "sample_duration_seconds": 5,
        "maximum_sample_invocations": 1, "binary_before": binary_before,
        "input_before": input_before, "prefix_audit": fingerprint(audit_path),
        "origin_provenance": fingerprint(origin / "provenance.json"),
        "driver": fingerprint(parent / "profile_prefixes.py"),
        "driver_helper": fingerprint(parent / "profile_init.py"),
        "target": audit["last_declaration"],
        "note": "No full Init input, shared build binary, core source, or main manifest is used or changed.",
    })
    print(json.dumps({"event": "prefix_ready", "line": line, "input": input_before,
                      "binary_sha256": binary_before["sha256"]}), flush=True)
    checker = sampler = None
    sample_info = None
    sampler_started = None
    timed_out = False
    failure = None
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
        stage, source_line, checked, cpu = match.groups()
        event = {"stage": stage, "line": int(source_line), "checked": int(checked),
                 "cpu_seconds": float(cpu), "observed_wall_seconds": time.monotonic() - started}
        if event["line"] in names:
            event["declaration"] = names[event["line"]]
        events.append(event)
        event_log.write(json.dumps(event, sort_keys=True) + "\n")
        event_log.flush()
        if stage != "declaration":
            print(json.dumps({"event": "phase", "prefix_line": line, **event}), flush=True)

    try:
        checker = subprocess.Popen(command, cwd=root, stdin=subprocess.DEVNULL,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
        print(json.dumps({"event": "checker_started", "prefix_line": line,
                          "pid": checker.pid, "started_utc": started_utc}), flush=True)
        for name in ("stdout", "stderr"):
            pipe = getattr(checker, name)
            os.set_blocking(pipe.fileno(), False)
            selector.register(pipe, selectors.EVENT_READ, name)
            logs[name] = (run_dir / f"checker.{name}.log").open("wb")
        while selector.get_map() or checker.poll() is None:
            if time.monotonic() >= deadline and checker.poll() is None:
                timed_out = True
                stop_process(checker)
            for key, _ in selector.select(timeout=0.05):
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
                    now - sampler_started >= 20 or checker.poll() is not None):
                stop_process(sampler)
                sample_info["stopped_by_driver"] = True
            if sampler is not None and sampler.poll() is not None and "exit_code" not in sample_info:
                sample_info.update(exit_code=sampler.wait(), ended_wall_seconds=now - started)
                print(json.dumps({"event": "sample_finished", "prefix_line": line,
                                  "exit_code": sampler.returncode,
                                  "correlation": sample_correlation(sample_info, events)}), flush=True)
            if sample_info is None and now - started >= SAMPLE_AFTER_SECONDS and checker.poll() is None:
                sample_command = ["/usr/bin/sample", str(checker.pid), "5", "1", "-mayDie",
                                  "-file", str(run_dir / "sample.txt")]
                sampler_started = time.monotonic()
                sample_info = {"command": sample_command, "checker_pid": checker.pid,
                               "started_wall_seconds": sampler_started - started,
                               "progress_at_trigger": events[-1] if events else None}
                print(json.dumps({"event": "sample_started", "prefix_line": line, **sample_info}), flush=True)
                write_json(run_dir / "sample-context.json", sample_info)
                try:
                    sampler = subprocess.Popen(sample_command, stdout=sample_log,
                                               stderr=subprocess.STDOUT, start_new_session=True)
                    sample_info["sampler_pid"] = sampler.pid
                except OSError as error:
                    sample_info["error"] = str(error)
                    sample_info["ended_wall_seconds"] = time.monotonic() - started
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
    code = checker.returncode if checker is not None else None
    after_binary, after_input = fingerprint(binary), fingerprint(source)
    intervals = []
    for first, second in zip(events, events[1:]):
        if first["stage"] == "declaration":
            intervals.append({"line": first["line"], "declaration": first.get("declaration"),
                              "checked_before": first["checked"], "checked_after": second["checked"],
                              "cpu_seconds": second["cpu_seconds"] - first["cpu_seconds"],
                              "observed_wall_seconds": second["observed_wall_seconds"] - first["observed_wall_seconds"]})
    report = {"started_utc": started_utc, "finished_utc": utc_now(), "command": command,
              "checker_pid": checker.pid if checker is not None else None,
              "driver_pid": os.getpid(), "elapsed_seconds": elapsed,
              "timeout_seconds": TIMEOUT_SECONDS, "fuel": 512, "prefix_line": line,
              "exit_code": code, "timed_out": timed_out, "classification": classify_exit(code, timed_out),
              "driver_error": failure, "sample": sample_info,
              "sample_not_taken_reason": "checker finished before 30 seconds" if sample_info is None else None,
              "last_progress": events[-1] if events else None,
              "phase_events": [event for event in events if event["stage"] != "declaration"],
              "declaration_events": sum(event["stage"] == "declaration" for event in events),
              "slowest_completed_batches": sorted(intervals, key=lambda item: item["cpu_seconds"], reverse=True)[:10],
              "log_bytes": totals, "log_truncated": {name: total > LOG_LIMIT for name, total in totals.items()},
              "binary_after": after_binary, "input_after": after_input,
              "integrity_verified": after_binary["sha256"] == binary_before["sha256"] and
                                    after_input["sha256"] == input_before["sha256"],
              "processes_reaped": all(process is None or process.returncode is not None for process in (checker, sampler)),
              "target": audit["last_declaration"],
              "scope_note": "A diagnostic prefix run is not full Init or a new Arena case."}
    write_json(run_dir / "report.json", report)
    print(json.dumps({"event": "prefix_finished", "run_dir": str(run_dir), **report}), flush=True)
    if failure is not None or not report["integrity_verified"]:
        raise RuntimeError("prefix profiling driver failed; inspect preserved report")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--label", required=True)
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9-]{0,79}", args.label):
        parser.error("label must be a short alphanumeric/hyphen identifier")
    parent = Path(__file__).resolve().parent
    if any((parent / f"{args.label}-prefix-{line}").exists() for line, _ in PREFIXES):
        parser.error("a requested run directory already exists; refusing duplicate attempts")
    for signum in (signal.SIGINT, signal.SIGTERM):
        signal.signal(signum, interrupted)
    for line, expected_hash in PREFIXES:
        run_prefix(parent, args.label, line, expected_hash)


if __name__ == "__main__":
    main()
