#!/usr/bin/env python3
"""Snapshot the current Rocq executable and run only verified large Arena inputs."""

import argparse
import os
from pathlib import Path
import shlex
import shutil
import sys
import time

import test_arena

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "arena/large"


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout", type=test_arena.positive_seconds, default=30)
    args = parser.parse_args(argv)
    manifest_path = WORK / "manifest.json"
    manifest = test_arena.load_manifest(manifest_path)
    if {case["id"] for case in manifest["cases"]} != {"init", "std"}:
        raise ValueError("generate both pinned Init/Std inputs before testing")
    binary = ROOT / "build/rocq-check"
    if not binary.is_file() or not os.access(binary, os.X_OK):
        raise ValueError("missing executable: build/rocq-check (parent-owned prerequisite)")
    directory = WORK / "checker-runs" / f"{time.time_ns()}-{os.getpid()}"
    directory.mkdir(parents=True)
    snapshot = directory / "rocq-check"
    before = test_arena.digest(binary)
    shutil.copy2(binary, snapshot)
    copied = test_arena.digest(snapshot)
    if before != copied or test_arena.digest(binary) != before:
        raise RuntimeError("checker changed during snapshot; rerun when parent build is stable")
    report_path = directory / "results.json"
    invocation = ["--manifest", str(manifest_path), "--checker", shlex.quote(str(snapshot)),
                  "--timeout", str(args.timeout), "--report", str(report_path)]
    provenance = {"started_at": test_arena.utc_now(), "finished_at": None,
                  "source_executable": str(binary), "snapshot": str(snapshot),
                  "checker_sha256": copied, "source_mtime_ns": binary.stat().st_mtime_ns,
                  "manifest_sha256": test_arena.digest(manifest_path),
                  "runner_sha256": test_arena.digest(Path(test_arena.__file__)),
                  "script_sha256": test_arena.digest(Path(__file__)),
                  "timeout_seconds_per_case": args.timeout, "runner_arguments": invocation}
    test_arena.write_json(directory / "provenance.json", provenance)
    result = test_arena.main(invocation)
    provenance.update(finished_at=test_arena.utc_now(), runner_exit_code=result,
                      snapshot_unchanged=test_arena.digest(snapshot) == copied)
    test_arena.write_json(directory / "provenance.json", provenance)
    test_arena.write_json(WORK / "latest-checker.json", {
        "report": str(report_path.relative_to(WORK)),
        "provenance": str((directory / "provenance.json").relative_to(WORK))})
    print(f"Checker report: {report_path}")
    return result if provenance["snapshot_unchanged"] else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, RuntimeError) as exc:
        print(f"Large Arena checker run failed: {exc}", file=sys.stderr)
        sys.exit(1)
