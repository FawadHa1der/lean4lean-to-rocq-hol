#!/usr/bin/env python3
"""One offline export-only retry of the retained, pinned Mathlib build."""

import argparse
import json
import os
import shutil
import sys
from types import SimpleNamespace

from acquire_mathlib_arena import Runner, cache_files
from acquire_large_arena import inspect_output
from prepare_mathlib_arena import ROOT, WORK, load_lock, source_hashes, source_paths, toolchain_check
from test_arena import digest, utc_now, write_json


PREVIOUS = WORK / "runs/1790716624648598000-95150"
PREVIOUS_SHA256 = "a98c7b0b6f35b5c31ede8eec54fd889ab94407bb327dd1d74bbe6ee76bec4dda"
MEMORY_MIB = 8192
EXPORT_SECONDS = 300


def verify_retained(lock):
    if digest(PREVIOUS / "report.json") != PREVIOUS_SHA256:
        raise ValueError("previous attempt report changed")
    previous = json.loads((PREVIOUS / "report.json").read_text())
    if previous["lock"] != lock or not previous["sources_unchanged_at_finish"]:
        raise ValueError("previous source provenance differs")
    for name, expected in previous["helper_sha256"].items():
        if digest(ROOT / "scripts" / name) != expected:
            raise ValueError(f"reviewed helper changed: {name}")
    index_path = PREVIOUS / "cache-files.json"
    if digest(index_path) != previous["cache_files_index_sha256"]:
        raise ValueError("previous cache inventory changed")
    index = json.loads(index_path.read_text())
    if len(index) != 8908 or set(index) != {p.name for p in cache_files()}:
        raise ValueError("complete cache set differs")
    marker = json.loads((WORK / "cache/recipe.json").read_text())
    if marker != {"lock_sha256": digest(WORK / "lock.json")}:
        raise ValueError("cache recipe marker differs")
    for name, expected in index.items():
        path = WORK / "cache" / name
        if path.stat().st_size != expected["size"] or digest(path) != expected["sha256"]:
            raise ValueError(f"retained cache bytes changed: {name}")
    exporter = PREVIOUS / "exporter"
    for name, expected in previous["exporter_source_sha256"].items():
        if digest(exporter / name) != expected:
            raise ValueError(f"retained exporter source changed: {name}")
    executable = exporter / ".lake/build/bin/lean4export"
    if digest(executable) != previous["exporter_binary_sha256"]:
        raise ValueError("retained exporter binary changed")
    if digest(PREVIOUS / "packages.json") != previous["package_overrides_sha256"]:
        raise ValueError("retained package overrides changed")
    return previous, exporter, executable


def execute(lock):
    if shutil.disk_usage(WORK).free < 64 * 1024**3:
        raise ValueError("at least 64 GiB free required")
    previous, exporter, executable = verify_retained(lock)
    original = source_hashes(lock)
    if original != previous["source_hashes"]:
        raise ValueError("retained source set changed")
    toolchain, version = toolchain_check(lock)
    runner = Runner(lock, SimpleNamespace(memory_mib=MEMORY_MIB), toolchain)
    runner.report.update(
        retry_script_sha256=digest(ROOT / "scripts/retry_mathlib_export.py"),
        previous_report=str((PREVIOUS / "report.json").relative_to(WORK)),
        previous_report_sha256=PREVIOUS_SHA256, retry_policy="one offline export; no automatic retry",
        lean_version=version, source_hashes=original, cache_files_reverified=8908,
        cache_index_sha256=previous["cache_files_index_sha256"],
        exporter_binary_sha256=digest(executable),
        exporter_source_sha256=previous["exporter_source_sha256"],
        initial_free_disk_bytes=shutil.disk_usage(WORK).free,
    )
    output = runner.directory / "mathlib.partial.ndjson"
    print(f"Mathlib export-only report: {runner.path}", flush=True)
    try:
        paths = source_paths(lock)
        runner.run([toolchain / "bin/lake", "--no-cache", "--no-ansi", "--packages",
                    PREVIOUS / "packages.json", "--no-build", "build", lock["module"]],
                   paths["mathlib"], "recheck cached Mathlib target without rebuilding", 90)
        search = ":".join(os.path.relpath(p / ".lake/build/lib/lean", exporter) for p in paths.values())
        runner.run([executable, lock["module"]], exporter, "retry exact full Mathlib export", EXPORT_SECONDS,
                   search=search, output=output, output_limit=lock["expected"]["size"] + 1048576)
        if source_hashes(lock) != original:
            raise ValueError("source set changed during retry")
        actual, matched = inspect_output(output, lock["expected"])
        runner.report.update(actual=actual, status="exact_match" if matched else "different_bytes")
        if matched:
            final = WORK / "exports/mathlib.ndjson"
            final.parent.mkdir(exist_ok=True)
            if final.exists():
                if not inspect_output(final, lock["expected"])[1]:
                    raise ValueError("existing final output differs; preserved")
            else:
                output.replace(final)
            runner.report["final_output"] = str(final.relative_to(WORK))
    except (OSError, ValueError, RuntimeError) as exc:
        runner.report.update(status="failed", error=str(exc))
        raise
    finally:
        try:
            runner.report["sources_unchanged_at_finish"] = source_hashes(lock) == original
        except (OSError, ValueError) as exc:
            runner.report.update(source_integrity_error=str(exc), status="failed")
        if output.exists():
            runner.report["retained_unpromoted_output"] = {
                "path": str(output.relative_to(WORK)), "size": output.stat().st_size, "sha256": digest(output)}
        runner.report.update(finished_at=utc_now(),
            previous_report_unchanged=digest(PREVIOUS / "report.json") == PREVIOUS_SHA256,
            shared_manifest_at_finish_sha256=digest(ROOT / "arena/manifest.json"))
        runner.save()
        write_json(WORK / "latest-export-retry.json", {
            "report": str(runner.path.relative_to(WORK)), "status": runner.report["status"]})
    return 0 if runner.report["status"] == "exact_match" else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--execute-reviewed", action="store_true")
    args = parser.parse_args()
    lock = load_lock()
    if args.execute_reviewed:
        return execute(lock)
    print(json.dumps({"previous_report": str(PREVIOUS / "report.json"),
        "previous_report_sha256": PREVIOUS_SHA256, "memory_mib": MEMORY_MIB,
        "export_timeout_seconds": EXPORT_SECONDS, "network": False,
        "checker_run": False, "manifest_import": False, "expected": lock["expected"]}, indent=2))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, RuntimeError) as exc:
        print(f"Mathlib export retry failed: {exc}", file=sys.stderr)
        sys.exit(1)
