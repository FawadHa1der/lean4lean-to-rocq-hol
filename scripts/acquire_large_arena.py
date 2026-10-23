#!/usr/bin/env python3
"""Reproduce only the reviewed, pinned Init/Std exports without upstream hooks."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

from fetch_arena import git
from test_arena import digest, positive_seconds, stop_group, utc_now, write_json

ROOT = Path(__file__).resolve().parents[1]
ARENA = ROOT / "arena"
WORK = ARENA / "large"
PROFILE = """(version 1)
(deny default)
(allow process*)
(allow file-read*)
(allow sysctl-read)
(allow mach-lookup)
(allow file-write* (subpath (param "WORK")) (literal "/dev/null"))
"""


def verified_blob(repository, revision, filename, expected=None):
    blob = git(repository, "show", f"{revision}:{filename}")
    if expected and hashlib.sha256(blob).hexdigest() != expected:
        raise ValueError(f"source hash mismatch: {filename}")
    return blob


def inspect_output(path, expected):
    with path.open("rb") as stream:
        lines = sum(1 for _ in stream)
    actual = {"sha256": digest(path), "size": path.stat().st_size, "lines": lines}
    return actual, all(actual[key] == expected[key] for key in actual)


def prerequisites(toolchain):
    lock = json.loads((WORK / "acquisition.lock.json").read_text())
    generation = json.loads((ARENA / "generation.lock.json").read_text())
    for key in ("arena_revision", "exporter_revision", "lean_version", "lean_githash"):
        if generation[key] != lock[key]:
            raise ValueError(f"generation lock differs: {key}")
    provenance = json.loads((ARENA / "provenance.lock.json").read_text())
    if provenance["upstream"]["published_revision"] != lock["arena_revision"]:
        raise ValueError("published Arena revision mismatch")
    result_pin = next(x for x in provenance["downloads"] if x["name"] == "results.json")
    results_path = ARENA / "downloads/results.json"
    if results_path.stat().st_size != result_pin["size"] or digest(results_path) != result_pin["sha256"]:
        raise ValueError("published results do not match provenance lock")
    published = json.loads(results_path.read_text())
    if published["meta"]["git_revision"] != lock["arena_revision"]:
        raise ValueError("published result revision mismatch")
    cases = {case["name"]: case for case in published["tests"]}
    for name, expected in lock["cases"].items():
        case = cases[name]
        for key in ("size", "sha256", "lines"):
            if case[key] != expected[key]:
                raise ValueError(f"published {name} {key} mismatch")
        if case["outcome"] != "accept" or case["lean_githash"] != lock["lean_githash"]:
            raise ValueError(f"unexpected published toolchain/outcome: {name}")
        verified_blob(ARENA / "upstream", lock["arena_revision"], expected["source"], expected["source_sha256"])
        verified_blob(ARENA / "upstream", lock["arena_revision"], expected["definition"], expected["definition_sha256"])
    lean = toolchain.resolve() / "bin/lean"
    version = subprocess.check_output([str(lean), "--version"], text=True, timeout=30).strip()
    if lock["lean_version"] not in version or lock["lean_githash"] not in version:
        raise ValueError(f"wrong generation toolchain: {version}")
    return lock, cases, lean, version


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--execute-reviewed", action="store_true")
    parser.add_argument("--toolchain-dir", type=Path, default=ARENA / "generation/toolchain/lean-4.34.1-darwin_aarch64")
    parser.add_argument("--step-timeout", type=positive_seconds, default=600)
    parser.add_argument("--case", action="append", choices=("init", "std"))
    args = parser.parse_args(argv)
    lock, published, lean, version = prerequisites(args.toolchain_dir)
    selected = list(dict.fromkeys(args.case or ["init", "std"]))
    print(json.dumps({"lean": version, "cases": {name: lock["cases"][name] for name in selected},
                      "step_timeout_seconds": args.step_timeout, "sandbox": PROFILE}, indent=2), flush=True)
    if not args.execute_reviewed:
        print("Preflight only; inspect source and pass --execute-reviewed to generate.")
        return 0
    if shutil.disk_usage(WORK).free < 3 * sum(lock["cases"][name]["size"] for name in selected):
        raise ValueError("less than three times selected output bytes free")
    run_dir = WORK / "runs" / f"{time.time_ns()}-{os.getpid()}"
    for part in ("home", "tmp", "logs", "exporter"):
        (run_dir / part).mkdir(parents=True)
    (WORK / "exports").mkdir(exist_ok=True)
    report_path = run_dir / "generation-report.json"
    report = {"started_at": utc_now(), "finished_at": None, "lock": lock,
              "script_sha256": digest(Path(__file__)), "lean_version": version,
              "lean_binary_sha256": digest(lean), "sandbox_profile": PROFILE,
              "steps": [], "cases": []}

    def run(command, cwd, label, output=None):
        index = len(report["steps"])
        stdout = output or run_dir / "logs" / f"{index:03d}.stdout"
        stderr = run_dir / "logs" / f"{index:03d}.stderr"
        env = {"HOME": str(run_dir / "home"), "TMPDIR": str(run_dir / "tmp"),
               "LEAN_ABORT_ON_PANIC": "1", "LEAN_PATH": ".:../exporter",
               "PATH": f"{os.path.relpath(lean.parent, cwd)}:/usr/bin:/bin"}
        cmd = ["/usr/bin/sandbox-exec", "-D", f"WORK={WORK}", "-p", PROFILE, *map(str, command)]
        start = time.monotonic()
        timed_out = False
        with stdout.open("wb") as out, stderr.open("wb") as err:
            proc = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=out, stderr=err, start_new_session=True)
            try:
                proc.wait(timeout=args.step_timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
            finally:
                stop_group(proc)
        step = {"label": label, "command": list(map(str, command)), "cwd": str(cwd),
                "timeout_seconds": args.step_timeout, "timed_out": timed_out,
                "elapsed_seconds": round(time.monotonic() - start, 3), "exit_code": proc.returncode,
                "stdout": str(stdout.relative_to(WORK)), "stderr": str(stderr.relative_to(WORK))}
        report["steps"].append(step)
        write_json(report_path, report)
        print(f"{label}: exit={proc.returncode} timeout={timed_out} seconds={step['elapsed_seconds']}", flush=True)
        return proc.returncode == 0 and not timed_out

    if not run(["/usr/bin/true"], run_dir, "sandbox probe"):
        raise RuntimeError("sandbox unavailable; no unsandboxed fallback")
    for filename in ("Export.lean", "Main.lean", "LICENSE"):
        blob = verified_blob(ARENA / "exporter-source", lock["exporter_revision"], filename)
        (run_dir / "exporter" / filename).write_bytes(blob)
    report["exporter_source_sha256"] = {
        name: digest(run_dir / "exporter" / name) for name in ("Export.lean", "Main.lean", "LICENSE")}
    if not run([lean, "-o", "Export.olean", "Export.lean"], run_dir / "exporter", "compile pinned exporter"):
        raise RuntimeError(f"exporter compilation failed: {report_path}")
    for name in selected:
        expected = lock["cases"][name]
        output = WORK / "exports" / f"{name}.ndjson"
        record = {"id": name, "expected": expected, "path": str(output.relative_to(WORK))}
        if output.exists():
            actual, matched = inspect_output(output, expected)
            record.update(actual=actual, status="reused_exact_match" if matched else "existing_mismatch")
        else:
            directory = run_dir / name
            directory.mkdir()
            (directory / "Test.lean").write_bytes(verified_blob(
                ARENA / "upstream", lock["arena_revision"], expected["source"], expected["source_sha256"]))
            partial = directory / f"{name}.partial.ndjson"
            compiled = run([lean, "-o", "Test.olean", "Test.lean"], directory, f"compile {name}")
            # No '--': Main.lean interprets an empty declaration selection as no exports.
            exported = compiled and run([lean, "--run", "../exporter/Main.lean", "Test"],
                                        directory, f"export {name}", partial)
            if exported:
                actual, matched = inspect_output(partial, expected)
                record.update(actual=actual, status="exact_match" if matched else "different_bytes")
                if matched:
                    partial.replace(output)
                else:
                    record["mismatched_output"] = str(partial.relative_to(WORK))
            else:
                record["status"] = "generation_error"
        report["cases"].append(record)
        write_json(report_path, report)
        print(f"{name}: {record['status']}", flush=True)
    report["finished_at"] = utc_now()
    write_json(report_path, report)
    if all(case["status"] in {"exact_match", "reused_exact_match"} for case in report["cases"]):
        subset = {"manifest_version": 1, "provenance": {"large_input_lock": lock}, "cases": []}
        for record in report["cases"]:
            name = record["id"]
            expected = lock["cases"][name]
            subset["cases"].append({"id": name, "expected": "accept", "availability": "available",
                                    "source_kind": "leanfile_export", "origin": "generated_local",
                                    "path": record["path"], "timeout_seconds": expected["upstream_timeout_seconds"],
                                    **{key: expected[key] for key in ("size", "sha256", "lines")}})
        write_json(WORK / "manifest.json", subset)
        write_json(WORK / "latest-generation.json", {"report": str(report_path.relative_to(WORK))})
        print(f"Exact-match inputs ready. Report: {report_path}")
        return 0
    return 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, RuntimeError, subprocess.SubprocessError) as exc:
        print(f"Large Arena acquisition failed: {exc}", file=sys.stderr)
        sys.exit(1)
