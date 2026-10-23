#!/usr/bin/env python3
"""Bounded, network-denied Con-Leche build and exact pinned Arena export."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import time

from acquire_con_leche_arena import ROOT, WORK, load_lock
from acquire_large_arena import PROFILE, inspect_output, verified_blob
from fetch_arena import verify_file
from test_arena import digest, positive_seconds, stop_group, utc_now, write_json


def source_hashes(lock, source):
    archive = WORK / "downloads" / lock["source"]["filename"]
    verify_file(archive, lock["source"])
    hashes = {}
    with tarfile.open(archive, "r:gz") as tar:
        for member in tar:
            if member.isfile():
                relative = Path(member.name).relative_to(lock["source"]["directory"])
                with tar.extractfile(member) as stream:
                    expected = hashlib.file_digest(stream, "sha256").hexdigest()
                if digest(source / relative) != expected:
                    raise ValueError(f"source changed from archive: {relative}")
                hashes[str(relative)] = expected
    if (source / "lakefile.lean").exists():
        raise ValueError("unexpected executable Lake configuration")
    if json.loads((source / "lake-manifest.json").read_text())["packages"]:
        raise ValueError("unreviewed external Lake dependencies")
    if (source / "lean-toolchain").read_text().strip() != f"leanprover/lean4:v{lock['lean_version']}":
        raise ValueError("source toolchain differs from pinned version")
    return hashes


def group_rss_kib(pgid):
    listing = subprocess.check_output(["/bin/ps", "-axo", "pgid=,rss="], text=True, timeout=5)
    return sum(int(rss) for group, rss in (line.split() for line in listing.splitlines())
               if int(group) == pgid)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--execute-reviewed", action="store_true", required=True)
    parser.add_argument("--build-timeout", type=positive_seconds, default=900)
    parser.add_argument("--export-timeout", type=positive_seconds, default=300)
    parser.add_argument("--memory-mib", type=int, default=8192,
                        help="sampled aggregate process-group RSS stop threshold, not a hard OS cap")
    args = parser.parse_args()
    if args.memory_mib <= 0:
        parser.error("--memory-mib must be positive")
    lock = load_lock()
    source = WORK / "source" / lock["source"]["directory"]
    toolchain = WORK / "toolchain" / lock["toolchain"]["directory"]
    lean, lake = toolchain / "bin/lean", toolchain / "bin/lake"
    verify_file(WORK / "downloads" / lock["toolchain"]["filename"], lock["toolchain"])
    original = source_hashes(lock, source)
    version = subprocess.check_output([str(lean), "--version"], text=True, timeout=30).strip()
    if lock["lean_version"] not in version or lock["lean_githash"] not in version:
        raise ValueError(f"wrong local generation toolchain: {version}")
    directory = WORK / "runs" / f"{time.time_ns()}-{os.getpid()}"
    for part in ("home", "tmp", "logs", "exporter"):
        (directory / part).mkdir(parents=True)
    report_path = directory / "report.json"
    report = {"started_at": utc_now(), "finished_at": None, "status": "running", "lock": lock,
              "lean_version": version, "lean_binary_sha256": digest(lean),
              "lake_binary_sha256": digest(lake), "source_hashes": original,
              "script_sha256": digest(Path(__file__)), "sandbox_profile": PROFILE,
              "memory_mib_sampled_limit": args.memory_mib, "steps": []}
    write_json(report_path, report)

    def run(command, cwd, label, timeout, output=None, search=".", max_bytes=None):
        index = len(report["steps"])
        stdout = output or directory / "logs" / f"{index:03d}.stdout"
        stderr = directory / "logs" / f"{index:03d}.stderr"
        env = {"HOME": str(directory / "home"), "TMPDIR": str(directory / "tmp"),
               "PATH": f"{os.path.relpath(lean.parent, cwd)}:/usr/bin:/bin", "LEAN_PATH": search,
               "LEAN_ABORT_ON_PANIC": "1", "LEAN_NUM_THREADS": "2"}
        command = list(map(str, command))
        step = {"label": label, "command": command, "cwd": str(cwd), "environment": env,
                "timeout_seconds": timeout, "started_at": utc_now(), "status": "running",
                "stdout": str(stdout.relative_to(WORK)), "stderr": str(stderr.relative_to(WORK))}
        report["steps"].append(step)
        write_json(report_path, report)
        wrapped = ["/usr/bin/sandbox-exec", "-D", f"WORK={WORK}", "-p", PROFILE, *command]
        start, peak, stop = time.monotonic(), 0, None
        with stdout.open("wb") as out, stderr.open("wb") as err:
            proc = subprocess.Popen(wrapped, cwd=cwd, env=env, stdout=out, stderr=err, start_new_session=True)
            try:
                while proc.poll() is None:
                    peak = max(peak, group_rss_kib(proc.pid))
                    if time.monotonic() - start >= timeout:
                        stop = "wall_timeout"
                    elif peak > args.memory_mib * 1024:
                        stop = "sampled_memory_limit"
                    elif max_bytes is not None and stdout.stat().st_size > max_bytes:
                        stop = "output_size_limit"
                    if stop:
                        break
                    time.sleep(0.5)
            finally:
                stop_group(proc)
        step.update(status="complete", exit_code=proc.returncode, stop_reason=stop,
                    sampled_peak_rss_kib=peak, elapsed_seconds=round(time.monotonic() - start, 3))
        write_json(report_path, report)
        print(f"{label}: exit={proc.returncode} stop={stop} seconds={step['elapsed_seconds']}", flush=True)
        if stop or proc.returncode:
            raise RuntimeError(f"{label} failed; inspect {report_path}")

    try:
        run(["/usr/bin/true"], source, "sandbox probe", 10)
        exporter = directory / "exporter"
        for filename in ("Export.lean", "Main.lean", "LICENSE"):
            (exporter / filename).write_bytes(verified_blob(
                ROOT / "arena/exporter-source", lock["exporter_revision"], filename))
        report["exporter_source_hashes"] = {name: digest(exporter / name)
                                           for name in ("Export.lean", "Main.lean", "LICENSE")}
        run([lean, "-o", "Export.olean", "Export.lean"], exporter, "compile pinned exporter", 120)
        run([lake, "--no-cache", "--no-ansi", "build", lock["module"]], source,
            "build ConLecheTests", args.build_timeout)
        report["source_unchanged_after_build"] = source_hashes(lock, source) == original
        search = f".:{os.path.relpath(source / '.lake/build/lib/lean', exporter)}"
        probe = f"import {lock['module']}\n" + "".join(
            f"#check {name}\n" for name in lock["export_declarations"])
        (exporter / "RecipeProbe.lean").write_text(probe)
        run([lean, "RecipeProbe.lean"], exporter, "check recipe declarations", 60, search=search)
        output = directory / "con-leche.partial.ndjson"
        run([lean, "--run", "Main.lean", lock["module"], "--", *lock["export_declarations"]],
            exporter, "export selected declarations", args.export_timeout, output, search,
            max_bytes=lock["expected"]["size"])
        actual, matched = inspect_output(output, lock["expected"])
        report.update(actual=actual, status="exact_match" if matched else "different_bytes")
        if matched:
            final = WORK / "exports/con-leche.ndjson"
            final.parent.mkdir(exist_ok=True)
            if final.exists():
                if not inspect_output(final, lock["expected"])[1]:
                    raise ValueError("existing final export differs; refusing to overwrite")
            else:
                output.replace(final)
            report["final_output"] = str(final.relative_to(WORK))
            write_json(WORK / "manifest.json", {"manifest_version": 1,
                "provenance": {"con_leche_lock": lock}, "cases": [{"id": "con-leche",
                    "expected": "accept", "availability": "available", "source_kind": "module_export",
                    "origin": "generated_local", "path": str(final.relative_to(WORK)),
                    "timeout_seconds": 720, **lock["expected"]}]})
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as exc:
        report.update(status="failed", error=str(exc))
        raise
    finally:
        report["finished_at"] = utc_now()
        write_json(report_path, report)
        write_json(WORK / "latest-build.json", {"report": str(report_path.relative_to(WORK)),
                                                "status": report["status"]})
        print(f"Con-Leche report: {report_path}", flush=True)
    return 0 if report["status"] == "exact_match" else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, RuntimeError, subprocess.SubprocessError) as exc:
        print(f"Con-Leche build/export failed: {exc}", file=sys.stderr)
        sys.exit(1)
