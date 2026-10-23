#!/usr/bin/env python3
# Copyright (c) 2026 Fawad Haider. All rights reserved.
"""Explicit, sandboxed generation of the reviewed small missing Arena subset."""

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import time

from fetch_arena import git
from test_arena import DEFAULT_MANIFEST, digest, load_manifest, stop_group, write_json


PROFILE = """(version 1)
(deny default)
(allow process*)
(allow file-read*)
(allow sysctl-read)
(allow mach-lookup)
(allow file-write* (subpath (param "WORK")) (literal "/dev/null"))
"""


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--execute-reviewed", action="store_true", required=True)
    parser.add_argument("--toolchain-dir", type=Path, required=True)
    parser.add_argument("--step-timeout", type=float, default=600)
    parser.add_argument("--only", action="append", default=[], help="exact case id within the bounded scope")
    args = parser.parse_args(argv)
    root = DEFAULT_MANIFEST.parent
    work = root / "generation"
    work.mkdir(exist_ok=True)
    lock = json.loads((root / "generation.lock.json").read_text())
    manifest = load_manifest(DEFAULT_MANIFEST)
    lean = args.toolchain_dir.resolve() / "bin/lean"
    version = subprocess.check_output([str(lean), "--version"], text=True).strip()
    if lock["lean_version"] not in version or lock["lean_githash"][:12] not in version:
        raise ValueError(f"wrong Lean toolchain: {version}")
    report_path = root / "generation-report.json"
    report = {"lock": lock, "lean_version_output": version, "lean_binary_sha256": digest(lean),
              "script_sha256": digest(Path(__file__)), "sandbox_profile": PROFILE,
              "steps": [], "cases": [], "finished": False}
    env = {"HOME": str(work / "home"),
           "TMPDIR": str(work / "tmp"), "LEAN_ABORT_ON_PANIC": "1"}
    for directory in (work / "home", work / "tmp", work / "logs", work / "exports"):
        directory.mkdir(exist_ok=True)

    def run(command, cwd, label, output=None, search="."):
        index = len(report["steps"])
        stdout = output or work / "logs" / f"{index:03d}.stdout"
        stderr = work / "logs" / f"{index:03d}.stderr"
        stdout.parent.mkdir(parents=True, exist_ok=True)
        cmd = ["/usr/bin/sandbox-exec", "-D", f"WORK={work}", "-p", PROFILE, *map(str, command)]
        start = time.monotonic()
        timed_out = False
        with stdout.open("wb") as out, stderr.open("wb") as err:
            process_env = {**env, "LEAN_PATH": search,
                           "PATH": f"{os.path.relpath(lean.parent, cwd)}:/usr/bin:/bin"}
            proc = subprocess.Popen(cmd, cwd=cwd, env=process_env,
                                    stdout=out, stderr=err, start_new_session=True)
            try:
                proc.wait(timeout=args.step_timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
            finally:
                stop_group(proc)
        step = {"label": label, "command": list(map(str, command)), "cwd": str(cwd),
                "lean_path": search, "exit_code": proc.returncode, "timeout": timed_out,
                "elapsed_seconds": round(time.monotonic() - start, 3),
                "stdout": str(stdout.relative_to(root)), "stderr": str(stderr.relative_to(root))}
        report["steps"].append(step)
        write_json(report_path, report)
        print(f"{label}: exit={proc.returncode} seconds={step['elapsed_seconds']}", flush=True)
        return proc.returncode == 0 and not timed_out

    # Verify the sandbox itself before executing any downloaded source.
    if not run(["/usr/bin/true"], work, "sandbox-probe"):
        raise RuntimeError("sandbox unavailable; refusing unsandboxed generation")
    exporters = {}

    def exporter(revision):
        if revision in exporters:
            return exporters[revision]
        directory = work / f"exporter-{revision[:12]}"
        directory.mkdir(exist_ok=True)
        for filename in ("Export.lean", "Main.lean"):
            (directory / filename).write_bytes(git(root / "exporter-source", "show", f"{revision}:{filename}"))
        if not run([lean, "-o", "Export.olean", "Export.lean"], directory, f"compile exporter {revision[:12]}"):
            raise RuntimeError("exporter compilation failed; see generation/logs")
        exporters[revision] = directory
        return directory

    exporter(lock["exporter_revision"])
    compiled = {}
    for case in manifest["cases"]:
        selected = case["expected"] == "either" and case["source_kind"] != "static"
        selected = selected or case["id"] in {"perf/magma-string-n4", "perf/magma-string-pair-n9"}
        if not selected or (args.only and case["id"] not in args.only):
            continue
        config = case["configuration"]
        record = {"id": case["id"], "published_sha256": case["sha256"], "published_size": case["size"]}
        try:
            exp = exporter(lock["exporter_revision"])
            if "leanfile" in config:
                source = config["leanfile"]
                key = source
                directory = work / Path(source).stem
                directory.mkdir(exist_ok=True)
                (directory / "Test.lean").write_bytes(git(root / "upstream", "show", f"{lock['arena_revision']}:{source}"))
                module = "Test"
                files = ["Test.lean"]
            else:
                if case["id"] != "corner-cases/nested-nonuniform-param":
                    raise ValueError("module outside reviewed generation scope")
                exp = exporter(lock["tutorial_exporter_revision"])
                key = "nested-nonuniform-param"
                directory = work / "tutorial"
                module = "CornerCases.NestedNonuniformParam"
                files = ["Tutorial/AddConstInfo.lean", "Tutorial/Export.lean", "Tutorial/TestCaseEnv.lean",
                         "Tutorial/Meta.lean", "CornerCases/NestedNonuniformParam.lean"]
                for filename in files:
                    target = directory / filename
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes(git(root / "upstream", "show", f"{lock['arena_revision']}:tutorial/{filename}"))
            # Relative search paths avoid ':' in the shared project's directory name.
            search = f".:../{exp.name}"
            if key not in compiled:
                compiled[key] = all(run([lean, "-o", str(Path(f).with_suffix(".olean")), f], directory,
                                        f"compile {key} {f}", search=search) for f in files)
            if not compiled[key]:
                record["status"] = "generation_error"
            else:
                out = work / "exports" / f"{case['id']}.ndjson"
                command = [lean, "--run", f"../{exp.name}/Main.lean", module, "--", *config.get("export-decls", [])]
                if run(command, directory, f"export {case['id']}", output=out, search=search):
                    record.update(path=str(out.relative_to(root)), sha256=digest(out), size=out.stat().st_size)
                    record["status"] = "exact_match" if record["sha256"] == case["sha256"] else "different_bytes"
                else:
                    record["status"] = "generation_error"
        except (OSError, RuntimeError, subprocess.CalledProcessError, ValueError) as exc:
            record.update(status="generation_error", error=str(exc))
        report["cases"].append(record)
        write_json(report_path, report)
        print(f"{record['id']}: {record['status']}", flush=True)
    report["finished"] = True
    write_json(report_path, report)
    return 0 if all(item["status"] == "exact_match" for item in report["cases"]) else 1


if __name__ == "__main__":
    sys.exit(main())
