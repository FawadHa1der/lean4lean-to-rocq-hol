#!/usr/bin/env python3
"""Run reviewed CSLib cache/build/export stages under local resource limits."""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

from acquire_cslib_arena import ROOT, WORK, load_lock, source_hashes, source_paths
from acquire_large_arena import PROFILE, inspect_output, verified_blob
from build_con_leche_arena import group_rss_kib
from fetch_arena import verify_file
from test_arena import digest, positive_seconds, stop_group, utc_now, write_json

# Only the reviewed, already-compiled cache executable gets this network policy.
CACHE_PROFILE = PROFILE + """
(allow network-outbound
  (remote tcp "*:443")
  (literal "/private/var/run/mDNSResponder"))
"""
CURL_POLICY = """proto = \"=https\"
proto-redir = \"=https\"
parallel-max = 2
connect-timeout = 15
max-time = 60
max-filesize = 134217728
"""


def package_overrides(lock, paths, project):
    manifest = json.loads((project / "lake-manifest.json").read_text())
    return {"schemaVersion": "1.2.0", "packages": [
        {"name": p["name"], "scope": p["scope"], "type": "path",
         "dir": os.path.relpath(paths[p["name"]], project), "inherited": p["inherited"],
         "configFile": p["configFile"], "manifestFile": p["manifestFile"]}
        for p in manifest["packages"]]}


def cache_layout(paths, project):
    # Upstream LTARs use this layout for dependencies other than Mathlib.
    directory = project / ".lake/packages"
    directory.mkdir(parents=True, exist_ok=True)
    for name, path in paths.items():
        if name == "cslib":
            continue
        link = directory / name
        if link.is_symlink():
            if link.resolve() != path.resolve():
                raise ValueError(f"unexpected package link preserved: {link}")
        elif link.exists():
            raise ValueError(f"unexpected package directory preserved: {link}")
        else:
            link.symlink_to(os.path.relpath(path, directory), target_is_directory=True)


class Runner:
    def __init__(self, lock, args, lean):
        self.args, self.lean = args, lean
        self.directory = WORK / "runs" / f"{time.time_ns()}-{os.getpid()}"
        for name in ("home", "tmp", "logs", "exporter"):
            (self.directory / name).mkdir(parents=True)
        (self.directory / "home/.curlrc").write_text(CURL_POLICY)
        self.path = self.directory / "report.json"
        self.report = {"started_at": utc_now(), "finished_at": None, "status": "running", "lock": lock,
                       "scripts_sha256": {p: digest(ROOT / "scripts" / p) for p in (
                           "build_cslib_arena.py", "inspect_cslib_imports.lean", "acquire_cslib_arena.py", "acquire_cedar_arena.py",
                           "acquire_large_arena.py", "build_con_leche_arena.py", "test_arena.py", "fetch_arena.py")},
                       "memory_mib_sampled_limit": args.memory_mib, "threads_environment": 2,
                       "network_policy": "HTTPS and macOS DNS resolver only, only reviewed compiled cache process",
                       "curl_policy": CURL_POLICY, "steps": []}

    def save(self):
        write_json(self.path, self.report)

    def run(self, command, cwd, label, timeout, search=".", source_search=".", output=None, network=False):
        index = len(self.report["steps"])
        stdout = output or self.directory / "logs" / f"{index:03d}.stdout"
        stderr = self.directory / "logs" / f"{index:03d}.stderr"
        env = {"HOME": str(self.directory / "home"), "TMPDIR": str(self.directory / "tmp"),
               "CURL_HOME": str(self.directory / "home"),
               "PATH": f"{os.path.relpath(self.lean.parent, cwd)}:/usr/bin:/bin",
               "LEAN_PATH": search, "LEAN_SRC_PATH": source_search,
               "LEAN_NUM_THREADS": "2", "RAYON_NUM_THREADS": "2", "LEAN_ABORT_ON_PANIC": "1",
               "MATHLIB_NO_CACHE_ON_UPDATE": "1", "MATHLIB_CACHE_DIR": str(WORK / "cache")}
        profile = CACHE_PROFILE if network else PROFILE
        command = list(map(str, command))
        step = {"label": label, "command": command, "cwd": str(cwd), "environment": env,
                "sandbox": profile, "timeout_seconds": timeout, "started_at": utc_now(),
                "stdout": str(stdout.relative_to(WORK)), "stderr": str(stderr.relative_to(WORK))}
        self.report["steps"].append(step)
        self.save()
        start, peak, reason = time.monotonic(), 0, None
        wrapped = ["/usr/bin/sandbox-exec", "-D", f"WORK={WORK}", "-p", profile, *command]
        with stdout.open("wb") as out, stderr.open("wb") as err:
            proc = subprocess.Popen(wrapped, cwd=cwd, env=env, stdout=out, stderr=err, start_new_session=True)
            try:
                while proc.poll() is None:
                    peak = max(peak, group_rss_kib(proc.pid))
                    if time.monotonic() - start >= timeout:
                        reason = "wall_timeout"
                    elif peak > self.args.memory_mib * 1024:
                        reason = "sampled_memory_limit"
                    elif shutil.disk_usage(WORK).free < 32 * 1024**3:
                        reason = "disk_reserve_limit"
                    elif output and stdout.stat().st_size > self.report["lock"]["expected"]["size"] + 1048576:
                        reason = "output_size_limit"
                    if reason:
                        break
                    time.sleep(0.5)
            finally:
                stop_group(proc)
        step.update(exit_code=proc.returncode, stop_reason=reason,
                    elapsed_seconds=round(time.monotonic() - start, 3), sampled_peak_rss_kib=peak)
        self.save()
        print(f"{label}: exit={proc.returncode} stop={reason} seconds={step['elapsed_seconds']}", flush=True)
        if reason or proc.returncode:
            raise RuntimeError(f"{label} failed; inspect {self.path}")


def execute(lock, args):
    if shutil.disk_usage(WORK).free < 32 * 1024**3:
        raise ValueError("at least 32 GiB free required")
    original, paths = source_hashes(lock), source_paths(lock)
    project = paths["cslib"]
    toolchain = WORK / "toolchain" / lock["toolchain"]["directory"]
    lean, lake = toolchain / "bin/lean", toolchain / "bin/lake"
    verify_file(WORK / "downloads" / lock["toolchain"]["filename"], lock["toolchain"])
    version = subprocess.check_output([str(lean), "--version"], text=True, timeout=30).strip()
    if lock["lean_version"] not in version or lock["lean_githash"] not in version:
        raise ValueError(f"toolchain differs: {version}")
    run = Runner(lock, args, lean)
    run.report.update(lean_version=version, source_hashes=original,
                      toolchain_binary_sha256={p: digest(toolchain / "bin" / p) for p in ("lean", "lake", "leantar")})
    print(f"CSLib report: {run.path}", flush=True)
    try:
        cache_layout(paths, project)
        overrides = run.directory / "packages.json"
        write_json(overrides, package_overrides(lock, paths, project))
        run.report["package_overrides_sha256"] = digest(overrides)
        lake_args = [lake, "--no-cache", "--no-ansi", "--packages", overrides]
        run.run(["/usr/bin/true"], project, "sandbox probe", 10)
        run.run([*lake_args, "build", "cache"], project, "compile pinned Mathlib cache tool", args.cache_build_timeout)
        cache_exe = paths["mathlib"] / ".lake/build/bin/cache"
        run.report["cache_binary_sha256"] = digest(cache_exe)
        source_search = ":".join(os.path.relpath(path, project) for path in paths.values())
        search = ":".join(os.path.relpath(path / ".lake/build/lib/lean", project) for path in paths.values())
        if args.allow_cache_download:
            run.run([cache_exe, "get", "--repo=leanprover-community/mathlib4"], project,
                    "get exact-source Mathlib cache", args.cache_timeout, search, source_search, network=True)
        else:
            run.run([cache_exe, "unpack"], project, "unpack existing local Mathlib cache",
                    args.cache_timeout, search, source_search)
        cache_step = run.report["steps"][-1]
        run.report["upstream_reports_cache_misses"] = any(
            "some files were not found in the cache" in (WORK / cache_step[key]).read_text()
            for key in ("stdout", "stderr"))
        missing = []
        for source in [paths["mathlib"] / "Mathlib.lean", *(paths["mathlib"] / "Mathlib").rglob("*.lean")]:
            compiled = paths["mathlib"] / ".lake/build/lib/lean" / source.relative_to(paths["mathlib"]).with_suffix(".olean")
            if not compiled.is_file():
                missing.append(str(source.relative_to(paths["mathlib"])))
        run.report["missing_mathlib_oleans"] = missing
        closure_path = run.directory / "import-closure.json"
        run.run([lean, "--run", ROOT / "scripts/inspect_cslib_imports.lean"], project,
                "inspect unmodified Cslib transitive imports", 90, search, source_search, closure_path)
        closure = json.loads(closure_path.read_text())
        run.report["import_closure_sha256"] = digest(closure_path)
        run.report["missing_required_dependency_oleans"] = closure["missing_dependency_oleans"]
        if closure["root"] != lock["module"] or closure["missing_dependency_oleans"]:
            raise ValueError("required dependency cache incomplete; no implicit dependency source rebuild")
        dependency_targets = sorted(f"+{p['module']}:olean" for p in closure["modules"] if not p["is_cslib"])
        run.report["required_dependency_count"] = len(dependency_targets)
        # The no-build gate checks trace freshness too, not merely file presence.
        for start in range(0, len(dependency_targets), 500):
            run.run([*lake_args, "--no-build", "build", *dependency_targets[start:start + 500]],
                    project, f"check cached dependency traces {start + 1}-{min(start + 500, len(dependency_targets))}", 60)
        run.report["sources_unchanged_after_cache"] = source_hashes(lock) == original
        cache_files = sorted((WORK / "cache").glob("*.ltar"))
        cache_index = {p.name: {"sha256": digest(p), "size": p.stat().st_size} for p in cache_files}
        write_json(run.directory / "cache-files.json", cache_index)
        run.report["cache_files_index_sha256"] = digest(run.directory / "cache-files.json")
        run.report["cache_file_count"] = len(cache_index)
        if not cache_index:
            raise ValueError("no Mathlib cache available; refusing an implicit full Mathlib rebuild")
        run.run([*lake_args, "build", lock["module"]], project, "build full pinned Cslib module", args.build_timeout)
        run.report["sources_unchanged_after_build"] = source_hashes(lock) == original
        exporter = run.directory / "exporter"
        files = ("Export.lean", "Main.lean", "LICENSE", "lakefile.toml", "lake-manifest.json")
        for name in files:
            (exporter / name).write_bytes(verified_blob(ROOT / "arena/exporter-source", lock["exporter_revision"], name))
        run.report["exporter_source_sha256"] = {p: digest(exporter / p) for p in files}
        run.run([lake, "--no-cache", "--no-ansi", "build", "lean4export"], exporter,
                "compile pinned native exporter", 180)
        executable = exporter / ".lake/build/bin/lean4export"
        run.report["exporter_binary_sha256"] = digest(executable)
        search = ":".join(os.path.relpath(path / ".lake/build/lib/lean", exporter) for path in paths.values())
        output = run.directory / "cslib.partial.ndjson"
        run.run([executable, lock["module"]], exporter, "export full Cslib module", args.export_timeout,
                search=search, output=output)
        run.report["sources_unchanged_after_export"] = source_hashes(lock) == original
        actual, matched = inspect_output(output, lock["expected"])
        run.report.update(actual=actual, status="exact_match" if matched else "different_bytes")
        if matched:
            final = WORK / "exports/cslib.ndjson"
            final.parent.mkdir(exist_ok=True)
            if final.exists():
                if not inspect_output(final, lock["expected"])[1]:
                    raise ValueError("existing final export differs; preserving it")
            else:
                output.replace(final)
            run.report["final_output"] = str(final.relative_to(WORK))
            # Deliberately no shared manifest import: active parent tests own that state.
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as exc:
        run.report.update(status="failed", error=str(exc))
        raise
    finally:
        try:
            run.report["sources_unchanged_at_finish"] = source_hashes(lock) == original
        except (OSError, ValueError) as exc:
            run.report["source_integrity_error_at_finish"] = str(exc)
            run.report["status"] = "failed"
        run.report["finished_at"] = utc_now()
        run.save()
        write_json(WORK / "latest-build.json", {"report": str(run.path.relative_to(WORK)), "status": run.report["status"]})
    return 0 if run.report["status"] == "exact_match" else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--execute-reviewed", action="store_true")
    parser.add_argument("--allow-cache-download", action="store_true")
    parser.add_argument("--cache-build-timeout", type=positive_seconds, default=180)
    parser.add_argument("--cache-timeout", type=positive_seconds, default=600)
    parser.add_argument("--build-timeout", type=positive_seconds, default=600)
    parser.add_argument("--export-timeout", type=positive_seconds, default=300)
    parser.add_argument("--memory-mib", type=int, default=8192)
    args = parser.parse_args()
    if not 0 < args.memory_mib <= 8192:
        parser.error("--memory-mib must be positive and at most 8192")
    if args.allow_cache_download and not args.execute_reviewed:
        parser.error("--allow-cache-download requires --execute-reviewed")
    lock = load_lock()
    if args.execute_reviewed:
        return execute(lock, args)
    print(json.dumps({"lock": lock, "limits": vars(args), "build_sandbox": PROFILE,
                      "cache_sandbox": CACHE_PROFILE, "curl_policy": CURL_POLICY}, indent=2))
    print("Read-only preflight. No shared manifest or checker binaries are modified.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, StopIteration, RuntimeError, subprocess.SubprocessError) as exc:
        print(f"CSLib build failed: {exc}", file=sys.stderr)
        sys.exit(1)
