#!/usr/bin/env python3
"""One bounded exact Mathlib acquisition attempt; no checker or shared-manifest writes."""

import argparse
from contextlib import ExitStack
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

from acquire_large_arena import PROFILE, inspect_output, verified_blob
from build_con_leche_arena import group_rss_kib
from build_cslib_arena import CACHE_PROFILE, CURL_POLICY
from prepare_mathlib_arena import ROOT, WORK, load_lock, source_hashes, source_paths, toolchain_check
from test_arena import digest, positive_seconds, stop_group, utc_now, write_json


def package_overrides(paths):
    project = paths["mathlib"]
    manifest = json.loads((project / "lake-manifest.json").read_text())
    return {"schemaVersion": "1.2.0", "packages": [
        {"name": p["name"], "scope": p["scope"], "type": "path",
         "dir": os.path.relpath(paths[p["name"]], project), "inherited": p["inherited"],
         "configFile": p["configFile"], "manifestFile": p["manifestFile"]}
        for p in manifest["packages"]]}


def prepare_layout(paths):
    project = paths["mathlib"]
    directory = project / ".lake/packages"
    directory.mkdir(parents=True, exist_ok=True)
    for name, path in paths.items():
        if name == "mathlib":
            continue
        link = directory / name
        if link.is_symlink():
            if link.resolve() != path.resolve():
                raise ValueError(f"unexpected package link preserved: {link}")
        elif link.exists():
            raise ValueError(f"unexpected package directory preserved: {link}")
        else:
            link.symlink_to(os.path.relpath(path, directory), target_is_directory=True)
    cache = WORK / "cache"
    marker = cache / "recipe.json"
    expected = {"lock_sha256": digest(WORK / "lock.json")}
    if marker.exists():
        if json.loads(marker.read_text()) != expected:
            raise ValueError("cache belongs to a different recipe; not reusing it")
    else:
        if cache.exists() and any(cache.iterdir()):
            raise ValueError("unrecognized cache preserved; no implicit reuse")
        cache.mkdir(exist_ok=True)
        write_json(marker, expected)


def cache_files():
    files = sorted((WORK / "cache").glob("*.ltar"))
    for path in files:
        if path.is_symlink() or not re.fullmatch(r"[0-9a-f]{16}\.ltar", path.name):
            raise ValueError(f"unrecognized cache artifact: {path}")
    return files


class Runner:
    def __init__(self, lock, args, toolchain):
        self.args, self.toolchain = args, toolchain
        self.directory = WORK / "runs" / f"{time.time_ns()}-{os.getpid()}"
        for name in ("home", "tmp", "logs", "exporter"):
            (self.directory / name).mkdir(parents=True)
        (self.directory / "home/.curlrc").write_text(CURL_POLICY)
        self.path = self.directory / "report.json"
        self.report = {"started_at": utc_now(), "finished_at": None, "status": "running", "lock": lock,
            "helper_sha256": {p: digest(ROOT / "scripts" / p) for p in (
                "acquire_mathlib_arena.py", "prepare_mathlib_arena.py", "inspect_mathlib_cache.lean",
                "acquire_cedar_arena.py", "acquire_large_arena.py", "build_con_leche_arena.py",
                "build_cslib_arena.py", "fetch_arena.py", "test_arena.py")},
            "memory_mib_sampled_limit": args.memory_mib, "thread_settings": 2,
            "decompressor_jobs": 2, "curl_policy": CURL_POLICY,
            "shared_manifest_at_start_sha256": digest(ROOT / "arena/manifest.json"),
            "checker_run": False, "steps": []}

    def save(self):
        write_json(self.path, self.report)

    def run(self, command, cwd, label, timeout, search=".", source_search=".",
            output=None, network=False, stdin=None, output_limit=None):
        index = len(self.report["steps"])
        stdout = output or self.directory / "logs" / f"{index:03d}.stdout"
        stderr = self.directory / "logs" / f"{index:03d}.stderr"
        env = {"HOME": str(self.directory / "home"), "TMPDIR": str(self.directory / "tmp"),
               "CURL_HOME": str(self.directory / "home"),
               "PATH": f"{os.path.relpath(self.toolchain / 'bin', cwd)}:/usr/bin:/bin",
               "LEAN_PATH": search, "LEAN_SRC_PATH": source_search,
               "LEAN_NUM_THREADS": "2", "RAYON_NUM_THREADS": "2", "LEAN_ABORT_ON_PANIC": "1",
               "MATHLIB_NO_CACHE_ON_UPDATE": "1", "MATHLIB_CACHE_DIR": str(WORK / "cache")}
        profile = CACHE_PROFILE if network else PROFILE
        command = list(map(str, command))
        step = {"label": label, "command": command, "cwd": str(cwd), "environment": env,
                "sandbox": profile, "timeout_seconds": timeout, "started_at": utc_now(),
                "stdout": str(stdout.relative_to(WORK)), "stderr": str(stderr.relative_to(WORK)),
                "stdin": str(stdin.relative_to(WORK)) if stdin else None}
        self.report["steps"].append(step)
        self.save()
        start, peak, reason = time.monotonic(), 0, None
        wrapped = ["/usr/bin/sandbox-exec", "-D", f"WORK={WORK}", "-p", profile, *command]
        with ExitStack() as stack:
            out = stack.enter_context(stdout.open("wb"))
            err = stack.enter_context(stderr.open("wb"))
            inp = stack.enter_context(stdin.open("rb")) if stdin else subprocess.DEVNULL
            proc = subprocess.Popen(wrapped, cwd=cwd, env=env, stdin=inp, stdout=out, stderr=err,
                                    start_new_session=True)
            try:
                while proc.poll() is None:
                    peak = max(peak, group_rss_kib(proc.pid))
                    if time.monotonic() - start >= timeout:
                        reason = "wall_timeout"
                    elif peak > self.args.memory_mib * 1024:
                        reason = "sampled_memory_limit"
                    elif shutil.disk_usage(WORK).free < 64 * 1024**3:
                        reason = "disk_reserve_limit"
                    elif output_limit is not None and stdout.stat().st_size > output_limit:
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
    if shutil.disk_usage(WORK).free < 64 * 1024**3:
        raise ValueError("at least 64 GiB free required")
    original, paths = source_hashes(lock), source_paths(lock)
    project = paths["mathlib"]
    toolchain, version = toolchain_check(lock)
    lean, lake, leantar = (toolchain / "bin" / name for name in ("lean", "lake", "leantar"))
    runner = Runner(lock, args, toolchain)
    runner.report.update(lean_version=version, source_hashes=original,
        toolchain_binary_sha256={p: digest(toolchain / "bin" / p) for p in ("lean", "lake", "leantar")})
    print(f"Mathlib report: {runner.path}", flush=True)
    output = runner.directory / "mathlib.partial.ndjson"
    try:
        prepare_layout(paths)
        overrides = runner.directory / "packages.json"
        write_json(overrides, package_overrides(paths))
        runner.report["package_overrides_sha256"] = digest(overrides)
        lake_args = [lake, "--no-cache", "--no-ansi", "--packages", overrides]
        runner.run(["/usr/bin/true"], project, "sandbox probe", 10)
        runner.run([*lake_args, "build", "cache"], project, "compile exact Mathlib cache tool", 180)
        cache_exe = project / ".lake/build/bin/cache"
        runner.report["cache_binary_sha256"] = digest(cache_exe)
        search = ":".join(os.path.relpath(p / ".lake/build/lib/lean", project) for p in paths.values())
        source_search = ":".join(os.path.relpath(p, project) for p in paths.values())
        if args.allow_cache_download:
            runner.run([cache_exe, "get-", "--repo=leanprover-community/mathlib4"], project,
                       "download exact-source Mathlib 4.34.1 cache", args.cache_timeout,
                       search, source_search, network=True)
        files = cache_files()
        if not files:
            raise ValueError("no matching cache; refusing a full source rebuild")
        index = {p.name: {"sha256": digest(p), "size": p.stat().st_size} for p in files}
        write_json(runner.directory / "cache-files.json", index)
        runner.report.update(cache_file_count=len(files),
            cache_files_index_sha256=digest(runner.directory / "cache-files.json"))
        decomp = runner.directory / "decompress.json"
        write_json(decomp, [str(p) for p in files])
        runner.run([leantar, "-x", "--jobs", "2", "-j", "-"], project,
                   "decompress pinned-recipe cache with two threads", 180, stdin=decomp)
        plan = runner.directory / "cache-plan.json"
        runner.run([lean, "--run", ROOT / "scripts/inspect_mathlib_cache.lean"], project,
                   "inspect full Mathlib cache closure", 90, search, source_search, plan)
        closure = json.loads(plan.read_text())
        if closure["root"] != lock["module"] or not closure["modules"]:
            raise ValueError("unexpected or empty cache closure")
        missing = closure["missing_oleans"]
        runner.report.update(cache_plan_sha256=digest(plan), required_module_count=len(closure["modules"]),
                             missing_oleans_before_build=missing)
        if len(missing) > args.max_missing_modules:
            raise ValueError(f"{len(missing)} missing modules exceed bounded source-build allowance {args.max_missing_modules}")
        runner.report["sources_unchanged_after_cache"] = source_hashes(lock) == original
        if not missing:
            runner.run([*lake_args, "--no-build", "build", lock["module"]], project,
                       "check complete cached Mathlib target traces", 90)
        runner.run([*lake_args, "build", lock["module"]], project,
                   "build original full Mathlib target", args.build_timeout)
        runner.report["sources_unchanged_after_build"] = source_hashes(lock) == original
        exporter = runner.directory / "exporter"
        names = ("Export.lean", "Main.lean", "LICENSE", "lakefile.toml", "lake-manifest.json")
        for name in names:
            (exporter / name).write_bytes(verified_blob(ROOT / "arena/exporter-source", lock["exporter_revision"], name))
        runner.report["exporter_source_sha256"] = {p: digest(exporter / p) for p in names}
        runner.run([lake, "--no-cache", "--no-ansi", "build", "lean4export"], exporter,
                   "compile exact native exporter", 180)
        executable = exporter / ".lake/build/bin/lean4export"
        runner.report["exporter_binary_sha256"] = digest(executable)
        export_search = ":".join(os.path.relpath(p / ".lake/build/lib/lean", exporter) for p in paths.values())
        # No declaration selection: the target remains the entire Mathlib module.
        runner.run([executable, lock["module"]], exporter, "export full Mathlib module", args.export_timeout,
                   search=export_search, output=output, output_limit=lock["expected"]["size"] + 1048576)
        runner.report["sources_unchanged_after_export"] = source_hashes(lock) == original
        actual, matched = inspect_output(output, lock["expected"])
        runner.report.update(actual=actual, status="exact_match" if matched else "different_bytes")
        if matched:
            final = WORK / "exports/mathlib.ndjson"
            final.parent.mkdir(exist_ok=True)
            if final.exists():
                if not inspect_output(final, lock["expected"])[1]:
                    raise ValueError("existing final output differs; preserving it")
            else:
                output.replace(final)
            runner.report["final_output"] = str(final.relative_to(WORK))
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as exc:
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
        runner.report["finished_at"] = utc_now()
        runner.report["shared_manifest_at_finish_sha256"] = digest(ROOT / "arena/manifest.json")
        runner.save()
        write_json(WORK / "latest-build.json", {"report": str(runner.path.relative_to(WORK)), "status": runner.report["status"]})
    return 0 if runner.report["status"] == "exact_match" else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--execute-reviewed", action="store_true")
    parser.add_argument("--allow-cache-download", action="store_true")
    parser.add_argument("--cache-timeout", type=positive_seconds, default=600)
    parser.add_argument("--build-timeout", type=positive_seconds, default=600)
    parser.add_argument("--export-timeout", type=positive_seconds, default=300)
    parser.add_argument("--memory-mib", type=int, default=8192)
    parser.add_argument("--max-missing-modules", type=int, default=16)
    args = parser.parse_args()
    if not 0 < args.memory_mib <= 8192:
        parser.error("--memory-mib must be positive and at most 8192")
    if not 0 <= args.max_missing_modules <= 16:
        parser.error("--max-missing-modules must be between 0 and 16")
    if args.allow_cache_download and not args.execute_reviewed:
        parser.error("--allow-cache-download requires --execute-reviewed")
    lock = load_lock()
    if args.execute_reviewed:
        return execute(lock, args)
    print(json.dumps({"lock": lock, "limits": vars(args), "network_profile": CACHE_PROFILE,
                      "curl_policy": CURL_POLICY, "decompressor_jobs": 2}, indent=2))
    print("Read-only preflight; one attempt per invocation, no checker or manifest import.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, StopIteration, RuntimeError, subprocess.SubprocessError) as exc:
        print(f"Mathlib acquisition failed: {exc}", file=sys.stderr)
        sys.exit(1)
