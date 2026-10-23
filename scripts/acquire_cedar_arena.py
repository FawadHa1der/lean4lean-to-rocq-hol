#!/usr/bin/env python3
"""Prepare/build the exact Cedar Arena recipe locally without destructive hooks."""

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import posixpath
import shutil
import subprocess
import sys
import tarfile
import time

from acquire_large_arena import PROFILE, inspect_output, verified_blob
from build_con_leche_arena import group_rss_kib
from fetch_arena import verify_file
from test_arena import digest, positive_seconds, stop_group, utc_now, write_json

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "arena/large/cedar"
TOOLCHAIN = ROOT / "arena/generation/toolchain/lean-4.34.1-darwin_aarch64"


def load_lock():
    lock = json.loads((WORK / "lock.json").read_text())
    generation = json.loads((ROOT / "arena/generation.lock.json").read_text())
    for key in ("arena_revision", "exporter_revision", "lean_version", "lean_githash"):
        if lock[key] != generation[key]:
            raise ValueError(f"generation pin differs: {key}")
    provenance = json.loads((ROOT / "arena/provenance.lock.json").read_text())
    results_path = ROOT / "arena/downloads/results.json"
    verify_file(results_path, next(x for x in provenance["downloads"] if x["name"] == "results.json"))
    results = json.loads(results_path.read_text())
    if results["meta"]["git_revision"] != lock["arena_revision"]:
        raise ValueError("published Arena revision differs")
    case = next(x for x in results["tests"] if x["name"] == "cedar")
    for key, value in {**lock["expected"], "lean_version": lock["lean_version"],
                       "lean_githash": lock["lean_githash"], "outcome": "accept"}.items():
        if case[key] != value:
            raise ValueError(f"published target differs: {key}")
    verified_blob(ROOT / "arena/upstream", lock["arena_revision"], lock["definition"], lock["definition_sha256"])
    definitions = ROOT / "arena/definitions.json"
    if digest(definitions) != provenance["definitions_sha256"]:
        raise ValueError("definitions differ from provenance lock")
    config = next(x for x in json.loads(definitions.read_text())["definitions"]
                  if x["path"] == lock["definition"])["configuration"]
    if (config["module"] != lock["module"] or config.get("export-decls")
            or config["rev"] != lock["sources"]["cedar"]["revision"]
            or hashlib.sha256(config["pre-build"].encode()).hexdigest() != lock["reviewed_pre_build_sha256"]):
        raise ValueError("recipe differs from reviewed full-module recipe")
    return lock


def members(tar, pin):
    for member in tar:
        path = PurePosixPath(member.name)
        if (path.is_absolute() or ".." in path.parts or not path.parts
                or path.parts[0] != pin["directory"] or "\\" in member.name
                or not (member.isfile() or member.isdir() or member.issym())):
            raise ValueError(f"unsafe/unexpected source member: {member.name}")
        if member.issym():
            target = PurePosixPath(member.linkname)
            resolved = PurePosixPath(posixpath.normpath(str(path.parent / target)))
            if (target.is_absolute() or "\\" in member.linkname
                    or not resolved.parts or resolved.parts[0] != pin["directory"]):
                raise ValueError(f"escaping source symlink: {member.name}")
        yield member


def prepare(lock, download):
    report = {"started_at": utc_now(), "lock_sha256": digest(WORK / "lock.json"), "archives": []}
    for name, pin in lock["sources"].items():
        archive = WORK / "downloads" / pin["filename"]
        archive.parent.mkdir(exist_ok=True)
        if not archive.exists():
            if not download:
                raise ValueError(f"missing {archive}; use --prepare --download")
            temporary = archive.with_suffix(".partial")
            subprocess.run(["/usr/bin/curl", "--fail", "--silent", "--show-error", "--location",
                            "--proto", "=https", "--proto-redir", "=https", "--max-time", "180",
                            "--max-filesize", str(pin["size"]), "--output", str(temporary), pin["url"]],
                           check=True, timeout=190)
            verify_file(temporary, pin)
            temporary.replace(archive)
        verify_file(archive, pin)
        destination = WORK / "sources" / name
        marker = destination / "prepared.json"
        if marker.exists():
            if json.loads(marker.read_text())["archive_sha256"] != pin["sha256"]:
                raise ValueError(f"unrecognized/incomplete extraction preserved: {destination}")
        else:
            if destination.exists() and any(destination.iterdir()):
                raise ValueError(f"unrecognized/incomplete extraction preserved: {destination}")
            destination.mkdir(parents=True, exist_ok=True)
            with tarfile.open(archive, "r:gz") as tar:
                checked = list(members(tar, pin))
                tar.extractall(destination, members=checked, filter="data")
            write_json(marker, {"archive_sha256": pin["sha256"], "prepared_at": utc_now()})
        report["archives"].append({"name": name, **pin})
    report["finished_at"] = utc_now()
    write_json(WORK / "preparation-report.json", report)
    print("Pinned Cedar and Batteries archives prepared; no upstream code executed.")


def source_paths(lock):
    return {name: WORK / "sources" / name / pin["directory"] for name, pin in lock["sources"].items()}


def source_hashes(lock):
    hashes = {}
    for name, pin in lock["sources"].items():
        archive = WORK / "downloads" / pin["filename"]
        verify_file(archive, pin)
        with tarfile.open(archive, "r:gz") as tar:
            for member in members(tar, pin):
                relative = Path(member.name).relative_to(pin["directory"])
                if member.isfile():
                    with tar.extractfile(member) as stream:
                        expected = hashlib.file_digest(stream, "sha256").hexdigest()
                    if digest(source_paths(lock)[name] / relative) != expected:
                        raise ValueError(f"source changed: {name}/{relative}")
                    hashes[f"{name}/{relative}"] = expected
                elif member.issym():
                    path = source_paths(lock)[name] / relative
                    if not path.is_symlink() or os.readlink(path) != member.linkname:
                        raise ValueError(f"source symlink changed: {name}/{relative}")
                    hashes[f"{name}/{relative}"] = {"symlink": member.linkname}
    sources = source_paths(lock)
    project = sources["cedar"] / lock["source_subdirectory"]
    manifest = json.loads((project / "lake-manifest.json").read_text())
    battery = next(x for x in manifest["packages"] if x["name"] == "batteries")
    if battery["rev"] != lock["sources"]["batteries"]["revision"]:
        raise ValueError("Batteries revision differs from Cedar manifest")
    if json.loads((sources["batteries"] / "lake-manifest.json").read_text())["packages"]:
        raise ValueError("unreviewed transitive Batteries dependencies")
    if (project / "lean-toolchain").read_text().strip() != f"leanprover/lean4:v{lock['lean_version']}":
        raise ValueError("Cedar Lean version differs")
    return hashes


def build(lock, args):
    if shutil.disk_usage(WORK).free < 16 * 1024**3:
        raise ValueError("fewer than 16 GiB free for bounded acquisition")
    original = source_hashes(lock)
    sources = source_paths(lock)
    project = sources["cedar"] / lock["source_subdirectory"]
    lean, lake = TOOLCHAIN / "bin/lean", TOOLCHAIN / "bin/lake"
    for path, key in ((lean, "lean_binary_sha256"), (lake, "lake_binary_sha256")):
        if digest(path) != lock[key]:
            raise ValueError(f"local toolchain binary differs: {path.name}")
    version = subprocess.check_output([str(lean), "--version"], text=True, timeout=30).strip()
    if lock["lean_version"] not in version or lock["lean_githash"] not in version:
        raise ValueError(f"wrong toolchain: {version}")
    directory = WORK / "runs" / f"{time.time_ns()}-{os.getpid()}"
    for part in ("home", "tmp", "logs", "exporter"):
        (directory / part).mkdir(parents=True)
    overrides = directory / "packages.json"
    write_json(overrides, {"schemaVersion": "1.2.0", "packages": [
        {"name": "batteries", "scope": "leanprover-community", "type": "path",
         "dir": str(sources["batteries"]), "inherited": False,
         "configFile": "lakefile.toml", "manifestFile": "lake-manifest.json"}]})
    report_path = directory / "report.json"
    report = {"started_at": utc_now(), "finished_at": None, "status": "running", "lock": lock,
              "lean_version": version, "source_hashes": original, "script_sha256": digest(Path(__file__)),
              "package_overrides_sha256": digest(overrides), "sandbox_profile": PROFILE,
              "memory_mib_sampled_limit": args.memory_mib, "exporter_mode": args.exporter_mode, "steps": []}

    def run(command, cwd, label, timeout, search=".", output=None, max_bytes=None):
        index = len(report["steps"])
        stdout = output or directory / "logs" / f"{index:03d}.stdout"
        stderr = directory / "logs" / f"{index:03d}.stderr"
        env = {"HOME": str(directory / "home"), "TMPDIR": str(directory / "tmp"),
               "PATH": f"{os.path.relpath(lean.parent, cwd)}:/usr/bin:/bin", "LEAN_PATH": search,
               "LEAN_ABORT_ON_PANIC": "1", "LEAN_NUM_THREADS": "2"}
        command = list(map(str, command))
        step = {"label": label, "command": command, "cwd": str(cwd), "environment": env,
                "timeout_seconds": timeout, "status": "running", "started_at": utc_now(),
                "stdout": str(stdout.relative_to(WORK)), "stderr": str(stderr.relative_to(WORK))}
        report["steps"].append(step)
        write_json(report_path, report)
        wrapped = ["/usr/bin/sandbox-exec", "-D", f"WORK={WORK}", "-p", PROFILE, *command]
        start, peak, reason = time.monotonic(), 0, None
        with stdout.open("wb") as out, stderr.open("wb") as err:
            proc = subprocess.Popen(wrapped, cwd=cwd, env=env, stdout=out, stderr=err, start_new_session=True)
            try:
                while proc.poll() is None:
                    peak = max(peak, group_rss_kib(proc.pid))
                    if time.monotonic() - start >= timeout:
                        reason = "wall_timeout"
                    elif peak > args.memory_mib * 1024:
                        reason = "sampled_memory_limit"
                    elif max_bytes is not None and stdout.stat().st_size > max_bytes:
                        reason = "output_size_limit"
                    if reason:
                        break
                    time.sleep(0.5)
            finally:
                stop_group(proc)
        step.update(status="complete", exit_code=proc.returncode, stop_reason=reason,
                    elapsed_seconds=round(time.monotonic() - start, 3), sampled_peak_rss_kib=peak)
        write_json(report_path, report)
        print(f"{label}: exit={proc.returncode} stop={reason} seconds={step['elapsed_seconds']}", flush=True)
        if reason or proc.returncode:
            raise RuntimeError(f"{label} failed; inspect {report_path}")

    try:
        run(["/usr/bin/true"], project, "sandbox probe", 10)
        exporter = directory / "exporter"
        exporter_files = ["Export.lean", "Main.lean", "LICENSE"]
        if args.exporter_mode == "native":
            exporter_files.extend(["lakefile.toml", "lake-manifest.json"])
        for filename in exporter_files:
            (exporter / filename).write_bytes(verified_blob(
                ROOT / "arena/exporter-source", lock["exporter_revision"], filename))
        report["exporter_source_hashes"] = {name: digest(exporter / name)
                                           for name in exporter_files}
        if args.exporter_mode == "native":
            run([lake, "--no-cache", "--no-ansi", "build", "lean4export"], exporter,
                "compile pinned native exporter", 180)
            executable = exporter / ".lake/build/bin/lean4export"
            report["exporter_binary_sha256"] = digest(executable)
            export_command = [executable, lock["module"]]
        else:
            run([lean, "-o", "Export.olean", "Export.lean"], exporter, "compile pinned exporter", 120)
            export_command = [lean, "--run", "Main.lean", lock["module"]]
        run([lake, "--no-cache", "--no-ansi", "--packages", overrides, "build", lock["module"]],
            project, "build Cedar with pinned local Batteries", args.build_timeout)
        report["sources_unchanged_after_build"] = source_hashes(lock) == original
        search = ":".join([".", *[os.path.relpath(path / ".lake/build/lib/lean", exporter)
                                  for path in (project, sources["batteries"])]])
        output = directory / "cedar.partial.ndjson"
        # Omit '--' to export the entire requested module, exactly as the recipe specifies.
        run(export_command, exporter, "export full Cedar module",
            args.export_timeout, search, output, lock["expected"]["size"])
        report["sources_unchanged_after_export"] = source_hashes(lock) == original
        actual, matched = inspect_output(output, lock["expected"])
        report.update(actual=actual, status="exact_match" if matched else "different_bytes")
        if matched:
            final = WORK / "exports/cedar.ndjson"
            final.parent.mkdir(exist_ok=True)
            if final.exists():
                if not inspect_output(final, lock["expected"])[1]:
                    raise ValueError("existing final export differs; refusing overwrite")
            else:
                output.replace(final)
            report["final_output"] = str(final.relative_to(WORK))
            write_json(WORK / "manifest.json", {"manifest_version": 1, "provenance": {"cedar_lock": lock},
                "cases": [{"id": "cedar", "expected": "accept", "availability": "available",
                           "source_kind": "module_export", "origin": "generated_local",
                           "path": str(final.relative_to(WORK)), "timeout_seconds": 940, **lock["expected"]}]})
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as exc:
        report.update(status="failed", error=str(exc))
        raise
    finally:
        report["finished_at"] = utc_now()
        write_json(report_path, report)
        write_json(WORK / "latest-build.json", {"report": str(report_path.relative_to(WORK)), "status": report["status"]})
        print(f"Cedar report: {report_path}", flush=True)
    return 0 if report["status"] == "exact_match" else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare", action="store_true")
    parser.add_argument("--download", action="store_true")
    parser.add_argument("--execute-reviewed", action="store_true")
    parser.add_argument("--build-timeout", type=positive_seconds, default=900)
    parser.add_argument("--export-timeout", type=positive_seconds, default=300)
    parser.add_argument("--memory-mib", type=int, default=8192)
    parser.add_argument("--exporter-mode", choices=("native", "interpreted"), default="native")
    args = parser.parse_args()
    if args.download and not args.prepare:
        parser.error("--download requires --prepare")
    if args.memory_mib <= 0:
        parser.error("--memory-mib must be positive")
    lock = load_lock()
    if args.prepare:
        prepare(lock, args.download)
    if args.execute_reviewed:
        return build(lock, args)
    if not args.prepare:
        print(json.dumps(lock, indent=2))
        print("Read-only preflight; use --prepare, review source, then --execute-reviewed.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, StopIteration, RuntimeError, subprocess.SubprocessError) as exc:
        print(f"Cedar acquisition failed: {exc}", file=sys.stderr)
        sys.exit(1)
