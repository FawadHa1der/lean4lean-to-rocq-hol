#!/usr/bin/env python3
"""Prepare only the Arena-pinned Mathlib 4.34.1 sources; never execute build hooks."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile

from acquire_cedar_arena import members
from acquire_large_arena import verified_blob
from fetch_arena import verify_file
from test_arena import digest, utc_now, write_json

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "arena/large/mathlib"


def load_lock():
    lock = json.loads((WORK / "lock.json").read_text())
    dependency_lock = ROOT / lock["dependency_pins"]["lock"]
    if digest(dependency_lock) != lock["dependency_pins"]["lock_sha256"]:
        raise ValueError("reused dependency pin file differs")
    dependencies = json.loads(dependency_lock.read_text())["sources"]
    lock["sources"] = {"mathlib": lock["source"], **{
        name: dependencies[name] for name in lock["dependency_pins"]["names"]}}
    provenance = json.loads((ROOT / "arena/provenance.lock.json").read_text())
    results_path = ROOT / "arena/downloads/results.json"
    verify_file(results_path, next(p for p in provenance["downloads"] if p["name"] == "results.json"))
    results = json.loads(results_path.read_text())
    if results["meta"]["git_revision"] != lock["arena_revision"]:
        raise ValueError("Arena revision differs")
    case = next(p for p in results["tests"] if p["name"] == "mathlib")
    for key, value in {**lock["expected"], "lean_version": lock["lean_version"],
                       "lean_githash": lock["lean_githash"], "outcome": "accept"}.items():
        if case[key] != value:
            raise ValueError(f"published target differs: {key}")
    verified_blob(ROOT / "arena/upstream", lock["arena_revision"], lock["definition"], lock["definition_sha256"])
    definitions = ROOT / "arena/definitions.json"
    if digest(definitions) != provenance["definitions_sha256"]:
        raise ValueError("definitions differ")
    config = next(p for p in json.loads(definitions.read_text())["definitions"]
                  if p["path"] == lock["definition"])["configuration"]
    if (config["rev"] != lock["source"]["revision"] or config["module"] != lock["module"]
            or config.get("export-decls") or config["pre-build"].strip() != lock["pre_build"]):
        raise ValueError("recipe differs")
    generation = json.loads((ROOT / "arena/generation.lock.json").read_text())
    for key in ("arena_revision", "lean_version", "lean_githash", "exporter_revision"):
        if generation[key] != lock[key]:
            raise ValueError(f"reused generation pin differs: {key}")
    return lock


def source_paths(lock):
    return {name: WORK / "sources" / name / pin["directory"] for name, pin in lock["sources"].items()}


def source_hashes(lock):
    paths, hashes = source_paths(lock), {}
    for name, pin in lock["sources"].items():
        archive = WORK / "downloads" / pin["filename"]
        verify_file(archive, pin)
        with tarfile.open(archive) as tar:
            for member in members(tar, pin):
                relative = Path(member.name).relative_to(pin["directory"])
                path = paths[name] / relative
                if member.isfile():
                    with tar.extractfile(member) as stream:
                        expected = hashlib.file_digest(stream, "sha256").hexdigest()
                    if path.is_symlink() or digest(path) != expected:
                        raise ValueError(f"source changed: {name}/{relative}")
                    hashes[f"{name}/{relative}"] = expected
                elif member.issym():
                    if not path.is_symlink() or os.readlink(path) != member.linkname:
                        raise ValueError(f"source link changed: {name}/{relative}")
                    hashes[f"{name}/{relative}"] = {"symlink": member.linkname}
    project = paths["mathlib"]
    if (project / "lean-toolchain").read_text().strip() != f"leanprover/lean4:v{lock['lean_version']}":
        raise ValueError("Mathlib toolchain differs")
    dependencies = {p["name"]: p for p in json.loads((project / "lake-manifest.json").read_text())["packages"]}
    if set(dependencies) != set(paths) - {"mathlib"}:
        raise ValueError("dependency set differs")
    for name, dep in dependencies.items():
        if dep["rev"] != lock["sources"][name]["revision"]:
            raise ValueError(f"dependency revision differs: {name}")
        expected_url = lock["sources"][name]["url"].replace("https://codeload.github.com/", "https://github.com/").split("/tar.gz/")[0]
        if dep["url"] != expected_url or dep["subDir"] is not None:
            raise ValueError(f"dependency source differs: {name}")
    for name, path in paths.items():
        manifest = path / "lake-manifest.json"
        if not manifest.exists():
            continue
        for dep in json.loads(manifest.read_text())["packages"]:
            expected = dependencies.get(dep["name"])
            if expected is None or any(dep[k] != expected[k] for k in ("url", "rev", "subDir")):
                raise ValueError(f"inconsistent transitive manifest: {name}/{dep['name']}")
    return hashes


def toolchain_check(lock):
    pin = lock["toolchain"]
    verify_file(ROOT / pin["archive"], pin)
    toolchain = ROOT / pin["path"]
    for name in ("lean", "lake"):
        if digest(toolchain / "bin" / name) != pin[f"{name}_binary_sha256"]:
            raise ValueError(f"reused toolchain binary differs: {name}")
    version = subprocess.check_output([str(toolchain / "bin/lean"), "--version"], text=True, timeout=30).strip()
    if lock["lean_version"] not in version or lock["lean_githash"] not in version:
        raise ValueError(f"reused toolchain version differs: {version}")
    return toolchain, version


def prepare(lock, download):
    if shutil.disk_usage(WORK).free < 64 * 1024**3:
        raise ValueError("at least 64 GiB free required")
    report = {"started_at": utc_now(), "lock_sha256": digest(WORK / "lock.json"), "artifacts": []}
    for name, pin in lock["sources"].items():
        archive = WORK / "downloads" / pin["filename"]
        archive.parent.mkdir(exist_ok=True)
        reused = ROOT / lock["dependency_pins"]["archive_directory"] / pin["filename"]
        if not archive.exists():
            temporary = archive.with_suffix(archive.suffix + ".partial")
            if name != "mathlib" and reused.exists():
                verify_file(reused, pin)
                shutil.copyfile(reused, temporary)
            else:
                if not download:
                    raise ValueError(f"missing {archive}; --prepare --download permits exact pinned retrieval")
                subprocess.run(["/usr/bin/curl", "--fail", "--silent", "--show-error", "--location",
                                "--proto", "=https", "--proto-redir", "=https", "--max-time", "120",
                                "--max-filesize", str(pin["size"]), "--output", str(temporary), pin["url"]],
                               check=True, timeout=130)
            verify_file(temporary, pin)
            temporary.replace(archive)
        verify_file(archive, pin)
        destination = WORK / "sources" / name
        marker = destination / "prepared.json"
        if marker.exists():
            if json.loads(marker.read_text())["archive_sha256"] != pin["sha256"]:
                raise ValueError(f"unrecognized extraction: {destination}")
        else:
            if destination.exists() and any(destination.iterdir()):
                raise ValueError(f"incomplete extraction preserved: {destination}")
            destination.mkdir(parents=True, exist_ok=True)
            with tarfile.open(archive) as tar:
                checked = list(members(tar, pin))
                tar.extractall(destination, members=checked, filter="data")
            write_json(marker, {"archive_sha256": pin["sha256"], "prepared_at": utc_now()})
        report["artifacts"].append({"name": name, **pin})
        print(f"Prepared pinned {name}", flush=True)
    report["source_files_verified"] = len(source_hashes(lock))
    toolchain, version = toolchain_check(lock)
    report.update(toolchain=str(toolchain), lean_version=version, finished_at=utc_now())
    write_json(WORK / "preparation-report.json", report)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare", action="store_true")
    parser.add_argument("--download", action="store_true")
    args = parser.parse_args()
    if args.download and not args.prepare:
        parser.error("--download requires --prepare")
    lock = load_lock()
    if args.prepare:
        prepare(lock, args.download)
    else:
        print(json.dumps(lock, indent=2))
        print("Read-only preflight. No build, cache, toolchain or shared-manifest changes.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, StopIteration, subprocess.SubprocessError) as exc:
        print(f"Mathlib preparation failed: {exc}", file=sys.stderr)
        sys.exit(1)
