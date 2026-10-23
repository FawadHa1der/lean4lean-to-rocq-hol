#!/usr/bin/env python3
"""Prepare exact CSLib source/dependencies/toolchain without executing build hooks."""

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tarfile

from acquire_cedar_arena import members
from acquire_large_arena import PROFILE, verified_blob
from fetch_arena import verify_file
from test_arena import digest, utc_now, write_json

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "arena/large/cslib"


def load_lock():
    lock = json.loads((WORK / "lock.json").read_text())
    provenance = json.loads((ROOT / "arena/provenance.lock.json").read_text())
    result = ROOT / "arena/downloads/results.json"
    verify_file(result, next(p for p in provenance["downloads"] if p["name"] == "results.json"))
    results = json.loads(result.read_text())
    if results["meta"]["git_revision"] != lock["arena_revision"]:
        raise ValueError("Arena revision differs")
    case = next(p for p in results["tests"] if p["name"] == "cslib")
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
    if (config["module"] != lock["module"] or config.get("export-decls")
            or config["rev"] != lock["sources"]["cslib"]["revision"]
            or config["pre-build"].strip() != lock["pre_build"]):
        raise ValueError("recipe differs")
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
    root = json.loads((paths["cslib"] / "lake-manifest.json").read_text())
    root_deps = {p["name"]: p for p in root["packages"]}
    if set(root_deps) != set(paths) - {"cslib"}:
        raise ValueError("dependency set differs")
    for name, path in paths.items():
        if name in ("mathlib", "cslib"):
            if (path / "lean-toolchain").read_text().strip() != f"leanprover/lean4:v{lock['lean_version']}":
                raise ValueError(f"toolchain differs: {name}")
        if name != "cslib" and root_deps[name]["rev"] != lock["sources"][name]["revision"]:
            raise ValueError(f"dependency pin differs: {name}")
        manifest = path / "lake-manifest.json"
        if not manifest.exists():
            continue
        for dep in json.loads(manifest.read_text())["packages"]:
            expected = root_deps.get(dep["name"])
            if expected is None or any(dep[k] != expected[k] for k in ("url", "rev", "subDir")):
                raise ValueError(f"inconsistent transitive manifest: {name}/{dep['name']}")
    return hashes


def prepare(lock, download, sources_only):
    if shutil.disk_usage(WORK).free < 32 * 1024**3:
        raise ValueError("at least 32 GiB free required")
    report = {"started_at": utc_now(), "lock_sha256": digest(WORK / "lock.json"), "artifacts": []}
    pins = [(name, pin, WORK / "sources" / name) for name, pin in lock["sources"].items()]
    if not sources_only:
        pins.append(("toolchain", lock["toolchain"], WORK / "toolchain"))
    for name, pin, destination in pins:
        archive = WORK / "downloads" / pin["filename"]
        archive.parent.mkdir(exist_ok=True)
        if not archive.exists():
            if not download:
                raise ValueError(f"missing {archive}; use --prepare --download")
            temporary = archive.with_suffix(archive.suffix + ".partial")
            subprocess.run(["/usr/bin/curl", "--fail", "--silent", "--show-error", "--location",
                            "--proto", "=https", "--proto-redir", "=https", "--max-time", "600",
                            "--max-filesize", str(pin["size"]), "--output", str(temporary), pin["url"]],
                           check=True, timeout=610)
            verify_file(temporary, pin)
            temporary.replace(archive)
        verify_file(archive, pin)
        marker = destination / "prepared.json"
        if marker.exists():
            if json.loads(marker.read_text())["archive_sha256"] != pin["sha256"]:
                raise ValueError(f"unrecognized extraction: {destination}")
        else:
            if destination.exists() and any(destination.iterdir()):
                raise ValueError(f"incomplete extraction preserved: {destination}")
            destination.mkdir(parents=True, exist_ok=True)
            if name != "toolchain":
                with tarfile.open(archive) as tar:
                    checked = list(members(tar, pin))
                    tar.extractall(destination, members=checked, filter="data")
            else:
                listing = subprocess.check_output(["/usr/bin/tar", "-tf", str(archive)], text=True, timeout=180)
                for item in listing.splitlines():
                    path = PurePosixPath(item)
                    if (path.is_absolute() or ".." in path.parts or not path.parts
                            or path.parts[0] != pin["directory"] or "\\" in item):
                        raise ValueError(f"unexpected toolchain archive member: {item}")
                subprocess.run(["/usr/bin/sandbox-exec", "-D", f"WORK={destination}", "-p", PROFILE,
                                "/usr/bin/tar", "-xf", str(archive), "-C", str(destination),
                                "--no-same-owner", "--no-same-permissions"], check=True, timeout=180)
            write_json(marker, {"archive_sha256": pin["sha256"], "prepared_at": utc_now()})
        report["artifacts"].append({"name": name, **pin})
        print(f"Prepared pinned {name}", flush=True)
    report["source_files_verified"] = len(source_hashes(lock))
    report["finished_at"] = utc_now()
    write_json(WORK / "preparation-report.json", report)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare", action="store_true")
    parser.add_argument("--download", action="store_true")
    parser.add_argument("--sources-only", action="store_true")
    args = parser.parse_args()
    if (args.download or args.sources_only) and not args.prepare:
        parser.error("--download and --sources-only require --prepare")
    lock = load_lock()
    if args.prepare:
        prepare(lock, args.download, args.sources_only)
    else:
        print(json.dumps(lock, indent=2))
        print("Read-only preflight. --prepare never executes upstream project hooks.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, StopIteration, subprocess.SubprocessError) as exc:
        print(f"CSLib preparation failed: {exc}", file=sys.stderr)
        sys.exit(1)
