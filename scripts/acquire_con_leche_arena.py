#!/usr/bin/env python3
"""Prepare pinned Con-Leche source/toolchain; never execute project build hooks."""

import argparse
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tarfile

from acquire_large_arena import PROFILE, verified_blob
from fetch_arena import verify_file
from test_arena import digest, utc_now, write_json

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "arena/large/con-leche"


def load_lock():
    lock = json.loads((WORK / "lock.json").read_text())
    provenance = json.loads((ROOT / "arena/provenance.lock.json").read_text())
    results = ROOT / "arena/downloads/results.json"
    verify_file(results, next(item for item in provenance["downloads"] if item["name"] == "results.json"))
    published = json.loads(results.read_text())
    if published["meta"]["git_revision"] != lock["arena_revision"]:
        raise ValueError("Arena revision differs from published results")
    case = next(item for item in published["tests"] if item["name"] == "con-leche")
    for key, expected in lock["expected"].items():
        if case[key] != expected:
            raise ValueError(f"published {key} mismatch")
    for key in ("lean_version", "lean_githash"):
        if case[key] != lock[key]:
            raise ValueError(f"published {key} mismatch")
    verified_blob(ROOT / "arena/upstream", lock["arena_revision"], lock["definition"],
                  lock["definition_sha256"])
    definitions = ROOT / "arena/definitions.json"
    if digest(definitions) != provenance["definitions_sha256"]:
        raise ValueError("definitions differ from provenance lock")
    definition = next(item for item in json.loads(definitions.read_text())["definitions"]
                      if item["path"] == lock["definition"])
    config = definition["configuration"]
    if (config["rev"] != lock["source_revision"] or config["module"] != lock["module"]
            or config["export-decls"] != lock["export_declarations"]
            or config.get("pre-build") or config["outcome"] != "accept"):
        raise ValueError("recipe differs or requests an unreviewed pre-build hook")
    return lock


def prepare(lock, download):
    downloads = WORK / "downloads"
    downloads.mkdir(exist_ok=True)
    report = {"started_at": utc_now(), "script_sha256": digest(Path(__file__)),
              "lock_sha256": digest(WORK / "lock.json"), "artifacts": []}
    for kind in ("source", "toolchain"):
        pin = lock[kind]
        archive = downloads / pin["filename"]
        if not archive.exists():
            if not download:
                raise ValueError(f"missing {archive}; use --download to fetch pinned bytes")
            temporary = archive.with_suffix(archive.suffix + ".partial")
            command = ["/usr/bin/curl", "--fail", "--silent", "--show-error", "--location",
                       "--proto", "=https", "--proto-redir", "=https", "--max-time", "600",
                       "--max-filesize", str(pin["size"]), "--output", str(temporary), pin["url"]]
            subprocess.run(command, check=True, timeout=610)
            verify_file(temporary, pin)
            temporary.replace(archive)
        verify_file(archive, pin)
        destination = WORK / kind
        marker = destination / "prepared.json"
        if destination.exists():
            if not marker.exists() or json.loads(marker.read_text())["archive_sha256"] != pin["sha256"]:
                raise ValueError(f"unrecognized/incomplete destination; preserve for inspection: {destination}")
        else:
            destination.mkdir()
            if kind == "source":
                with tarfile.open(archive, "r:gz") as tar:
                    for member in tar.getmembers():
                        path = PurePosixPath(member.name)
                        if (path.is_absolute() or ".." in path.parts or not path.parts
                                or path.parts[0] != pin["directory"] or "\\" in member.name
                                or not (member.isfile() or member.isdir())):
                            raise ValueError(f"unexpected source archive member: {member.name}")
                    tar.extractall(destination, filter="data")
            else:
                listing = subprocess.check_output(["/usr/bin/tar", "-tf", str(archive)], text=True, timeout=180)
                for name in listing.splitlines():
                    path = PurePosixPath(name)
                    if (path.is_absolute() or ".." in path.parts or not path.parts
                            or path.parts[0] != pin["directory"] or "\\" in name):
                        raise ValueError(f"unexpected toolchain archive path: {name}")
                subprocess.run(["/usr/bin/sandbox-exec", "-D", f"WORK={destination}", "-p", PROFILE,
                                "/usr/bin/tar", "-xf", str(archive), "-C", str(destination),
                                "--no-same-owner", "--no-same-permissions"], check=True, timeout=180)
            write_json(marker, {"archive_sha256": pin["sha256"], "prepared_at": utc_now()})
        report["artifacts"].append({"kind": kind, **pin, "archive": str(archive),
                                    "directory": str(destination / pin["directory"])})
    report["finished_at"] = utc_now()
    write_json(WORK / "preparation-report.json", report)
    print(json.dumps(report, indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare", action="store_true")
    parser.add_argument("--download", action="store_true")
    args = parser.parse_args()
    lock = load_lock()
    if args.download and not args.prepare:
        parser.error("--download requires --prepare")
    if args.prepare:
        prepare(lock, args.download)
    else:
        print(json.dumps(lock, indent=2))
        print("Read-only preflight complete; preparation requires --prepare.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, StopIteration, subprocess.SubprocessError) as exc:
        print(f"Con-Leche preparation failed: {exc}", file=sys.stderr)
        sys.exit(1)
