#!/usr/bin/env python3
# Copyright (c) 2026 Fawad Haider. All rights reserved.
"""Verify/import pinned Arena data. Never execute upstream build or generator code."""

import argparse
from collections import Counter
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tarfile
import tempfile
import urllib.request

from test_arena import digest, relative_path, write_json


ROOT = Path(__file__).resolve().parents[1] / "arena"


def verified_copy(stream, target, expected):
    target.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(dir=target.parent, delete=False) as out:
            temporary = Path(out.name)
            h = hashlib.sha256()
            size = 0
            while chunk := stream.read(1024 * 1024):
                size += len(chunk)
                if size > expected["size"]:
                    raise ValueError(f"{target.name}: exceeds pinned size")
                h.update(chunk)
                out.write(chunk)
            if size != expected["size"] or h.hexdigest() != expected["sha256"]:
                raise ValueError(f"{target.name}: size/SHA-256 mismatch")
        temporary.replace(target)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def verify_file(path, expected):
    if path.stat().st_size != expected["size"] or digest(path) != expected["sha256"]:
        raise ValueError(f"{path}: differs from pinned size/SHA-256")


def git(source, *args):
    return subprocess.check_output(["git", "-C", str(source), *args])


def clone_source(root, lock):
    source = root / "upstream"
    if not source.exists():
        subprocess.run(["git", "clone", "--no-checkout", "--depth", "1", lock["upstream"]["url"], str(source)], check=True)
    remote = git(source, "remote", "get-url", "origin").decode().strip()
    if remote != lock["upstream"]["url"]:
        raise ValueError("existing upstream has a different origin; refusing to modify it")
    for revision in (lock["upstream"]["source_head"], lock["upstream"]["published_revision"]):
        subprocess.run(["git", "-C", str(source), "fetch", "--depth", "1", "origin", revision], check=True)
    # No checkout/reset: an existing checkout may have another worker's changes.
    print("Source commits fetched; manifest construction reads exact blobs with git show.")


def extract_archive(archive, root, tests):
    imported = {}
    with tarfile.open(archive, "r:gz") as tar:
        for member in tar:
            path = PurePosixPath(member.name)
            if (not member.isfile() or path.is_absolute() or ".." in path.parts
                    or "\\" in member.name or len(path.parts) < 2
                    or path.parts[0] not in {"good", "bad"} or path.suffix != ".ndjson"):
                raise ValueError(f"unsafe/unexpected archive member: {member.name}")
            name = str(PurePosixPath(*path.parts[1:]))[:-len(".ndjson")]
            if name in imported or name not in tests:
                raise ValueError(f"duplicate/unknown archive case: {name}")
            test = tests[name]
            expected = "accept" if path.parts[0] == "good" else "reject"
            if test["outcome"] != expected or member.size != test["size"]:
                raise ValueError(f"archive metadata differs from published inventory: {name}")
            target = relative_path(root, f"corpus/{name}.ndjson")
            with tar.extractfile(member) as stream:
                verified_copy(stream, target, test)
            imported[name] = {"origin": "published_tarball", "archive_member": member.name}
    return imported


def input_stats(path):
    lines = 0
    with path.open("rb") as stream:
        first = stream.readline()
        if first:
            lines = 1 + sum(1 for _ in stream)
    meta = json.loads(first)["meta"]
    return {"lines": lines, "format_version": meta["format"]["version"], "header": meta}


def build_manifest(root, lock, generated):
    if digest(root / "definitions.json") != lock["definitions_sha256"]:
        raise ValueError("definitions.json differs from provenance lock")
    definitions = json.loads((root / "definitions.json").read_text())
    revision = lock["upstream"]["published_revision"]
    if definitions["source_revision"] != revision:
        raise ValueError("definitions revision differs from published revision")
    by_yaml = {item["path"]: item for item in definitions["definitions"]}
    source = root / "upstream"
    if source.exists():
        for item in by_yaml.values():
            raw = git(source, "show", f"{revision}:{item['path']}")
            if hashlib.sha256(raw).hexdigest() != item["sha256"]:
                raise ValueError(f"definition blob differs: {item['path']}")
    published = json.loads((root / "downloads/results.json").read_text())
    if published["meta"]["git_revision"] != revision:
        raise ValueError("published inventory revision differs from lock")
    tests = {test["name"]: test for test in published["tests"]}
    if len(tests) != len(published["tests"]):
        raise ValueError("duplicate published test ids")
    imported = extract_archive(root / "downloads/lean-arena-tests.tar.gz", root, tests)
    archive_count = len(imported)
    for name, test in tests.items():
        config = by_yaml[test["yaml_file"]]["configuration"]
        if name not in imported and config.get("file") and source.exists():
            raw = git(source, "show", f"{revision}:{config['file']}")
            target = relative_path(root, f"corpus/{name}.ndjson")
            verified_copy(io.BytesIO(raw), target, test)
            imported[name] = {"origin": "upstream_static", "source_path": config["file"]}
    for name, path in generated.items():
        if name not in tests:
            raise ValueError(f"unknown generated case: {name}")
        target = relative_path(root, f"corpus/{name}.ndjson")
        with path.open("rb") as stream:
            verified_copy(stream, target, tests[name])
        imported[name] = {"origin": "generated_local", "imported_from": str(path.resolve())}
    # Preserve previously imported exact-match generated files on offline reruns.
    previous = root / "manifest.json"
    previous_cases = {}
    if previous.exists():
        previous_cases = {case["id"]: case for case in json.loads(previous.read_text())["cases"]}
    for name, test in tests.items():
        old = previous_cases.get(name, {})
        if name not in imported and old.get("origin") == "generated_local":
            verify_file(relative_path(root, f"corpus/{name}.ndjson"), test)
            imported[name] = {"origin": "generated_local", "imported_from": old.get("imported_from")}
    cases = []
    for name, test in sorted(tests.items()):
        definition = by_yaml[test["yaml_file"]]
        config = definition["configuration"]
        kind = ("static" if "file" in config else "generated_multiple" if config.get("multiple")
                else "leanfile_export" if "leanfile" in config else "module_export" if "module" in config
                else "generated_command")
        case = {
            "id": name, "expected": test["outcome"], "path": f"corpus/{name}.ndjson",
            "availability": "available" if name in imported else "missing_download",
            "source_kind": kind, "definition": test["yaml_file"],
            "definition_sha256": definition["sha256"], "configuration": config,
            "size": test["size"], "sha256": test["sha256"], "lines": test["lines"],
            "lean_version": test.get("lean_version"), "lean_githash": test.get("lean_githash"),
            "exporter_version": test.get("lean4export_version"),
            "description": test.get("description", ""),
        }
        if test.get("timeout"):
            case["timeout_seconds"] = test["timeout"]
        if name in imported:
            case.update(imported[name])
            stats = input_stats(root / case["path"])
            if stats["lines"] != test["lines"]:
                raise ValueError(f"published line count differs for {name}")
            case.update(stats)
        else:
            case["origin"] = "published_inventory_only"
            case["missing_reason"] = ("published tarball excludes inputs larger than 10 MiB"
                                      if test["size"] > 10 * 1024 * 1024 else
                                      "published tarball excludes outcome=either; generator not run")
        cases.append(case)
    represented = {case["definition"] for case in cases}
    for path, definition in sorted(by_yaml.items()):
        if path not in represented:
            config = definition["configuration"]
            name = path.removeprefix("tests/").removesuffix(".yaml")
            cases.append({"id": name, "expected": config.get("outcome", "either"),
                          "path": f"corpus/{name}.ndjson", "availability": "missing_generated",
                          "source_kind": "source_only_definition", "definition": path,
                          "configuration": config, "missing_reason": "definition has no published cases; generator not run"})
    manifest = {
        "manifest_version": 1, "provenance": {**lock, "published_meta": published["meta"]},
        "summary": {
            "cases": len(cases), "definitions": len(by_yaml), "archive_cases": archive_count,
            "availability": dict(Counter(case["availability"] for case in cases)),
            "source_kinds": dict(Counter(case["source_kind"] for case in cases)),
            "expected": dict(Counter(case["expected"] for case in cases)),
            "available_bytes": sum(case["size"] for case in cases if case["availability"] == "available"),
            "published_bytes": sum(test["size"] for test in tests.values()),
        }, "cases": cases,
    }
    write_json(root / "manifest.json", manifest)
    print(json.dumps(manifest["summary"], indent=2))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--arena-dir", type=Path, default=ROOT)
    parser.add_argument("--download", action="store_true", help="fetch missing downloads, rejecting bytes that differ from lock")
    parser.add_argument("--source", action="store_true", help="fetch pinned source commits, without checkout/build")
    parser.add_argument("--import-generated", action="append", default=[], metavar="ID=PATH", help="import externally generated input only if its published checksum matches")
    args = parser.parse_args(argv)
    try:
        root = args.arena_dir.resolve()
        lock = json.loads((root / "provenance.lock.json").read_text())
        if lock["lock_version"] != 1:
            raise ValueError("unsupported provenance lock")
        if args.source:
            clone_source(root, lock)
        for item in lock["downloads"]:
            path = relative_path(root, f"downloads/{item['name']}")
            if not path.exists() and args.download:
                if not item["url"].startswith("https://"):
                    raise ValueError("downloads require HTTPS")
                with urllib.request.urlopen(item["url"], timeout=60) as stream:
                    if not stream.url.startswith("https://"):
                        raise ValueError("download redirected away from HTTPS")
                    verified_copy(stream, path, item)
            verify_file(path, item)
        generated = {}
        for spec in args.import_generated:
            name, separator, path = spec.partition("=")
            if not separator or not name or not path or name in generated:
                raise ValueError("--import-generated requires unique ID=PATH entries")
            generated[name] = Path(path)
        build_manifest(root, lock, generated)
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError, tarfile.TarError) as exc:
        print(f"Arena import failed: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
