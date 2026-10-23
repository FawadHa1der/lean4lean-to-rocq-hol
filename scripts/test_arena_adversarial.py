#!/usr/bin/env python3
# Copyright (c) 2026 Fawad Haider. All rights reserved.
"""Generate semantic adversarial cases and filename-neutral metamorphic Arena inputs."""

import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile

from test_arena import DEFAULT_MANIFEST, digest, load_manifest, relative_path, write_json


def encode(records):
    return b"".join((json.dumps(record, separators=(",", ":"), sort_keys=True) + "\n").encode() for record in records)


def semantic_cases(baseline):
    """Small kernel obligations, not malformed-wire parser tests."""
    control = copy.deepcopy(baseline)
    control[1]["str"]["str"] = "ArenaAdversarial"
    yield "universe-control", "accept", control, "Sort 0 inhabits Sort 1."
    bad = copy.deepcopy(control)
    bad[-1]["def"]["type"] = 1
    yield "universe-mismatch", "reject", bad, "Sort 0 does not inhabit itself."
    bad = copy.deepcopy(control)
    bad.insert(-1, {"bvar": 0, "ie": 2})
    bad[-1]["def"]["value"] = 2
    yield "unbound-variable", "reject", bad, "A closed declaration cannot use free de Bruijn index 0."
    bad = copy.deepcopy(control)
    bad.insert(-1, {"in": 2, "str": {"pre": 0, "str": "NotDeclared"}})
    bad.insert(-1, {"ie": 2, "const": {"name": 2, "us": []}})
    bad[-1]["def"]["value"] = 2
    yield "unknown-constant", "reject", bad, "A name-table entry is not an environment declaration."
    bad = copy.deepcopy(control)
    bad.insert(-1, {"ie": 2, "const": {"name": 1, "us": []}})
    bad[-1]["def"]["value"] = 2
    yield "self-reference", "reject", bad, "A safe definition may not assume itself before checking its body."
    bad = copy.deepcopy(control)
    theorem = bad[-1].pop("def")
    theorem.pop("hints")
    theorem.pop("safety")
    bad[-1]["thm"] = theorem
    yield "non-proposition-theorem", "reject", bad, "A theorem must prove a proposition, not a universe."
    bad = copy.deepcopy(control)
    second = copy.deepcopy(control[-1])
    second["def"].update(name=2, all=[2], type=1)
    bad.extend([{"in": 2, "str": {"pre": 0, "str": "Second"}}, second])
    yield "valid-prefix-invalid-tail", "reject", bad, "A valid first declaration must not hide a later bad declaration."


def generate(manifest_path, destination):
    manifest_checksum = digest(manifest_path)
    manifest = load_manifest(manifest_path)
    cases = []

    def put(name, expected, records, origin, reason, parent=None, timeout=None):
        # Content-derived paths carry no good/bad classification or expected verdict.
        directory = relative_path(destination, "inputs")
        directory.mkdir(parents=True, exist_ok=True)
        checksum = hashlib.sha256()
        size = 0
        temporary = None
        try:
            with tempfile.NamedTemporaryFile(dir=directory, prefix=".canonical-", delete=False) as stream:
                temporary = Path(stream.name)
                for record in records:
                    payload = (json.dumps(record, separators=(",", ":"), sort_keys=True) + "\n").encode()
                    stream.write(payload)
                    checksum.update(payload)
                    size += len(payload)
            checksum = checksum.hexdigest()
            relative = f"inputs/{checksum}.ndjson"
            temporary.replace(relative_path(destination, relative))
        finally:
            if temporary is not None:
                temporary.unlink(missing_ok=True)
        case = {"id": name, "expected": expected, "availability": "available", "path": relative,
                "size": size, "sha256": checksum, "source_kind": "generated_local",
                "origin": origin, "description": reason, "parent": parent, "format_version": "3.1.0"}
        if timeout is not None:
            case["timeout_seconds"] = timeout
        cases.append(case)

    def source_records(path, case, capture):
        checksum = hashlib.sha256()
        size = 0
        with path.open("rb") as stream:
            for line in stream:
                checksum.update(line)
                size += len(line)
                if line.strip():
                    record = json.loads(line)
                    if capture is not None:
                        capture.append(record)
                    yield record
        if size != case["size"] or checksum.hexdigest() != case["sha256"]:
            raise ValueError(f"input size/checksum changed: {case['id']}")

    baseline = None
    for case in manifest["cases"]:
        if case["availability"] != "available":
            continue
        path = relative_path(manifest_path.parent, case["path"])
        capture = [] if case["id"] == "tutorial/001_basicDef" else None
        put(f"metamorphic/{case['id']}", case["expected"], source_records(path, case, capture), "canonical-json-and-neutral-filename",
            "Same JSON values and record order as the pinned source case; no logical transformation.",
            {"id": case["id"], "sha256": case["sha256"]}, case.get("timeout_seconds"))
        if case["id"] == "tutorial/001_basicDef":
            baseline = capture
    if baseline is None:
        raise ValueError("semantic generation needs the pinned tutorial/001_basicDef control")
    for name, expected, records, reason in semantic_cases(baseline):
        put(f"adversarial/{name}", expected, records, "local-semantic-mutation", reason,
            {"id": "tutorial/001_basicDef"})
    if digest(manifest_path) != manifest_checksum:
        raise ValueError("parent manifest changed during generation")
    result = {"manifest_version": 1, "provenance": {
        "parent_manifest_sha256": manifest_checksum, "generator": "scripts/test_arena_adversarial.py",
        "generator_sha256": digest(Path(__file__)),
        "note": "Local generated tests, not additional published Arena cases. Semantic verdicts are specified by the obligations in descriptions; not oracle-confirmed."
    }, "cases": cases}
    write_json(destination / "manifest.json", result)
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--output", type=Path, default=DEFAULT_MANIFEST.parent / "adversarial")
    args = parser.parse_args(argv)
    result = generate(args.manifest.resolve(), args.output.resolve())
    print(f"Generated {len(result['cases'])} separately attributed cases in {args.output}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
