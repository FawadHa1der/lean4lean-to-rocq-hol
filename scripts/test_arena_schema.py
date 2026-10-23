#!/usr/bin/env python3
# Copyright (c) 2026 Fawad Haider. All rights reserved.
"""Audit observed NDJSON structure without attempting to decide proof validity."""

import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path
import sys

from test_arena import DEFAULT_MANIFEST, digest, load_manifest, write_json


def audit(manifest_path):
    manifest = load_manifest(manifest_path)
    record_counts = Counter()
    nested_counts = Counter()
    fields = defaultdict(Counter)
    format_versions = Counter()
    exporter_versions = Counter()
    lean_versions = Counter()
    reflexivity = Counter()
    zero_definitions = Counter()
    observations = defaultdict(list)
    observation_counts = Counter()
    scanned = []
    failures = []
    total_lines = 0
    total_bytes = 0

    def note(kind, case, line, detail=None):
        observation_counts[kind] += 1
        if len(observations[kind]) < 8:
            observations[kind].append({"case": case, "line": line, "detail": detail})

    for case in manifest["cases"]:
        if case["availability"] != "available":
            continue
        path = manifest_path.parent / case["path"]
        if path.stat().st_size != case["size"] or digest(path) != case["sha256"]:
            failures.append({"case": case["id"], "error": "integrity mismatch"})
            continue
        scanned.append(case["id"])
        total_bytes += path.stat().st_size
        # Name.anonymous and Level.zero are implicit; expression 0 is not implicit.
        indices = {"in": {0}, "il": {0}, "ie": set()}
        greatest_index = {"in": 0, "il": 0, "ie": -1}
        with path.open("rb") as stream:
            for line_number, raw in enumerate(stream, 1):
                total_lines += 1
                if not raw.strip():
                    note("blank_lines", case["id"], line_number)
                    continue
                try:
                    record = json.loads(raw)
                except (ValueError, UnicodeError) as exc:
                    failures.append({"case": case["id"], "line": line_number, "error": str(exc)})
                    continue
                if not isinstance(record, dict):
                    note("nonobject_record", case["id"], line_number)
                    continue
                if "meta" in record:
                    meta = record["meta"]
                    format_versions[meta.get("format", {}).get("version", "missing")] += 1
                    exporter = meta.get("exporter", {})
                    exporter_versions[f"{exporter.get('name')}:{exporter.get('version')}"] += 1
                    lean_versions[meta.get("lean", {}).get("version", "missing")] += 1
                    if line_number != 1:
                        note("late_metadata", case["id"], line_number)
                for key in indices:
                    if key not in record:
                        continue
                    index = record[key]
                    if index == 0:
                        zero_definitions[key] += 1
                    if index in indices[key]:
                        note("duplicate_index", case["id"], line_number, {key: index})
                    if index != greatest_index[key] + 1:
                        note("nonconsecutive_index", case["id"], line_number, {key: index})
                    indices[key].add(index)
                    greatest_index[key] = max(greatest_index[key], index)
                for key, value in record.items():
                    if key in indices:
                        continue
                    record_counts[key] += 1
                    if isinstance(value, dict):
                        fields[key].update(value.keys())
                    if key in {"def", "thm", "opaque"} and "all" not in value:
                        note("missing_all", case["id"], line_number, key)
                    if key == "inductive":
                        for group, items in value.items():
                            for item in items:
                                nested_counts[group] += 1
                                fields[f"inductive.{group}"].update(item.keys())
                                if group in {"types", "recs"} and "all" not in item:
                                    note("missing_all", case["id"], line_number, f"inductive.{group}")
                                if group == "types":
                                    reflexivity[str(item.get("isReflexive", "missing")).lower()] += 1
                                    if "isReflexive" not in item:
                                        note("missing_isReflexive", case["id"], line_number)
                                if group == "recs":
                                    for rule in item.get("rules", []):
                                        nested_counts["rules"] += 1
                                        fields["inductive.recs.rules"].update(rule.keys())
                if record.get("str", {}).get("pre") == 0 or record.get("num", {}).get("pre") == 0:
                    note("implicit_name_zero_reference", case["id"], line_number)
                if record.get("sort") == 0 or record.get("succ") == 0:
                    note("implicit_level_zero_reference", case["id"], line_number)
    return {
        "audit_version": 1, "manifest_sha256": digest(manifest_path), "scanned_cases": len(scanned),
        "scanned_bytes": total_bytes, "scanned_lines": total_lines,
        "unavailable_cases": [case["id"] for case in manifest["cases"] if case["availability"] != "available"],
        "format_versions": dict(format_versions), "exporters": dict(exporter_versions),
        "lean_versions": dict(lean_versions), "record_counts": dict(record_counts),
        "nested_counts": dict(nested_counts), "field_counts": dict(fields),
        "isReflexive": dict(reflexivity), "explicit_index_zero": dict(zero_definitions),
        "observation_counts": dict(observation_counts), "examples": dict(observations), "errors": failures,
        "note": "Observational inventory, not a formal schema or checker verdict. Rejected proof inputs are included."
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--report", type=Path, default=DEFAULT_MANIFEST.parent / "schema-audit.json")
    args = parser.parse_args(argv)
    report = audit(args.manifest.resolve())
    write_json(args.report, report)
    print(json.dumps({key: report[key] for key in ("scanned_cases", "scanned_bytes", "scanned_lines", "format_versions", "isReflexive", "explicit_index_zero", "observation_counts", "errors")}, indent=2))
    return 1 if report["errors"] else 0


if __name__ == "__main__":
    sys.exit(main())
