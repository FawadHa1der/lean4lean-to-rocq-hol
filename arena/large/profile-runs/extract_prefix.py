#!/usr/bin/env python3
"""Extract an unchanged NDJSON prefix and audit its transport dependency closure.

This is diagnostic input analysis, not a parser replacement or logical checker.
No declaration, expression, table index, or metadata field is rewritten.
"""

import argparse
import hashlib
import json
from pathlib import Path


DECLARATIONS = {"axiom", "def", "thm", "opaque", "quot", "inductive"}


def dotted(value):
    return tuple(("str", part) for part in value.split("."))


def display(name):
    return ".".join(str(value) if tag == "str" else f"[{value}]"
                    for tag, value in name) or "<anonymous>"


def analyze(raw_lines, progress):
    names = {0: ()}
    exprs = {}
    rows = []
    metadata = None
    for line, raw in enumerate(raw_lines, 1):
        record = json.loads(raw)
        tag, = [key for key in record if key not in {"in", "il", "ie"}]
        value = record[tag]
        if tag == "meta":
            metadata = value
        elif tag in ("str", "num"):
            part = value["str"] if tag == "str" else value["i"]
            names[record["in"]] = names[value["pre"]] + ((tag, part),)
        elif "ie" in record:
            children = []
            dependencies = []
            if tag == "const":
                dependencies = [names[value["name"]]]
            elif tag == "app":
                children = [value["fn"], value["arg"]]
            elif tag in ("lam", "forallE"):
                children = [value["type"], value["body"]]
            elif tag == "letE":
                children = [value["type"], value["value"], value["body"]]
            elif tag == "proj":
                children = [value["struct"]]
                dependencies = [names[value["typeName"]]]
            elif tag == "mdata":
                children = [value["expr"]]
            elif tag == "natVal":
                dependencies = list(map(dotted, ("Nat", "Nat.zero", "Nat.succ")))
            elif tag == "strVal":
                dependencies = list(map(dotted, ("String", "Char", "Char.ofNat",
                                                "String.ofList", "List", "List.nil", "List.cons")))
            elif tag not in ("bvar", "sort"):
                raise ValueError(f"unsupported diagnostic expression tag {tag}")
            if any(child not in exprs for child in children):
                raise ValueError(f"forward expression reference at line {line}")
            if record["ie"] in exprs:
                raise ValueError(f"duplicate expression at line {line}")
            exprs[record["ie"]] = (children, dependencies)
        elif tag in DECLARATIONS:
            headers = ([*value["types"], *value["ctors"], *value["recs"]]
                       if tag == "inductive" else [value])
            owned = [names[header["name"]] for header in headers]
            roots = [header["type"] for header in headers]
            if tag in ("def", "thm", "opaque"):
                roots.append(value["value"])
            if tag == "inductive":
                roots.extend(rule["rhs"] for rec in value["recs"] for rule in rec["rules"])
            references = []
            for header in headers:
                references.extend(names[name] for name in header.get("all", []))
                references.extend(names[name] for name in header.get("ctors", []))
                if "induct" in header:
                    references.append(names[header["induct"]])
                references.extend(names[rule["ctor"]] for rule in header.get("rules", []))
            rows.append({"line": line, "tag": tag, "owned": owned, "roots": roots,
                         "all": [names[name] for name in value.get("all", [])],
                         "metadata_references": references,
                         "safety": value.get("safety"), "wire_record": record})
        elif "il" not in record:
            raise ValueError(f"unsupported diagnostic record at line {line}: {tag}")
    if not rows or rows[-1]["line"] != len(raw_lines):
        raise ValueError("prefix must end exactly on a declaration record")
    index = {}
    for i, row in enumerate(rows):
        for name in row["owned"]:
            if name in index:
                raise ValueError(f"duplicate declaration {display(name)}")
            index[name] = i
    owner = {}
    batches = []
    problems = []
    for i, row in enumerate(rows):
        if i in owner:
            continue
        mutual = row["tag"] == "def" and (row["safety"] == "partial" or
                                         row["safety"] == "unsafe" and len(row["all"]) > 1)
        members = [i]
        if mutual:
            if len(set(row["all"])) != len(row["all"]) or row["owned"][0] not in row["all"]:
                problems.append({"line": row["line"], "problem": "malformed mutual names"})
            if any(name not in index for name in row["all"]):
                problems.append({"line": row["line"], "problem": "incomplete mutual group"})
            else:
                members = [index[name] for name in row["all"]]
                if any(j in owner or rows[j]["tag"] != "def" or
                       len(set(rows[j]["all"])) != len(rows[j]["all"]) or
                       set(rows[j]["all"]) != set(row["all"]) for j in members):
                    problems.append({"line": row["line"], "problem": "inconsistent mutual group"})
        for j in members:
            owner[j] = len(batches)
        batches.append({"line": row["line"], "members": members})

    summary = {}
    tree_sizes = {}
    depths = {}
    tree_cap = 10 ** 18
    for expr, (children, dependencies) in exprs.items():
        direct_owners = [owner[index[name]] for name in dependencies if name in index]
        summary[expr] = (
            max([-1, *direct_owners, *(summary[child][0] for child in children)]),
            any(name not in index for name in dependencies) or
            any(summary[child][1] for child in children))
        tree_sizes[expr] = min(tree_cap, 1 + sum(tree_sizes[child] for child in children))
        depths[expr] = 1 + max([0, *(depths[child] for child in children)])
    for i, batch in enumerate(batches):
        for member in batch["members"]:
            row = rows[member]
            for root in row["roots"]:
                maximum, missing = summary[root]
                if maximum > i or missing:
                    problems.append({"line": row["line"], "expression": root,
                                     "forward_dependency": maximum > i,
                                     "missing_dependency": missing})
            if row["tag"] == "quot" and (dotted("Eq") not in index or
                                             owner[index[dotted("Eq")]] > i):
                problems.append({"line": row["line"], "problem": "missing/forward quotient Eq"})
            for name in row["metadata_references"]:
                if name not in index:
                    problems.append({"line": row["line"], "problem": "missing metadata member",
                                     "name": display(name)})
    observed = [event for event in progress if event["stage"] == "declaration"]
    expected = []
    checked = 0
    for batch in batches:
        expected.append((batch["line"], checked))
        checked += len(batch["members"])
    observed_order = [(event["line"], event["checked"]) for event in observed[:len(expected)]]
    observed_matches = observed_order == expected
    used = set()
    todo = [root for row in rows for root in row["roots"]]
    while todo:
        node = todo.pop()
        if node not in used:
            used.add(node)
            todo.extend(exprs[node][0])
    referenced = {name for node in used for name in exprs[node][1]}
    last = rows[-1]
    target_roots = []
    for root in last["roots"]:
        reachable = set()
        todo = [root]
        while todo:
            node = todo.pop()
            if node not in reachable:
                reachable.add(node)
                todo.extend(exprs[node][0])
        target_roots.append({"expression": root, "unique_nodes": len(reachable),
                             "max_depth": depths[root], "unfolded_tree_nodes": tree_sizes[root],
                             "unfolded_tree_count_exact": tree_sizes[root] < tree_cap})
    return {
        "format_metadata": metadata,
        "prefix_lines": len(raw_lines), "declaration_records": len(rows),
        "batches": len(batches), "expression_nodes": len(exprs),
        "reachable_expression_nodes": len(used),
        "referenced_constant_names": len(referenced),
        "missing_constant_names": sorted(display(name) for name in referenced if name not in index),
        "dependency_closed_in_input_order": not problems,
        "observed_full_run_batch_order_matches_prefix": observed_matches,
        "audit_problem_count": len(problems), "audit_problems": problems[:100],
        "last_declaration": {"line": last["line"], "tag": last["tag"],
                             "names": [display(name) for name in last["owned"]],
                             "expression_stats": target_roots,
                             "wire_record": last["wire_record"]},
        "limitations": [
            "This audit checks transport dependencies, not typing or logical validity.",
            "The prefix is a diagnostic derivative, not the full Arena input or a new Arena case.",
            "No separate checker execution is performed on the extracted prefix.",
        ],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-dir", type=Path, required=True)
    parser.add_argument("--line", type=int)
    args = parser.parse_args()
    parent = Path(__file__).resolve().parent
    run_dir = args.run_dir.resolve()
    if run_dir.parent != parent:
        parser.error("run directory must be under arena/large/profile-runs")
    report = json.loads((run_dir / "report.json").read_text())
    provenance = json.loads((run_dir / "provenance.json").read_text())
    line = args.line or report["last_progress"]["line"]
    progress = [json.loads(value) for value in (run_dir / "progress.jsonl").read_text().splitlines()]
    source = Path(provenance["input_before"]["path"])
    raw_lines = []
    source_hash = hashlib.sha256()
    with source.open("rb") as stream:
        for _ in range(line):
            raw = stream.readline()
            if not raw:
                raise ValueError("source ended before requested line")
            raw_lines.append(raw)
            source_hash.update(raw)
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            source_hash.update(block)
    if source_hash.hexdigest() != provenance["input_before"]["sha256"]:
        raise ValueError("source changed since the checker run")
    audit = analyze(raw_lines, progress)
    prefix = run_dir / f"init-through-line-{line}.ndjson"
    with prefix.open("xb") as output:
        output.writelines(raw_lines)
    audit.update({"prefix_path": str(prefix), "prefix_sha256": hashlib.sha256(b"".join(raw_lines)).hexdigest(),
                  "prefix_bytes": sum(map(len, raw_lines)),
                  "source_sha256": provenance["input_before"]["sha256"],
                  "source_sha256_reverified_at_extraction": source_hash.hexdigest(),
                  "source_integrity_verified_by_run": report["integrity_verified"],
                  "byte_identity": "original bytes from byte zero through the newline ending the target declaration"})
    audit_path = run_dir / f"init-through-line-{line}.json"
    with audit_path.open("x") as output:
        json.dump(audit, output, indent=2, sort_keys=True)
        output.write("\n")
    print(json.dumps(audit, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
