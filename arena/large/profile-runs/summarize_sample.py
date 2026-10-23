#!/usr/bin/env python3
"""Summarize an existing macOS sample tree; do not collect another sample."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re


FRAME = re.compile(r"^([ +!:|]*)(\d+) (.+)$")
GRAPH_END = re.compile(r"^Total number in stack(?: \([^\r\n]*\))?:$")


def summarize(text):
    stack = []
    inclusive = Counter()
    exclusive = Counter()
    roots = 0
    active = False
    complete = False

    def finish(node):
        remaining = node["count"] - node["children"]
        if remaining < 0:
            raise ValueError("sample children exceed their parent count")
        exclusive[node["symbol"]] += remaining

    for raw in text.splitlines():
        if raw == "Call graph:":
            if active:
                raise ValueError("duplicate sample call graph header")
            active = True
            continue
        if not active:
            continue
        if GRAPH_END.fullmatch(raw):
            complete = True
            break
        match = FRAME.match(raw)
        if match is None:
            if not raw.strip():
                continue
            raise ValueError("unrecognized line within sample call graph")
        prefix, count, description = match.groups()
        depth = len(prefix)
        count = int(count)
        symbol = description.split("  (in ", 1)[0]
        while stack and stack[-1]["depth"] >= depth:
            finish(stack.pop())
        if stack:
            stack[-1]["children"] += count
        else:
            roots += count
        if not any(node["symbol"] == symbol for node in stack):
            inclusive[symbol] += count
        stack.append({"depth": depth, "count": count, "symbol": symbol, "children": 0})
    # At EOF, missing children would otherwise be misattributed to their parents.
    # Summing those invented leaves still equals the root count, so it is not a
    # completeness check. The format's explicit graph terminator is required.
    if not complete:
        raise ValueError("incomplete sample call graph (missing terminator)")
    while stack:
        finish(stack.pop())
    if sum(exclusive.values()) != roots or roots == 0:
        raise ValueError("sample tree did not account for every stack sample")
    def rows(counter):
        return [{"symbol": symbol, "samples": count, "percent": 100 * count / roots}
                for symbol, count in counter.most_common() if count]
    return {"call_graph_complete": True, "stack_samples": roots,
            "exclusive_accounted_samples": sum(exclusive.values()),
            "exclusive": rows(exclusive), "inclusive_without_recursive_double_count": rows(inclusive),
            "note": "Inclusive rows overlap across different functions; do not add their percentages."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("sample", type=Path)
    args = parser.parse_args()
    path = args.sample.resolve()
    if path.parent.parent != Path(__file__).resolve().parent:
        parser.error("sample must be in a run directory under arena/large/profile-runs")
    raw = path.read_bytes()
    result = summarize(raw.decode("utf-8"))
    result["source_sha256"] = hashlib.sha256(raw).hexdigest()
    output = path.with_name("sample-summary.json")
    with output.open("x") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"stack_samples": result["stack_samples"],
                      "exclusive_top": result["exclusive"][:12],
                      "inclusive_top": result["inclusive_without_recursive_double_count"][:20]}, indent=2))


if __name__ == "__main__":
    main()
