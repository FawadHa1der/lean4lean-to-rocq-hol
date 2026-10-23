#!/bin/sh
set -eu
ROOT=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd -P)
cd "$ROOT"
B=build/rocq-regressions
run() { sh scripts/toolchain-exec.sh ocamlfind ocamlopt -package yojson,zarith "$@"; }
for suite in test_hints test_hint_callbacks; do
  run -w +8+11 -warn-error +8+11 -I "$B" -c -o "$B/$suite.cmx" "frontend/$suite.ml"
  run -linkpkg -I "$B" "$B/wire.cmx" "$B/replay.cmx" "$B/lean_arena.cmx" \
    "$B/rocq_adapter.cmx" "$B/dag_adapter.cmx" "$B/persistent_adapter.cmx" \
    "$B/full_result.cmx" "$B/$suite.cmx" -o "$B/$suite"
done
"$B/test_hints"
"$B/test_hint_callbacks" "${1:-tests/rocq/hint-policy-controls.json}"
