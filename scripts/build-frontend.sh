#!/bin/sh
set -eu
PROJECT_ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd -P)
cd "$PROJECT_ROOT"
mkdir -p build/frontend
run() { sh "$PROJECT_ROOT/scripts/toolchain-exec.sh" "$@"; }
run ocamlfind ocamlopt -package yojson,zarith -c -o build/frontend/wire.cmx frontend/wire.ml
run ocamlfind ocamlopt -package yojson,zarith -I build/frontend -c \
    -o build/frontend/test_wire.cmx frontend/test_wire.ml
run ocamlfind ocamlopt -package yojson,zarith -linkpkg -I build/frontend \
    build/frontend/wire.cmx build/frontend/test_wire.cmx -o build/frontend/test-wire
run ocamlfind ocamlopt -package yojson,zarith -I build/frontend -c \
    -o build/frontend/inspect_wire.cmx frontend/inspect_wire.ml
run ocamlfind ocamlopt -package yojson,zarith -linkpkg -I build/frontend \
    build/frontend/wire.cmx build/frontend/inspect_wire.cmx -o build/frontend/inspect-wire
build/frontend/test-wire
for module in replay test_replay; do
  run ocamlfind ocamlopt -package yojson,zarith -I build/frontend -c \
    -o "build/frontend/$module.cmx" "frontend/$module.ml"
done
run ocamlfind ocamlopt -package yojson,zarith -linkpkg -I build/frontend \
  build/frontend/wire.cmx build/frontend/replay.cmx build/frontend/test_replay.cmx \
  -o build/frontend/test-replay
build/frontend/test-replay
run ocamlfind ocamlopt -package yojson,zarith -I build/frontend -c \
  -o build/frontend/inspect_replay.cmx frontend/inspect_replay.ml
run ocamlfind ocamlopt -package yojson,zarith -linkpkg -I build/frontend \
  build/frontend/wire.cmx build/frontend/replay.cmx build/frontend/inspect_replay.cmx \
  -o build/frontend/inspect-replay
