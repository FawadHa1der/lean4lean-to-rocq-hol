#!/bin/sh
# Rebuild the native bridge from existing, coherent structural extraction.
set -eu
PROJECT_ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd -P)
cd "$PROJECT_ROOT"
mkdir -p build/rocq
run() { sh "$PROJECT_ROOT/scripts/toolchain-exec.sh" "$@"; }
run ocamlopt -c -o build/rocq/lean_arena.cmi rocq/lean_arena.mli
run ocamlopt -I build/rocq -c -o build/rocq/lean_arena.cmx rocq/lean_arena.ml
for module in rocq_adapter dag_adapter persistent_adapter rocq_main; do
    run ocamlfind ocamlopt -package yojson,zarith -I build/frontend -I build/rocq \
        -c -o "build/rocq/$module.cmx" "frontend/$module.ml"
done
run ocamlfind ocamlopt -package yojson,zarith -linkpkg -I build/frontend -I build/rocq \
    build/frontend/wire.cmx build/frontend/replay.cmx build/rocq/lean_arena.cmx \
    build/rocq/rocq_adapter.cmx build/rocq/dag_adapter.cmx build/rocq/persistent_adapter.cmx build/rocq/rocq_main.cmx \
    -o build/rocq-check.next
mv build/rocq-check.next build/rocq-check
