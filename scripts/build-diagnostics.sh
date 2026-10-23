#!/bin/sh
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd -P)
cd "$ROOT"
sh scripts/toolchain-exec.sh ocamlfind ocamlopt -package yojson,zarith \
  -I build/frontend -I build/rocq -c -o build/rocq/diagnose_inductive.cmx frontend/diagnose_inductive.ml
sh scripts/toolchain-exec.sh ocamlfind ocamlopt -package yojson,zarith -linkpkg \
  -I build/frontend -I build/rocq build/frontend/wire.cmx build/frontend/replay.cmx build/rocq/lean_arena.cmx \
  build/rocq/rocq_adapter.cmx build/rocq/diagnose_inductive.cmx -o build/diagnose-inductive
