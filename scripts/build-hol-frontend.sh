#!/bin/sh
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd -P)
cd "$ROOT"
mkdir -p build/frontend
sh scripts/toolchain-exec.sh ocamlfind ocamlc -package yojson,zarith \
    -c -o build/frontend/wire.cmo frontend/wire.ml
sh scripts/toolchain-exec.sh ocamlfind ocamlc -package yojson,zarith -I build/frontend \
    -c -o build/frontend/replay.cmo frontend/replay.ml
sh scripts/toolchain-exec.sh ocamlfind ocamlc -package yojson,zarith -I build/frontend \
    -c -o build/frontend/hol_input.cmo frontend/hol_input.ml
sh scripts/toolchain-exec.sh ocamlfind ocamlc -package yojson,zarith -I build/frontend \
    -c -o build/frontend/test_hol_input.cmo frontend/test_hol_input.ml
sh scripts/toolchain-exec.sh ocamlfind ocamlc -package yojson,zarith -linkpkg -I build/frontend \
    build/frontend/wire.cmo build/frontend/replay.cmo build/frontend/hol_input.cmo \
    build/frontend/test_hol_input.cmo -o build/test-hol-input
sh scripts/toolchain-exec.sh build/test-hol-input
