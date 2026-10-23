#!/bin/sh
# Opt-in transport build only. Does not launch HOL or alter default dispatch.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd -P)
cd "$ROOT"
sh scripts/build-hol-frontend.sh
sh scripts/toolchain-exec.sh ocamlfind ocamlc -package yojson,zarith -I build/frontend \
    -c -o build/frontend/hol_safety_input.cmo frontend/hol_safety_input.ml
sh scripts/toolchain-exec.sh ocamlfind ocamlc -package yojson,zarith -I build/frontend \
    -c -o build/frontend/hol_safety_frontend_tests.cmo tests/hol_safety/frontend_tests.ml
sh scripts/toolchain-exec.sh ocamlfind ocamlc -package yojson,zarith -linkpkg -I build/frontend \
    build/frontend/wire.cmo build/frontend/replay.cmo build/frontend/hol_input.cmo \
    build/frontend/hol_safety_input.cmo build/frontend/hol_safety_frontend_tests.cmo \
    -o build/test-hol-safety-input
sh scripts/toolchain-exec.sh build/test-hol-safety-input
