#!/bin/sh
set -eu
ROOT=$(CDPATH='' cd -- "$(dirname -- "$0")/../.." && pwd -P)
cd "$ROOT"
sh scripts/toolchain-exec.sh ocamlfind ocamlc -package yojson,zarith \
  -I build/frontend -c -o build/frontend/verify_slices.cmo \
  tests/hol_composition/verify_slices.ml
sh scripts/toolchain-exec.sh ocamlfind ocamlc -package yojson,zarith -linkpkg \
  -I build/frontend build/frontend/wire.cmo build/frontend/verify_slices.cmo \
  -o build/verify-indexed-slices
DATA=tests/hol_composition/data
sh scripts/toolchain-exec.sh build/verify-indexed-slices \
  "$DATA/sources/indexed/inmodel_mutual_idx.ndjson" \
  "$DATA/fixtures/indexed/rs-slice.ndjson" "$DATA/sources/indexed/rs-slice.ndjson.lines"
sh scripts/toolchain-exec.sh build/verify-indexed-slices \
  "$DATA/sources/indexed/ind_mutual_idxsort.ndjson" \
  "$DATA/fixtures/indexed/ma-mb-slice.ndjson" "$DATA/sources/indexed/ma-mb-slice.ndjson.lines"
