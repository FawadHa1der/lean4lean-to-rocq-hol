#!/bin/sh
set -eu
PROJECT_ROOT=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd -P)
. "$PROJECT_ROOT/scripts/toolchain-env.sh"
run() { sh "$PROJECT_ROOT/scripts/toolchain-exec.sh" "$@"; }
mkdir -p "$TOOLCHAIN_DIR/smoke-build" "$TOOLCHAIN_DIR/logs"
cp "$TOOLCHAIN_DIR/smoke/Smoke.v" "$TOOLCHAIN_DIR/smoke/Reject.v" "$TOOLCHAIN_DIR/smoke/smoke_ocaml.ml" "$TOOLCHAIN_DIR/smoke-build/"
cd "$TOOLCHAIN_ALIAS/smoke-build"
run ocamlc -version
run rocq --version
run rocq compile Smoke.v > "$TOOLCHAIN_DIR/logs/rocq-smoke.log" 2>&1
grep -q 'Closed under the global context' "$TOOLCHAIN_DIR/logs/rocq-smoke.log"
if run rocq compile Reject.v > "$TOOLCHAIN_DIR/logs/rocq-reject.log" 2>&1; then
    echo "FAIL: Rocq accepted an invalid proof" >&2
    exit 1
fi
grep -q 'expected to have type' "$TOOLCHAIN_DIR/logs/rocq-reject.log"
run rocq check Smoke > "$TOOLCHAIN_DIR/logs/rocq-check.log" 2>&1
run ocamlfind ocamlopt -package unix,yojson,zarith -linkpkg smoke_extracted.mli smoke_extracted.ml smoke_ocaml.ml -o smoke-ocaml
./smoke-ocaml > "$TOOLCHAIN_DIR/logs/ocaml-smoke.log"
cat "$TOOLCHAIN_DIR/logs/ocaml-smoke.log"
LINE_EDITOR='env' run hol.sh < "$TOOLCHAIN_DIR/smoke/smoke_hol.ml" > "$TOOLCHAIN_DIR/logs/hol-smoke.log" 2>&1
grep -Eq '^[# >]*HOL_THEOREM_AND_REJECTION_OK$' "$TOOLCHAIN_DIR/logs/hol-smoke.log"
if grep -E '(^|# )Error:|Exception:|Error in included file|Parse error' "$TOOLCHAIN_DIR/logs/hol-smoke.log"; then
    echo "FAIL: HOL Light reported an error; inspect toolchain/logs/hol-smoke.log" >&2
    exit 1
fi
printf 'PASS: Rocq proof, kernel recheck, invalid-proof rejection, OCaml extraction, Yojson/Zarith, HOL Light proof and rejection\n'
