#!/bin/sh
# Load and verify all 138 hol/*.ml modules of kernel_v3_complete across two
# fresh sequential HOL Light sessions:
#   1. verify_all_v3.ml     — 130 core/metatheory/property/regression modules
#   2. verify_entries_v3.ml —   8 held "655" entry modules + 104 entry cases
#                             (candidate_entry655 requires a pristine session)
# Usage: sh hol/kernel_v3_complete/verify_all_v3.sh [LOGDIR]
set -eu
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)
ROOT=$(CDPATH='' cd -- "$HERE/../.." && pwd -P)
SCRATCH=${1:-${LEAN4LEAN_V3_SCRATCH:-$(mktemp -d /tmp/lean4lean-v3.XXXXXX)}}
MAIN_LOG="$SCRATCH/verify_all_v3.log"
ENTRIES_LOG="$SCRATCH/verify_entries_v3.log"
mkdir -p "$SCRATCH/frontend" "$SCRATCH/fixture_tmp_main" "$SCRATCH/fixture_tmp_entries"
run() { sh "$ROOT/scripts/toolchain-exec.sh" "$@"; }

# Genuine Wire/Replay frontend required by full_input610 and its dependents.
run ocamlfind ocamlc -package yojson,zarith -c \
  -o "$SCRATCH/frontend/wire.cmo" "$HERE/frontend/wire.ml"
run ocamlfind ocamlc -package yojson,zarith -I "$SCRATCH/frontend" -c \
  -o "$SCRATCH/frontend/replay.cmo" "$HERE/frontend/replay.ml"

cd "$HERE"
start=$(date +%s)

# Run sessions sequentially under bounded virtual memory and compact OCaml GC
# so verification succeeds reliably on 8 GiB / 0 swap environments.
(
  ulimit -v 4500000
  OCAMLRUNPARAM="s=16M,i=32M,o=30" \
  LEAN4LEAN_FIXTURE_TMPDIR="$SCRATCH/fixture_tmp_main" \
  LEAN4LEAN_V3_FRONTEND_DIR="$SCRATCH/frontend" \
  LINE_EDITOR=env run hol.sh < verify_all_v3.ml > "$MAIN_LOG" 2>&1
) || true

(
  ulimit -v 4500000
  OCAMLRUNPARAM="s=16M,i=32M,o=30" \
  LEAN4LEAN_FIXTURE_TMPDIR="$SCRATCH/fixture_tmp_entries" \
  LEAN4LEAN_V3_FRONTEND_DIR="$SCRATCH/frontend" \
  LINE_EDITOR=env run hol.sh < verify_entries_v3.ml > "$ENTRIES_LOG" 2>&1
) || true

end=$(date +%s)

echo "wall_clock_seconds=$((end - start))"
echo "=== Session 1: verify_all_v3.ml ($MAIN_LOG) ==="
grep -E '^(V3_SUMMARY|V3_FAILED|AXIOMS=|AXIOM |V3_CHECK_AXIOMS|V3_LOAD_DONE)' "$MAIN_LOG" || true
echo "=== Session 2: verify_entries_v3.ml ($ENTRIES_LOG) ==="
grep -E '^(V3E_SUMMARY|V3E_FAILED|V3E_CASES|V3E_CASE_FAILED|AXIOMS=|AXIOM |V3_CHECK_AXIOMS|V3_LOAD_DONE)' "$ENTRIES_LOG" || true

# Verify exact disk coverage: every hol/*.ml file must appear in V3_MODULE_OK.
ls hol/*.ml | LC_ALL=C sort > "$SCRATCH/expected_modules.txt"
sed -n 's/^V3_MODULE_OK \(hol\/[^ ]*\.ml\) .*/\1/p' "$MAIN_LOG" "$ENTRIES_LOG" | LC_ALL=C sort -u > "$SCRATCH/verified_modules.txt"
expected_count=$(wc -l < "$SCRATCH/expected_modules.txt" | tr -d ' ')
verified_count=$(wc -l < "$SCRATCH/verified_modules.txt" | tr -d ' ')
echo "disk_coverage: verified=$verified_count expected=$expected_count"

if ! cmp -s "$SCRATCH/expected_modules.txt" "$SCRATCH/verified_modules.txt"; then
  echo "MISSING_OR_EXTRA_MODULES:" >&2
  diff -u "$SCRATCH/expected_modules.txt" "$SCRATCH/verified_modules.txt" >&2 || true
  echo "V3_VERIFICATION_INCOMPLETE" >&2
  exit 1
fi

if grep -q '^V3_SUMMARY loaded=130 failed=0 total=130$' "$MAIN_LOG" &&
   grep -q '^AXIOMS=3$' "$MAIN_LOG" &&
   grep -q '^V3_CHECK_AXIOMS_OK$' "$MAIN_LOG" &&
   grep -q '^V3_LOAD_DONE$' "$MAIN_LOG" &&
   grep -q '^V3E_SUMMARY loaded=8 failed=0 total=8$' "$ENTRIES_LOG" &&
   grep -q '^V3E_CASES ok=104 failed=0$' "$ENTRIES_LOG" &&
   grep -q '^AXIOMS=3$' "$ENTRIES_LOG" &&
   grep -q '^V3_CHECK_AXIOMS_OK$' "$ENTRIES_LOG" &&
   grep -q '^V3_LOAD_DONE$' "$ENTRIES_LOG"; then
  echo "V3_ALL_MODULES_VERIFIED"
else
  echo "V3_VERIFICATION_INCOMPLETE" >&2
  exit 1
fi
