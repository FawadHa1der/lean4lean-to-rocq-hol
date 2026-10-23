#!/bin/sh
# Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd -P)
cd "$ROOT"
LOG=${HOL_CORE_LOG:-/private/tmp/lean4hol-core-tests.log}
cat hol/tests.ml hol/nat_literal_tests.ml hol/family_tests.ml hol/indexed_tests.ml \
  hol/projection_core_tests.ml hol/projection_tests.ml hol/structure_tests.ml |
  LINE_EDITOR=env sh scripts/toolchain-exec.sh hol.sh > "$LOG" 2>&1
if ! grep -Eq '(^|[[:space:]])HOL_CORE_TESTS_PASSED [0-9]+[[:space:]]*$' "$LOG" ||
   ! grep -Eq '(^|[[:space:]])HOL_ADMISSION_TESTS_PASSED [0-9]+[[:space:]]*$' "$LOG" ||
   ! grep -Eq '(^|[[:space:]])HOL_ENVIRONMENT_TESTS_PASSED [0-9]+[[:space:]]*$' "$LOG" ||
   ! grep -Eq '(^|[[:space:]])HOL_INDUCTIVE_TESTS_PASSED [0-9]+[[:space:]]*$' "$LOG" ||
   ! grep -Eq '(^|[[:space:]])HOL_NAT_LITERAL_TESTS_PASSED [0-9]+[[:space:]]*$' "$LOG" ||
   ! grep -Eq '(^|[[:space:]])HOL_FAMILY_TESTS_PASSED [0-9]+[[:space:]]*$' "$LOG" ||
   ! grep -Eq '(^|[[:space:]])HOL_INDEXED_TESTS_PASSED [0-9]+[[:space:]]*$' "$LOG" ||
   ! grep -Eq '(^|[[:space:]])HOL_PROJECTION_CORE_TESTS_PASSED [0-9]+[[:space:]]*$' "$LOG" ||
   ! grep -Eq '(^|[[:space:]])HOL_PROJECTION_TESTS_PASSED [0-9]+[[:space:]]*$' "$LOG" ||
   ! grep -Eq '(^|[[:space:]])HOL_STRUCTURE_TESTS_PASSED [0-9]+[[:space:]]*$' "$LOG" ||
   grep -Eq '(^|[[:space:]])(Error:|Exception:)|Parse error|Error in included file' "$LOG"; then
    tail -100 "$LOG"
    echo "HOL core regression failed; full log: $LOG" >&2
    exit 1
fi
grep -E '(^|[[:space:]])HOL_CORE_TESTS_PASSED [0-9]+[[:space:]]*$' "$LOG"
grep -E '(^|[[:space:]])HOL_ADMISSION_TESTS_PASSED [0-9]+[[:space:]]*$' "$LOG"
grep -E '(^|[[:space:]])HOL_ENVIRONMENT_TESTS_PASSED [0-9]+[[:space:]]*$' "$LOG"
grep -E '(^|[[:space:]])HOL_INDUCTIVE_TESTS_PASSED [0-9]+[[:space:]]*$' "$LOG"
grep -E '(^|[[:space:]])HOL_NAT_LITERAL_TESTS_PASSED [0-9]+[[:space:]]*$' "$LOG"
grep -E '(^|[[:space:]])HOL_FAMILY_TESTS_PASSED [0-9]+[[:space:]]*$' "$LOG"
grep -E '(^|[[:space:]])HOL_INDEXED_TESTS_PASSED [0-9]+[[:space:]]*$' "$LOG"
grep -E '(^|[[:space:]])HOL_PROJECTION_CORE_TESTS_PASSED [0-9]+[[:space:]]*$' "$LOG"
grep -E '(^|[[:space:]])HOL_PROJECTION_TESTS_PASSED [0-9]+[[:space:]]*$' "$LOG"
grep -E '(^|[[:space:]])HOL_STRUCTURE_TESTS_PASSED [0-9]+[[:space:]]*$' "$LOG"
echo "HOL core proof log: $LOG"
