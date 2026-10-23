#!/bin/sh
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd -P)
cd "$ROOT"
LOG=${HOL_QUOTIENT_LOG:-/private/tmp/lean4hol-quotient-syntax-tests.log}
FIXTURE=arena/corpus/tutorial/128_quotLiftType.ndjson
printf '%s  %s\n' 3abbf269039bfe725e22e5ae35438451f87ea200b2434e2e402deac0b9c8faf3 "$FIXTURE" |
  shasum -a 256 -c -
mkdir -p build/quotient-syntax
run() { sh scripts/toolchain-exec.sh "$@"; }
run ocamlfind ocamlopt -package yojson,zarith -c \
  -o build/quotient-syntax/wire.cmx frontend/wire.ml
run ocamlfind ocamlopt -package yojson,zarith -I build/quotient-syntax -c \
  -o build/quotient-syntax/quotient_signature_dump.cmx frontend/quotient_signature_dump.ml
run ocamlfind ocamlopt -package yojson,zarith -linkpkg -I build/quotient-syntax \
  build/quotient-syntax/wire.cmx build/quotient-syntax/quotient_signature_dump.cmx \
  -o build/quotient-syntax/signature-dump
build/quotient-syntax/signature-dump "$FIXTURE" > build/hol-quotient-inputs.ml
python3 -c 'import os,signal,subprocess
p=subprocess.Popen(["sh","scripts/toolchain-exec.sh","hol.sh"],stdin=subprocess.PIPE,
  stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True,
  env=dict(os.environ,LINE_EDITOR="env"))
try:
  out,_=p.communicate(b"needs \"hol/quotient_syntax_tests.ml\";;\n",timeout=180)
  print(out.decode(errors="replace")); raise SystemExit(p.returncode)
except subprocess.TimeoutExpired:
  os.killpg(p.pid,signal.SIGKILL); out,_=p.communicate()
  print(out.decode(errors="replace")); raise SystemExit(124)
' > "$LOG" 2>&1
if ! grep -Eq 'HOL_QUOTIENT_SYNTAX_TESTS_PASSED [0-9]+' "$LOG" ||
   grep -Eq '(^|[[:space:]])(Error:|Exception:)|Parse error|Error in included file' "$LOG"; then
  tail -80 "$LOG"
  exit 1
fi
grep -E 'HOL_QUOTIENT_SYNTAX_TESTS_PASSED [0-9]+' "$LOG"
