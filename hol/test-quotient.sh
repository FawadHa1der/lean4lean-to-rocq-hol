#!/bin/sh
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd -P)
cd "$ROOT"
LOG=${HOL_QUOTIENT_LOG:-/private/tmp/lean4hol-quotient-tests.log}
python3 -c 'import os,signal,subprocess
p=subprocess.Popen(["sh","scripts/toolchain-exec.sh","hol.sh"],stdin=subprocess.PIPE,
  stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True,
  env=dict(os.environ,LINE_EDITOR="env"))
try:
  out,_=p.communicate(b"needs \"hol/quotient_tests.ml\";;\n",timeout=180)
  print(out.decode(errors="replace")); raise SystemExit(p.returncode)
except subprocess.TimeoutExpired:
  os.killpg(p.pid,signal.SIGKILL); out,_=p.communicate()
  print(out.decode(errors="replace")); raise SystemExit(124)
' > "$LOG" 2>&1
if ! grep -Eq 'HOL_QUOTIENT_TESTS_PASSED [0-9]+' "$LOG" ||
   grep -Eq '(^|[[:space:]])(Error:|Exception:)|Parse error|Error in included file' "$LOG"; then
  tail -100 "$LOG"
  exit 1
fi
grep -E 'HOL_QUOTIENT_TESTS_PASSED [0-9]+' "$LOG"
