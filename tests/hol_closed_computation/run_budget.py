#!/usr/bin/env python3
"""Compile the pure cache accounting regressions; this does not launch HOL."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]


def main():
    sources = [ROOT / 'hol/closed_budget.ml', Path(__file__).with_name('budget_tests.ml')]
    before = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in sources}
    with tempfile.TemporaryDirectory(prefix='closed-budget-') as temporary:
        build = Path(temporary)
        tool = ['sh', str(ROOT / 'scripts/toolchain-exec.sh'), 'ocamlc']
        for source in sources:
            subprocess.run([*tool, '-I', str(build), '-c', '-o',
                            str(build / (source.stem + '.cmo')), str(source)],
                           cwd=ROOT, check=True, timeout=60)
        binary = build / 'budget-tests'
        subprocess.run([*tool, '-I', str(build), '-o', str(binary),
                        *[str(build / (p.stem + '.cmo')) for p in sources]],
                       cwd=ROOT, check=True, timeout=60)
        result = subprocess.run([str(binary)], cwd=ROOT, check=True,
                                capture_output=True, text=True, timeout=60)
    if result.stdout.strip() != 'CLOSED_BUDGET_OFFLINE_PASS 83391' or result.stderr:
        raise RuntimeError('Unexpected accounting test output: ' + repr(result))
    after = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
             for p in sources}
    if after != before:
        raise RuntimeError('Accounting sources changed during execution')
    print(result.stdout.strip())
    print(json.dumps({'source_sha256': after, 'source_unchanged': True}))


if __name__ == '__main__':
    main()
