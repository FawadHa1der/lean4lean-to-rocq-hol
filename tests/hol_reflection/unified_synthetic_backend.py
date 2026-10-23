#!/usr/bin/env python3
"""Synthetic UNIFIED protocol faults; never a HOL or Arena verdict."""
import re
import sys
import time

mode = sys.argv[1]
for line in sys.stdin:
    if not line.startswith('Printf.printf '):
        continue
    match = re.search(r'REFLECTION_STAGE_DONE ([0-9a-f]+) (\d+)', line)
    if not match:
        continue
    nonce, index = match.groups()
    i = int(index)
    done = f'REFLECTION_STAGE_DONE {nonce} {index}'
    marker = ('NAT_INSTANTIATION_SETUP_READY' if i == 0 else
              'UNIFIED_SETUP_READY' if i == 1 else f'UNIFIED_WORK_PASS synthetic-{index} 1')
    if mode == 'completion-first' and i == 2:
        print(done, flush=True)
    if mode == 'out-of-order' and i == 0:
        print('UNIFIED_SETUP_READY', flush=True)
    if not (mode == 'missing' and i == 2):
        print(marker, flush=True)
    if mode == 'duplicate' and i == 2:
        print(marker, flush=True)
    if mode == 'unexpected' and i == 2:
        print('UNIFIED_WORK_PASS other 1', flush=True)
    if mode == 'failure' and i == 2:
        print('UNIFIED_WORK_FAIL synthetic-2 explicit fault', flush=True)
    if mode == 'unfinished' and i == 2:
        time.sleep(30)
    if mode == 'wrong-nonce' and i == 2:
        done = f'REFLECTION_STAGE_DONE 00000000 {index}'
    print(done, flush=True)

if mode == 'late-failure':
    print('UNIFIED_WORK_FAIL synthetic-2 late explicit fault', flush=True)
elif mode == 'late-error':
    print('Error in included file: synthetic-late.ml', flush=True)
