#!/usr/bin/env python3
"""Synthetic runner protocol/fault process. Never produces a HOL/Arena verdict."""
import os
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
    done = f'REFLECTION_STAGE_DONE {nonce} {index}'
    marker = f'COMPOSED_WORK_PASS synthetic-{index} 1'
    if mode == 'completion-first':
        print(done, flush=True)
    print(marker, flush=True)
    if mode == 'duplicate':
        print(marker, flush=True)
    if mode == 'wrong-marker':
        print('COMPOSED_WORK_PASS not-requested 1', flush=True)
    if mode == 'unfinished':
        time.sleep(30)
    if mode == 'log-flood':
        print('X' * 32768, flush=True)
    if mode == 'in-stage-error':
        print('Exception: synthetic in-stage fault', flush=True)
    print(done, flush=True)
    if mode == 'duplicate-done':
        print(done, flush=True)
    if mode == 'interstage-error' and index == '0':
        time.sleep(0.03)
        print('Exception: synthetic after stage completion', flush=True)

if mode == 'final-error':
    print('Error in included file: synthetic-late.ml', flush=True)
elif mode == 'surviving-child':
    child = os.fork()
    if child == 0:
        time.sleep(1)
        os._exit(0)
    print(f'SYNTHETIC_CHILD {child}', flush=True)
elif mode == 'nonzero':
    sys.exit(7)
