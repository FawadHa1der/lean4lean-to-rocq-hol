#!/usr/bin/env python3
"""Explicit ONE-TIME preservation gate; never imported by the safety runner/tests.

The original pins are intentionally immutable. Later independently approved
changes may fail this historical gate without being safety regressions.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

import helper_contract

BASELINE = Path(__file__).resolve().parent / 'baseline'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def registry_keys(root):
    directory = root / 'tests/hol_composition'
    spec = importlib.util.spec_from_file_location('safety_integration_registry', directory / 'run.py')
    module = importlib.util.module_from_spec(spec)
    sys.path.insert(0, str(directory))
    try:
        spec.loader.exec_module(module)
    finally:
        sys.path.pop(0)
    return list(module.jobs())


def inspect(root, stage):
    if stage not in ('before', 'after'):
        raise ValueError('stage must be before or after')
    baseline = json.loads((BASELINE / 'source-pins.json').read_text())
    checks = []

    def check(label, action):
        try:
            passed, details = action()
            checks.append({'label': label, 'passed': bool(passed), 'details': details})
        except Exception as error:
            checks.append({'label': label, 'passed': False, 'error': str(error)})

    def file_hash(path, expected):
        actual = digest(path)
        return actual == expected, {'expected': expected, 'actual': actual}

    for relative, expected in baseline['source_sha256'].items():
        check(relative, lambda p=relative, h=expected: file_hash(root / p, h))
    check('original environment baseline integrity', lambda:
          file_hash(BASELINE / 'environment.ml', baseline['environment_before_sha256']))

    def environment():
        source = (root / 'hol/environment.ml').read_text()
        if stage == 'after':
            helper_contract.require_helper(source)
            source = source.replace(helper_contract.DECLARATION, '', 1)
            source = source.replace(helper_contract.IMPLEMENTATION, '', 1)
        return source == (BASELINE / 'environment.ml').read_text(), {
            'stage': stage, 'scope': 'whole environment, excluding exactly the two helper insertions after integration'}

    check('whole environment preservation', environment)

    def registry():
        actual = registry_keys(root)
        return len(actual) == baseline['registry_count'] and actual == baseline['registry_keys'], {
            'expected_count': baseline['registry_count'], 'actual_count': len(actual),
            'expected_keys': baseline['registry_keys'], 'actual_keys': actual}

    check('original registry count and ordered keys', registry)
    return {'kind': 'explicit one-time integration preservation', 'root': str(root), 'stage': stage,
            'checks': checks, 'passed': all(c['passed'] for c in checks),
            'native_runs': 0, 'routine_safety_verdict': False,
            'boundary': 'A failure may reflect a separately reviewed unrelated integration. Do not refresh these original pins to make it pass.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--stage', choices=('before', 'after'), required=True)
    args = parser.parse_args()
    result = inspect(args.root.resolve(), args.stage)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result['passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
