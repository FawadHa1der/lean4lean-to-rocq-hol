#!/usr/bin/env python3
"""Baseline-gated P2 regression on the frozen checkpoint plus one exact flags patch."""

import argparse
from collections import Counter
import difflib
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
AUDIT = HERE.parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from test_metadata_mutations import materialize, validate_materialized, run_suite, checker_snapshot
from test_arena import utc_now

SOURCE_MANIFEST_SHA = '0da63b7358a3e038924bf2512c4f4c4091715f5bcd7be1424a824f90e16f4ead'
REVIEW_SHA = '7677c7e691c7a42884b0ff7e97577960615396e6d8bfeddb62fba5988c2003fa'
ORIGINAL_READY_SHA = '19aa5c31e75e63e3859b643f897815b4a46ff6e423b38de3189d7507a99be34d'
FIXED_ENV_SHA = '6eb71198bbbe0bbda583aa5bfc9830e6fda1de95e1ea195c0f1f08e6444d22a8'
CASE_IDS = ['sortelim-coherent/' + name for name in (
    'hidden-data-prop-only', 'hidden-data-forged-large',
    'nested-index-prop-only', 'nested-index-forged-large')]
OLD = '''        REWRITE_TAC ([l4_index_large;l4_index_large_fields;l4_index_k;ALL;ALL2;LENGTH;
          l4_index_fields;l4_index_result;distinctness "list";injectivity "list";hn] @ zeros) THEN'''
NEW = '''        REWRITE_TAC ([l4_index_large;l4_index_large_fields;l4_index_k;ALL;ALL2;LENGTH;MEM;
          l4_index_fields;l4_index_result;distinctness "l4_expr";injectivity "l4_expr";
          distinctness "list";injectivity "list";hn] @ zeros) THEN'''


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def pinned(path, digest):
    if path.is_symlink():
        raise ValueError('symlink input: ' + str(path))
    raw = path.read_bytes()
    if sha(raw) != digest:
        raise ValueError('hash mismatch: ' + str(path))
    return raw


def plan(private):
    snapshot = json.loads(pinned(AUDIT / 'snapshot/manifest.json', REVIEW_SHA))
    original = (AUDIT / 'snapshot/hol/environment.ml').read_text()
    if original.count(OLD) != 1:
        raise ValueError('the reviewed flags block is not unique')
    fixed = original.replace(OLD, NEW, 1).encode()
    if sha(fixed) != FIXED_ENV_SHA:
        raise ValueError('fixed-source pin mismatch')
    # Copy source changes, not just startup hashes, are restricted to the flags block.
    for e in snapshot['inputs']:
        pinned(AUDIT / 'snapshot' / e['path'], e['sha256'])
        expected = FIXED_ENV_SHA if e['path'] == 'hol/environment.ml' else e['sha256']
        pinned(private / e['path'], expected)
    if (private / 'hol/environment.ml').read_bytes() != fixed:
        raise ValueError('private edit exceeds the exact flags change')
    source = json.loads(pinned(AUDIT / 'manifest.json', SOURCE_MANIFEST_SHA))
    manifest = {'version': 1, 'suite': 'hol-indexed-p2-fix-v1', 'source_manifest_sha256': SOURCE_MANIFEST_SHA,
                'review_manifest_sha256': REVIEW_SHA, 'fixed_environment_sha256': FIXED_ENV_SHA,
                'baselines': source['baselines'], 'cases': [c for c in source['cases'] if c['id'] in CASE_IDS]}
    if sorted(c['id'] for c in manifest['cases']) != sorted(CASE_IDS):
        raise ValueError('targeted case selection is incomplete')
    files = {e['path']: pinned(AUDIT / e['path'], e['sha256'])
             for e in manifest['baselines'] + manifest['cases']}
    files['flags.patch'] = ''.join(difflib.unified_diff(original.splitlines(True), fixed.decode().splitlines(True),
                                                      fromfile='a/hol/environment.ml', tofile='b/hol/environment.ml')).encode()
    return manifest, files


def check_runtime(private, path, expected_digest):
    raw = pinned(path, expected_digest)
    runtime = json.loads(raw)
    original = json.loads(pinned(AUDIT / 'indexed-startup-provenance.json', ORIGINAL_READY_SHA))
    expected = {e['path']: e['sha256'] for e in original['snapshot']['inputs']}
    expected['hol/environment.ml'] = FIXED_ENV_SHA
    actual = {e['path']: e['sha256'] for e in runtime['snapshot']['inputs']}
    if actual != expected or len(actual) != len(runtime['snapshot']['inputs']):
        raise ValueError('private runtime is not the exact reviewed closure plus flags fix')
    if Path(runtime['snapshot']['project_root']) != private:
        raise ValueError('runtime root differs from private source tree')
    if runtime['snapshot']['bootstrap'] != original['snapshot']['bootstrap']:
        raise ValueError('private bootstrap changed')
    for name, digest in actual.items():
        pinned(private / name, digest)
    return raw, runtime


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--private-root', type=Path, required=True)
    parser.add_argument('--generate', action='store_true')
    parser.add_argument('--runtime-provenance', type=Path)
    parser.add_argument('--runtime-sha256')
    parser.add_argument('--report', type=Path)
    parser.add_argument('--checker', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    private = args.private_root.resolve(strict=True)
    if not str(private).startswith('/private/tmp/'):
        raise ValueError('this regression is restricted to a private temporary copy')
    manifest, files = plan(private)
    if args.generate:
        materialize(HERE, manifest, files)
    validate_materialized(HERE, manifest, files)
    if not args.checker:
        print(json.dumps({'baselines': len(manifest['baselines']), 'cases': len(manifest['cases']),
                          'fixed_environment_sha256': FIXED_ENV_SHA}, sort_keys=True))
        return 0
    if not args.runtime_provenance or not args.runtime_sha256 or not args.report:
        raise ValueError('execution requires pinned READY provenance and a new report')
    report_path = args.report.resolve()
    if report_path.parent != HERE or report_path.exists() or report_path.suffix != '.json':
        raise ValueError('report must be a new top-level JSON file in p2_fix')
    raw, runtime = check_runtime(private, args.runtime_provenance, args.runtime_sha256)
    i = args.checker.index('--socket') + 1
    if args.checker[i:i + 1] != [runtime['startup']['socket']]:
        raise ValueError('socket and startup provenance disagree')
    watches = [Path(__file__), ROOT / 'scripts/test_metadata_mutations.py', ROOT / 'scripts/test_arena.py',
               args.runtime_provenance, private / 'scripts/hol-check.py', private / 'hol/environment.ml']
    with checker_snapshot(args.checker, None, watches) as (command, identities):
        report = run_suite(manifest, HERE, command, 25, 4096)
    if plan(private) != (manifest, files):
        raise ValueError('private inputs or fixtures changed during replay')
    validate_materialized(HERE, manifest, files)
    check_runtime(private, args.runtime_provenance, args.runtime_sha256)
    report.update(finished_at=utc_now(), checker_identity=identities, valid=identities['unchanged'],
                  review_snapshot_sha256=REVIEW_SHA, fixed_environment_sha256=FIXED_ENV_SHA,
                  runtime_provenance_sha256=sha(raw), runtime_startup=runtime['startup'],
                  runtime_note='Frozen indexed checkpoint plus only the flags rewrite-list change; no later production changes.')
    report['observed_codes'] = {group: dict(Counter(str(c.get('exit_code')) for c in report[group]))
                                for group in ('baselines', 'cases')}
    if not report['valid']:
        report['summary'].update(covered=0, complete=False)
    with report_path.open('x') as stream:
        json.dump(report, stream, indent=2, sort_keys=True)
        stream.write('\n')
    with (HERE / 'fixed-startup-provenance.json').open('xb') as stream:
        stream.write(raw)
    print(json.dumps(report['summary'], sort_keys=True))
    return 3 if not report['valid'] else 1 if report['summary']['failures'] else 0 if report['summary']['complete'] else 2


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError) as error:
        print('private audit fault: ' + str(error), file=sys.stderr)
        sys.exit(3)
