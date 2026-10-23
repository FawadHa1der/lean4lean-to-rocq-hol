#!/usr/bin/env python3
"""Frozen-checkpoint converter regression with separately labelled RBTree observations."""

import argparse
from collections import Counter
import difflib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
AUDIT = HERE.parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(AUDIT / 'p2_fix'))
import run_targeted as p2
from test_metadata_mutations import materialize, validate_materialized, run_suite, checker_snapshot
from test_arena import run_process, utc_now

ENV_SHA = '91fa4b30e5a385dd4fb6ead82dc7c0cabaa9bac66341fa5b8bf90d623f87a3da'
OLD = '        mem (fst(dest_const h)) ["l4_vars";"l4_decimal_aux";"l4_fresh_univ_aux"] &&'
NEW = '''        mem (fst(dest_const h),List.length args)
          ["l4_vars",2;"l4_decimal_aux",2;"l4_fresh_univ_aux",3] &&'''
PINS = [
    {'id': 'tutorial/071_rbTreeRef', 'name': '071_rbTreeRef.ndjson',
     'sha256': '2c88f371f5859df7de86e51fe52fc85d9be7fb242ad61ef0d4155b1263812ab6'},
    {'id': 'tutorial/082_RBTree.id_spec', 'name': '082_RBTree.id_spec.ndjson',
     'sha256': '88349328dd81100fb22396180bef9b5c2b0997275b7c3c672b19a7ac87ed72f9'},
]


def plan(private):
    snapshot = json.loads(p2.pinned(AUDIT / 'snapshot/manifest.json', p2.REVIEW_SHA))
    reviewed = (AUDIT / 'snapshot/hol/environment.ml').read_text()
    base = reviewed.replace(p2.OLD, p2.NEW, 1)
    fixed = base.replace(OLD, NEW, 1)
    if base.count(OLD) != 1 or p2.sha(base.encode()) != p2.FIXED_ENV_SHA or p2.sha(fixed.encode()) != ENV_SHA:
        raise ValueError('exact converter patch/source pin mismatch')
    for e in snapshot['inputs']:
        p2.pinned(AUDIT / 'snapshot' / e['path'], e['sha256'])
        p2.pinned(private / e['path'], ENV_SHA if e['path'] == 'hol/environment.ml' else e['sha256'])
    if (private / 'hol/environment.ml').read_text() != fixed:
        raise ValueError('unexpected private source change')
    previous = json.loads((AUDIT / 'p2_fix/manifest.json').read_bytes())
    source = json.loads(p2.pinned(AUDIT / 'manifest.json', p2.SOURCE_MANIFEST_SHA))
    if previous['baselines'] != source['baselines'] or previous['cases'] != [c for c in source['cases'] if c['id'] in p2.CASE_IDS]:
        raise ValueError('prior fixture selection changed')
    manifest = {'version': 1, 'suite': 'hol-rbtree-converter-private-v1', 'review_manifest_sha256': p2.REVIEW_SHA,
                'environment_sha256': ENV_SHA, 'base_environment_sha256': p2.FIXED_ENV_SHA,
                'baselines': previous['baselines'].copy(), 'cases': previous['cases'], 'observations': PINS}
    files = {e['path']: p2.pinned(AUDIT / e['path'], e['sha256']) for e in manifest['baselines'] + manifest['cases']}
    for pin in PINS:
        raw = p2.pinned(AUDIT / 'p2_fix/diagnostics' / pin['name'], pin['sha256'])
        if len(raw) > 65536:
            raise ValueError('diagnostic input exceeds 64 KiB')
        files['observations/' + pin['name']] = raw
    # Shared prefix ends with the RBTree declaration, before either file's later definitions.
    prefix = files['observations/071_rbTreeRef.ndjson'].splitlines(keepends=True)[:294]
    other = files['observations/082_RBTree.id_spec.ndjson'].splitlines(keepends=True)[:294]
    if prefix != other or 'inductive' not in json.loads(prefix[-1]):
        raise ValueError('genuine shared RBTree admission prefix changed')
    raw = b''.join(prefix)
    path = 'baselines/rbtree-admission.ndjson'
    files[path] = raw
    manifest['baselines'].append({'id': 'baseline/rbtree-admission', 'family': 'rbtree-admission',
                                  'path': path, 'size': len(raw), 'sha256': p2.sha(raw),
                                  'derivation': 'Identical first 294 lines of pinned 071 and 082, through the complete RBTree block.'})
    files['converter.patch'] = ''.join(difflib.unified_diff(base.splitlines(True), fixed.splitlines(True),
                                                          fromfile='a/hol/environment.ml', tofile='b/hol/environment.ml')).encode()
    return manifest, files


def runtime(private, path, digest):
    raw = p2.pinned(path, digest)
    value = json.loads(raw)
    original = json.loads(p2.pinned(AUDIT / 'indexed-startup-provenance.json', p2.ORIGINAL_READY_SHA))
    expected = {e['path']: e['sha256'] for e in original['snapshot']['inputs']}
    expected['hol/environment.ml'] = ENV_SHA
    inputs = value['snapshot']['inputs']
    if len(inputs) != len(expected) or {e['path']: e['sha256'] for e in inputs} != expected:
        raise ValueError('runtime closure differs from frozen checkpoint plus the two proof-search patches')
    if Path(value['snapshot']['project_root']) != private or value['snapshot']['bootstrap'] != original['snapshot']['bootstrap']:
        raise ValueError('runtime root/bootstrap mismatch')
    for name, sha in expected.items():
        p2.pinned(private / name, sha)
    return raw, value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--private-root', type=Path, required=True)
    parser.add_argument('--generate', action='store_true')
    parser.add_argument('--runtime-provenance', type=Path)
    parser.add_argument('--runtime-sha256')
    parser.add_argument('--checker', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    private = args.private_root.resolve(strict=True)
    if not str(private).startswith('/private/tmp/'):
        raise ValueError('only private temporary copies are allowed')
    manifest, files = plan(private)
    if args.generate:
        materialize(HERE, manifest, files)
    validate_materialized(HERE, manifest, files)
    if not args.checker:
        print(json.dumps({'baselines': len(manifest['baselines']), 'cases': len(manifest['cases']), 'observations': len(PINS)}))
        return 0
    if (HERE / 'report.json').exists() or (HERE / 'startup-provenance.json').exists():
        raise ValueError('refusing to overwrite runtime evidence')
    raw, identity = runtime(private, args.runtime_provenance, args.runtime_sha256)
    i = args.checker.index('--socket') + 1
    if args.checker[i:i + 1] != [identity['startup']['socket']]:
        raise ValueError('wrong private socket')
    watches = [Path(__file__), Path(p2.__file__), ROOT / 'scripts/test_metadata_mutations.py',
               ROOT / 'scripts/test_arena.py', args.runtime_provenance,
               private / 'scripts/hol-check.py', private / 'hol/environment.ml']
    with checker_snapshot(args.checker, None, watches) as (command, ids):
        report = run_suite(manifest, HERE, command, 45, 4096)
        report['observations'] = [{**pin, **run_process(command + [str(HERE / 'observations' / pin['name'])],
                                  HERE / 'observations' / pin['name'], 45, 'file', 4096)} for pin in PINS]
    if plan(private) != (manifest, files):
        raise ValueError('source or fixture inputs changed')
    validate_materialized(HERE, manifest, files)
    runtime(private, args.runtime_provenance, args.runtime_sha256)
    report.update(finished_at=utc_now(), valid=ids['unchanged'], checker_identity=ids,
                  runtime_provenance_sha256=args.runtime_sha256, runtime_startup=identity['startup'],
                  fixed_environment_sha256=ENV_SHA,
                  observation_note='071/082 are diagnostic observations without expected-verdict or pass/fail labels; 077 is not run.')
    report['observed_codes'] = {g: dict(Counter(str(c.get('exit_code')) for c in report[g])) for g in ('baselines', 'cases', 'observations')}
    if not report['valid']:
        report['summary'].update(covered=0, complete=False)
    with (HERE / 'report.json').open('x') as stream:
        json.dump(report, stream, indent=2, sort_keys=True)
        stream.write('\n')
    with (HERE / 'startup-provenance.json').open('xb') as stream:
        stream.write(raw)
    print(json.dumps({'summary': report['summary'], 'observed_codes': report['observed_codes'], 'valid': report['valid']}, indent=2))
    return 3 if not report['valid'] else 1 if report['summary']['failures'] else 0 if report['summary']['complete'] else 2


if __name__ == '__main__':
    sys.exit(main())
