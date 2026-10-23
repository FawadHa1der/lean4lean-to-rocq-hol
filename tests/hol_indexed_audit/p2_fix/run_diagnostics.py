#!/usr/bin/env python3
"""Three bounded, observation-only Arena probes; no expected verdicts or oracle."""

import argparse
import json
from pathlib import Path
import sys

import run_targeted as target
from test_arena import run_process, utc_now
from test_metadata_mutations import checker_snapshot

PINS = [
    {'id': 'tutorial/071_rbTreeRef', 'path': 'corpus/tutorial/071_rbTreeRef.ndjson', 'size': 16556,
     'sha256': '2c88f371f5859df7de86e51fe52fc85d9be7fb242ad61ef0d4155b1263812ab6'},
    {'id': 'tutorial/077_sortElimProp2Rec', 'path': 'corpus/tutorial/077_sortElimProp2Rec.ndjson', 'size': 6794,
     'sha256': 'eaaa3909ab1527239fa0373e392464e6941097162531033d9a7ad422e7cb9945'},
    {'id': 'tutorial/082_RBTree.id_spec', 'path': 'corpus/tutorial/082_RBTree.id_spec.ndjson', 'size': 49017,
     'sha256': '88349328dd81100fb22396180bef9b5c2b0997275b7c3c672b19a7ac87ed72f9'},
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--private-root', type=Path, required=True)
    parser.add_argument('--runtime-provenance', type=Path, required=True)
    parser.add_argument('--runtime-sha256', required=True)
    parser.add_argument('--checker', nargs=argparse.REMAINDER, required=True)
    args = parser.parse_args()
    private = args.private_root.resolve(strict=True)
    target.plan(private)
    raw, runtime = target.check_runtime(private, args.runtime_provenance, args.runtime_sha256)
    i = args.checker.index('--socket') + 1
    if args.checker[i:i + 1] != [runtime['startup']['socket']]:
        raise ValueError('socket differs from fixed READY provenance')
    directory = target.HERE / 'diagnostics'
    directory.mkdir(exist_ok=True)
    if (directory / 'report.json').exists():
        raise ValueError('refusing to overwrite diagnostic report')
    files = []
    for pin in PINS:
        if pin['size'] > 65536:
            raise ValueError('diagnostic source exceeds 64 KiB')
        raw = target.pinned(target.ROOT / 'arena' / pin['path'], pin['sha256'])
        if len(raw) != pin['size']:
            raise ValueError('diagnostic source size differs')
        path = directory / Path(pin['path']).name
        with path.open('xb') as stream:
            stream.write(raw)
        files.append(path)
    watches = [Path(__file__), target.HERE / 'run_targeted.py', target.ROOT / 'scripts/test_arena.py',
               target.ROOT / 'scripts/test_metadata_mutations.py', args.runtime_provenance,
               private / 'scripts/hol-check.py', private / 'hol/environment.ml'] + files
    with checker_snapshot(args.checker, None, watches) as (command, identities):
        observations = [{**pin, **run_process(command + [str(path)], path, 25, 'file', 4096)}
                        for pin, path in zip(PINS, files)]
    target.plan(private)
    target.check_runtime(private, args.runtime_provenance, args.runtime_sha256)
    report = {'finished_at': utc_now(), 'observations': observations, 'checker_identity': identities,
              'valid': identities['unchanged'], 'runtime_provenance_sha256': args.runtime_sha256,
              'fixed_environment_sha256': target.FIXED_ENV_SHA,
              'note': 'Observation only on the frozen indexed checkpoint plus flags fix; no later K or projection code, no expected verdicts, no pass/fail classification.'}
    with (directory / 'report.json').open('x') as stream:
        json.dump(report, stream, indent=2, sort_keys=True)
        stream.write('\n')
    print(json.dumps([{'id': r['id'], 'code': r['exit_code'], 'seconds': r['elapsed_seconds'],
                       'diagnostic': r['stderr']} for r in observations], indent=2))
    return 0 if report['valid'] else 3


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError) as error:
        print('private diagnostic fault: ' + str(error), file=sys.stderr)
        sys.exit(3)
