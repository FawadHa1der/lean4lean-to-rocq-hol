#!/usr/bin/env python3
"""Bounded valid 078/079 probes: declaration gates, original theorem, u=0 specialization."""

import argparse
import copy
import json
from pathlib import Path

import projection_audit as suite
from test_arena import run_process, utc_now

PINS = {
    '078_boolRecEqns': '4fc92c213242a1fadda56ef895988f4407df5fbb495805eb565e76c794ebe92d',
    '079_prodRecEqns': 'f6d9afec199974f6658dfd9609b5eb6256ef562d6ab9ee1c8899620314d233a6'}


def specialize(rows):
    wire = suite.Wire(rows)
    h = wire.decls[-1]['thm']
    assert len(h['levelParams']) == 1
    parameter = h['levelParams'][0]
    levels = {r['il']: {k: v for k, v in r.items() if k != 'il'} for r in wire.rows if 'il' in r}

    def level(n):
        if n == 0:
            return suite.ZERO
        p = levels[n]
        if 'param' in p:
            assert p['param'] == parameter
            return suite.ZERO
        if 'succ' in p:
            return ('succ', level(p['succ']))
        tag = 'max' if 'max' in p else 'imax'
        return (tag, *(level(v) for v in p[tag]))

    cache = {}
    def expr(n):
        if n in cache:
            return cache[n]
        p = copy.deepcopy(wire.expressions[n])
        if 'sort' in p:
            p['sort'] = wire.level(level(p['sort']))
        elif 'const' in p:
            p['const']['us'] = [wire.level(level(u)) for u in p['const']['us']]
        elif 'app' in p:
            p['app'] = {k: expr(v) for k, v in p['app'].items()}
        elif 'proj' in p:
            p['proj']['struct'] = expr(p['proj']['struct'])
        elif 'bvar' not in p:
            tag = next(t for t in ('lam', 'forallE') if t in p)
            for k in ('type', 'body'):
                p[tag][k] = expr(p[tag][k])
        cache[n] = wire.raw(p)
        return cache[n]

    h['type'], h['value'] = expr(h['type']), expr(h['value'])
    h['levelParams'] = []
    return wire.finish()


def plan():
    source = suite.ROOT / 'arena/manifest.json'
    manifest = {'version': 1, 'kind': 'projection-adjacent-valid-recursor-probes',
                'arena_manifest_sha256': suite.sha(source.read_bytes()),
                'baselines': [], 'cases': []}
    entries = json.loads(source.read_bytes())['cases']
    files = {}
    for name, digest in PINS.items():
        seed = next(e for e in entries if e['id'] == 'tutorial/' + name)
        assert seed['sha256'] == digest
        raw = (suite.ROOT / 'arena' / seed['path']).read_bytes()
        assert suite.sha(raw) == digest and len(raw) == seed['size']
        rows = suite.builder.rows_of(raw)
        assert 'thm' in rows[-1]
        for label, data, baseline, rationale in (
            ('declarations', suite.ndjson_bytes(rows[:-1]), True,
             'All original rows except the final theorem; complete exported declaration blocks must first accept.'),
            ('original', raw, False, 'Complete SHA-pinned actual Arena export, unchanged.'),
            ('universe-zero', suite.ndjson_bytes(specialize(rows)), False,
             'Only the final theorem is coherently specialized at universe zero; inductive and recursor declarations are byte-structurally unchanged.')):
            path = ('baselines/' if baseline else 'cases/') + name + '-' + label + '.ndjson'
            item = {'id': name + '/' + label, 'family': name, 'path': path,
                    'sha256': suite.sha(data), 'size': len(data), 'seed_sha256': digest,
                    'rationale': rationale, 'dimension': 'valid-recursor-diagnostic'}
            if not baseline:
                item['expected'] = 'accept'
            manifest['baselines' if baseline else 'cases'].append(item)
            files[path] = data
    return manifest, files


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--generate', action='store_true')
    p.add_argument('--run', action='store_true')
    p.add_argument('--runtime-provenance', type=Path)
    p.add_argument('--runtime-sha256')
    p.add_argument('--report', type=Path)
    p.add_argument('--checker', nargs=argparse.REMAINDER)
    args = p.parse_args()
    manifest, files = plan()
    directory = suite.HERE / 'recursor_probes'
    if args.generate:
        suite.materialize(directory, manifest, files)
    suite.validate_materialized(directory, manifest, files)
    if not args.run:
        print(json.dumps({'gates': 2, 'probes': 4, 'runtime_calls': 0}))
        return 0
    if not all((args.report, args.runtime_provenance, args.runtime_sha256, args.checker)):
        p.error('run needs report, runtime provenance/hash, and checker')
    if args.report.exists() or args.report.is_symlink():
        p.error('report exists')
    runtime = suite.runtime_comparison(args.runtime_provenance, args.runtime_sha256)
    at = args.checker.index('--socket')
    if args.checker[at + 1] != runtime['socket']:
        p.error('socket differs from provenance')
    watched = [Path(__file__), Path(suite.__file__), args.runtime_provenance]
    watched += [Path(a) for a in args.checker if Path(a).is_file()]
    def execute(command, *rest):
        result = run_process(command, *rest)
        print(json.dumps({'file': Path(command[-1]).name, **result}), flush=True)
        return result
    with suite.checker_snapshot(args.checker, None, watched) as (command, identity):
        result = suite.run_suite(manifest, directory, command, 40, 4096, execute=execute)
    suite.validate_materialized(directory, manifest, files)
    result.update(runtime=runtime, checker=identity, finished_at=utc_now(),
                  manifest_sha256=suite.sha(suite.json_bytes(manifest)))
    suite.atomic_report(args.report, result)
    print(json.dumps(result['summary']))
    return 1 if result['summary']['failures'] or not identity['unchanged'] else (2 if not result['summary']['complete'] else 0)


if __name__ == '__main__':
    raise SystemExit(main())
