#!/usr/bin/env python3
"""Bounded, baseline-gated projection witnesses. Generation never calls a checker."""

import argparse
import copy
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SNAPSHOT = HERE / 'snapshot'
SNAPSHOT_SHA = '49ade84203d704cf207c1594456063af963469dead7eab076e3f30c91f930200'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def verify_snapshot():
    data = (SNAPSHOT / 'manifest.json').read_bytes()
    if sha(data) != SNAPSHOT_SHA:
        raise ValueError('review snapshot manifest changed')
    record = json.loads(data)
    for entry in record['files']:
        path = SNAPSHOT / entry['path']
        if path.is_symlink() or SNAPSHOT not in path.resolve().parents:
            raise ValueError('unsafe snapshot path')
        data = path.read_bytes()
        if sha(data) != entry['sha256'] or len(data) != entry['size']:
            raise ValueError('snapshot input changed: ' + entry['path'])
    return record


PINS = verify_snapshot()
# Reuse the frozen test-only DAG builder and harness, never checker verdicts.
sys.path.insert(0, str(SNAPSHOT / 'scripts'))
spec = importlib.util.spec_from_file_location(
    'projection_pinned_builder', SNAPSHOT / 'tests/hol_indexed_audit/witnesses.py')
builder = importlib.util.module_from_spec(spec)
spec.loader.exec_module(builder)
from test_metadata_mutations import (materialize, validate_materialized, ndjson_bytes,
                                     json_bytes, run_suite, checker_snapshot)
from test_arena import utc_now

V, S, C, A, bind = builder.V, builder.S, builder.C, builder.A, builder.bind
ZERO, ONE = builder.ZERO, builder.ONE


class Wire(builder.Wire):
    def expr(self, term, context=()):
        if term[0] == 'proj':
            return self.raw({'proj': {'typeName': self.name(term[1]), 'idx': term[2],
                                      'struct': self.expr(term[3], context)}})
        return super().expr(term, context)


def proj(owner, index, major):
    return ('proj', owner, index, major)


def seed_rows(seed):
    data = (SNAPSHOT / 'arena' / seed['path']).read_bytes()
    if sha(data) != seed['sha256'] or len(data) != seed['size']:
        raise ValueError('baseline differs from Arena pin')
    return builder.rows_of(data), data


def projection_edit(rows, name, mode):
    wire = Wire(rows)
    header = next(h for row in wire.decls for tag, h in row.items()
                  if tag in ('def', 'thm') and h['name'] == wire.name(name))
    root, path = header['value'], []
    node = root
    while 'lam' in wire.expressions[node]:
        path.append(('lam', 'body'))
        node = wire.expressions[node]['lam']['body']
    payload = copy.deepcopy(wire.expressions[node])
    p = payload['proj']
    block = next(row['inductive'] for row in wire.decls if 'inductive' in row
                 and any(t['name'] == p['typeName'] for t in row['inductive']['types']))
    ctor = next(c for c in block['ctors'] if c['induct'] == p['typeName'])
    if mode == 'owner-constructor':
        p['typeName'] = ctor['name']
    elif mode == 'owner-unknown':
        p['typeName'] = wire.name('ProjectionAudit.AbsentOwner')
    elif mode == 'index-boundary':
        p['idx'] = ctor['numFields']
    elif mode == 'index-swapped':
        assert p['idx'] == 1 and ctor['numFields'] == 2
        p['idx'] = 0
    elif mode == 'major-sort':
        p['struct'] = wire.expr(S(ZERO))
    else:
        raise ValueError('unknown mutation mode')
    header['value'] = wire.replace(root, path, wire.raw(payload))
    return wire.finish()


def binder_control(rows):
    rows = copy.deepcopy(rows)
    for row in rows:
        for tag in ('lam', 'forallE'):
            if tag in row:
                row[tag]['name'] = 0
    return rows


def prop_variant(rows, index, proof=ZERO, data=ONE):
    wire = Wire(rows)
    h = next(row['def'] for row in reversed(wire.decls) if 'def' in row)
    major = C('PropStructure', [proof, data])
    result = C('PUnit', [data if index in (1, 3) else proof])
    params = [('x', major)]
    levels = sorted({u[1] for u in (proof, data) if u[0] == 'param'})
    h['levelParams'] = [wire.name(n) for n in levels]
    h['type'] = wire.expr(bind('forallE', params, result))
    h['value'] = wire.expr(bind('lam', params, proj('PropStructure', index, V('x'))))
    return wire.finish()


def dependent_computation(rows, mode='control'):
    wire = Wire(rows)
    a, b = V('A'), V('B')
    params = [('A', S(ONE)), ('B', bind('forallE', [('x', a)], S(ONE))),
              ('a', a), ('other', a), ('b', A(b, V('a'))), ('otherb', A(b, V('other')))]
    first = V('other') if mode in ('wrong-first-field', 'coherent-other') else V('a')
    second = V('otherb') if mode in ('wrong-dependent-field', 'coherent-other') else V('b')
    result = V('other') if mode in ('wrong-result-index', 'coherent-other') else V('a')
    major = A(C('PSigma.mk', [ONE, ONE]), a, b, first, second)
    wire.definition('ProjectionAudit.dependent', [],
                    bind('forallE', params, A(b, result)),
                    bind('lam', params, proj('PSigma', 1, major)))
    return wire.finish()


def reduction_variant(rows, mode):
    wire = Wire(rows)
    h = next(row['def'] for row in reversed(wire.decls) if 'def' in row)
    boolean, yes, no = C('Bool'), C('Bool.true'), C('Bool.false')
    fields = (no, yes) if mode == 'swapped-constructor-fields' else (yes, no)
    major = A(C('Prod.mk', [ZERO, ZERO]), boolean, boolean, *fields)
    redex = proj('Prod', 0 if mode == 'first-index' else 1, major)
    result = yes if mode == 'wrong-result' else no
    h['type'] = wire.expr(A(C('Eq', [ONE]), boolean, redex, result))
    h['value'] = wire.expr(A(C('Eq.refl', [ONE]), boolean, redex))
    return wire.finish()


TARGETS = {'083': 'And.right', '084': 'Prod.snd', '085': 'PProd.snd',
           '086': 'PSigma.snd', '089': 'projProp1', '091': 'projProp3', '098': 'Prod.snd'}
UPSTREAM = 'vendor/lean4lean/Lean4Lean/TypeChecker.lean'


def plan():
    verify_snapshot()
    manifest = {'version': 1, 'suite': 'hol-projection-audit',
                'review_snapshot_sha256': SNAPSHOT_SHA,
                'upstream_revision': PINS['upstream_revision'],
                'scope': 'Bounded export witnesses, not a soundness or completeness proof.',
                'baseline_policy': 'A family must first return 0; code 2 is always a coverage gap.',
                'baselines': [], 'cases': []}
    files = {}

    def add(family, label, rows, expected, dimension, rationale, seed, baseline=False, raw=None):
        data = raw if raw is not None else ndjson_bytes(rows)
        path = ('baselines/' + family if baseline else 'cases/' + family + '/' + label) + '.ndjson'
        entry = {'id': family if baseline else family + '/' + label, 'family': family,
                 'path': path, 'sha256': sha(data), 'size': len(data), 'seed': seed['id'],
                 'seed_sha256': seed['sha256'], 'dimension': dimension, 'rationale': rationale,
                 'upstream': UPSTREAM + (':343-351' if dimension == 'reduction' else ':233-260')}
        if not baseline:
            entry['expected'] = expected
        manifest['baselines' if baseline else 'cases'].append(entry)
        files[path] = data

    for seed in PINS['seeds']:
        rows, raw = seed_rows(seed)
        family = Path(seed['path']).name[:3]
        add(family, '', rows, 'accept', 'gate', 'Complete unmodified actual Arena export.', seed, True, raw)
        add(family, 'unchanged', rows, 'accept', 'control', 'Exact baseline bytes replayed independently.', seed, raw=raw)
        add(family, 'anonymous-binders', binder_control(rows), 'accept', 'transport',
            'Only binder display names become anonymous; all de Bruijn indices and metadata are unchanged.', seed)
        tables = [r for r in rows if any(k in r for k in ('meta', 'in', 'il', 'ie'))]
        decls = [r for r in rows if not any(k in r for k in ('meta', 'in', 'il', 'ie'))]
        add(family, 'forward-declarations', tables + list(reversed(decls)), 'accept', 'transport',
            'Identical DAG and declarations; dependency replay must resolve declarations listed in reverse order.', seed)
        for mode, reason in (
            ('owner-constructor', 'Projection owner is now its constructor name, not the inductive head of the unchanged major type.'),
            ('owner-unknown', 'Fresh undeclared owner differs from the unchanged major type; declaration and expression DAG remain otherwise intact.'),
            ('index-boundary', 'Index equals the constructor field count, the first index outside its telescope.'),
            ('major-sort', 'Major becomes Sort 0, whose type is a sort rather than an application of the stated owner.')):
            add(family, mode, projection_edit(rows, TARGETS[family], mode), 'reject',
                mode.split('-')[0], reason, seed)
        if family in ('083', '084', '085', '086'):
            add(family, 'index-swapped', projection_edit(rows, TARGETS[family], 'index-swapped'),
                'reject', 'index', 'Second projection is replaced by first but the polymorphic result type is unchanged; distinct arbitrary parameters (or B (fst x)) are not convertible.', seed)
        if family in ('089', '091'):
            other = 2 if family == '089' else 0
            variants = [
                ('other-independent-proof', other, ZERO, ONE, 'accept', 'Fields 0 and 2 both have type PUnit.0; field 1 is data but unused in the remaining telescope.'),
                ('direct-data', 1, ZERO, ONE, 'reject', 'The result type is coherently PUnit.1, isolating forbidden data extraction from a Prop structure.'),
                ('dependent-skip', 5, ZERO, ONE, 'reject', 'The selected field is a proof, but skipped field 3 is PUnit.1 data used by the equality type of field 4.'),
                ('all-prop-final', 5, ZERO, ZERO, 'accept', 'Both universes are zero, so even the skipped dependent field 3 is a proof.'),
                ('maybe-data-independent', 2, ZERO, ('param', 'projection_v'), 'accept', 'An arbitrary-universe data field can be skipped when unused; the selected field 2 is always a proof.'),
                ('maybe-data-dependent', 5, ZERO, ('param', 'projection_v'), 'reject', 'The dependent skipped field is not always Prop; valuation projection_v=1 witnesses the forbidden branch.'),
                ('maybe-proof-selected', 0, ('param', 'projection_u'), ONE, 'reject', 'The selected field is PUnit.u and is not always Prop; valuation u=1 forbids its projection from Prop.')]
            for label, index, u, v, expected, reason in variants:
                add(family, label, prop_variant(rows, index, u, v), expected, 'prop-universe', reason, seed)
        if family == '086':
            derived = '086-dependent'
            add(derived, '', dependent_computation(rows), 'accept', 'gate',
                'Genuine PSigma export plus a typed snd (mk A B a b) : B a declaration; the extra derivation must itself accept.', seed, True)
            reasons = {'control': ('accept', 'Unchanged derived constructor-reduction gate.'),
                       'wrong-dependent-field': ('reject', 'mk A B a otherb supplies otherb : B other where B a is required; a and other are arbitrary distinct variables.'),
                       'wrong-first-field': ('reject', 'mk A B other b supplies b : B a where B other is required.'),
                       'wrong-result-index': ('reject', 'snd (mk A B a b) has type B a, not the claimed B other.'),
                       'coherent-other': ('accept', 'First field, dependent second field, and claimed result all consistently use other; guards must not reject all changes.')}
            for mode, (expected, reason) in reasons.items():
                add(derived, mode, dependent_computation(rows, mode), expected, 'dependent-field', reason, seed)
        if family == '098':
            for mode, expected, reason in (
                ('direct', 'accept', 'Replace the snd wrapper with a direct projection and rfl wrapper with Eq.refl; snd (true,false) reduces to false.'),
                ('first-index', 'reject', 'First projection reduces to Bool.true but the claimed right endpoint remains Bool.false.'),
                ('swapped-constructor-fields', 'reject', 'Swapping the constructor fields makes snd reduce to true; right endpoint stays false.'),
                ('wrong-result', 'reject', 'snd still reduces to false, but the claimed right endpoint is true; proof irrelevance cannot identify propositions of different types.')):
                add(family, 'reduction-' + mode, reduction_variant(rows, mode), expected, 'reduction', reason, seed)
    assert len(manifest['baselines']) == 8 and len(manifest['cases']) == 76
    return manifest, files


def runtime_comparison(path, expected_hash):
    raw = path.read_bytes()
    if sha(raw) != expected_hash:
        raise ValueError('runtime provenance hash mismatch')
    runtime = json.loads(raw)
    snapshot = runtime['snapshot']
    encoded = (json.dumps(snapshot, sort_keys=True, ensure_ascii=True, separators=(',', ':')) + '\n').encode('ascii')
    digest = sha(encoded)
    startup = runtime['startup']
    if (runtime['kind'] != 'hol-runner-startup-provenance'
            or runtime['scope'] != 'project-inputs-only'
            or digest != runtime['snapshot_sha256']
            or digest != startup['before_snapshot_sha256']
            or digest != startup['ready_snapshot_sha256']
            or startup['comparison'] != 'before-launch-and-at-ready-identical'):
        raise ValueError('runtime provenance self-integrity mismatch')
    def inputs(s):
        values = {e['path']: (e['sha256'], e['size_bytes']) for e in s['inputs']}
        if len(values) != len(s['inputs']):
            raise ValueError('duplicate provenance inputs')
        return values
    actual, reviewed = inputs(snapshot), inputs(PINS['project'])
    differences = [{'path': p, 'review': reviewed.get(p), 'runtime': actual.get(p)}
                   for p in sorted(actual.keys() | reviewed.keys()) if actual.get(p) != reviewed.get(p)]
    bootstrap_matches = snapshot['bootstrap'] == PINS['project']['bootstrap']
    return {'manifest_sha256': expected_hash, 'socket': startup['socket'],
            'matches_review': not differences and bootstrap_matches,
            'bootstrap_matches': bootstrap_matches, 'differences': differences,
            'limitations': runtime['limitations']}


def atomic_report(path, record):
    path = path.absolute()
    if path.exists() or path.is_symlink():
        raise ValueError('report exists; refusing overwrite')
    data = json_bytes(record)
    if len(data) > 4 * 1024 * 1024:
        raise ValueError('report too large')
    fd, temp = tempfile.mkstemp(prefix='.projection-report-', dir=path.parent)
    try:
        with os.fdopen(fd, 'wb') as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.link(temp, path)
    finally:
        os.unlink(temp)


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    actions = p.add_mutually_exclusive_group(required=True)
    for flag in ('generate', 'verify', 'run'):
        actions.add_argument('--' + flag, action='store_true')
    p.add_argument('--suite-dir', type=Path, default=HERE / 'fixtures')
    p.add_argument('--report', type=Path)
    p.add_argument('--runtime-provenance', type=Path)
    p.add_argument('--runtime-sha256')
    p.add_argument('--allow-distinct-snapshot', action='store_true')
    p.add_argument('--watch-file', type=Path, action='append', default=[])
    p.add_argument('--timeout', type=float, default=20)
    p.add_argument('--checker', nargs=argparse.REMAINDER)
    args = p.parse_args(argv)
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        p.error('timeout must be finite and positive')
    manifest, files = plan()
    suite = args.suite_dir.resolve()
    if args.generate:
        materialize(suite, manifest, files)
    else:
        validate_materialized(suite, manifest, files)
    if not args.run:
        print(json.dumps({'baselines': len(manifest['baselines']), 'cases': len(manifest['cases']),
                          'manifest_sha256': sha(json_bytes(manifest)), 'runtime_calls': 0}))
        return 0
    if not args.checker or not args.report or not args.runtime_provenance or not args.runtime_sha256:
        p.error('--run requires --checker, --report, --runtime-provenance and --runtime-sha256')
    if args.report.exists() or args.report.is_symlink():
        p.error('report exists; refusing overwrite')
    runtime = runtime_comparison(args.runtime_provenance, args.runtime_sha256)
    if not runtime['matches_review'] and not args.allow_distinct_snapshot:
        p.error('loaded runtime differs from review; explicit --allow-distinct-snapshot required')
    if '--socket' in args.checker:
        at = args.checker.index('--socket')
        if args.checker[at + 1:at + 2] != [runtime['socket']]:
            p.error('checker socket differs from READY provenance')
    watched = [Path(__file__), SNAPSHOT / 'manifest.json', args.runtime_provenance] + args.watch_file
    watched += [Path(a) for a in args.checker if Path(a).is_file()]
    with checker_snapshot(args.checker, None, watched) as (command, identity):
        result = run_suite(manifest, suite, command, args.timeout, 4096)
    validate_materialized(suite, manifest, files)
    verify_snapshot()
    result.update(finished_at=utc_now(), runtime=runtime, checker=identity,
                  review_snapshot_sha256=SNAPSHOT_SHA, manifest_sha256=sha(json_bytes(manifest)),
                  limitations=['Declines and timeouts are gaps, not refutations.',
                               'Source review and startup hashes do not attest runtime or semantics.'])
    atomic_report(args.report, result)
    print(json.dumps(result['summary'], sort_keys=True))
    return 1 if result['summary']['failures'] or not identity['unchanged'] else (2 if not result['summary']['complete'] else 0)


if __name__ == '__main__':
    raise SystemExit(main())
