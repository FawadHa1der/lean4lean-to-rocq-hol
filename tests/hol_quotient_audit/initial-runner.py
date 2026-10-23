#!/usr/bin/env python3
"""Pinned quotient export audit. Offline generation never invokes a checker."""

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
SNAPSHOT_SHA = 'eb4dfadc04f3b5dfa79ddad8f6a218cb5aacd22a3a349a9756d113a4ae607964'


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
sys.path.insert(0, str(SNAPSHOT / 'scripts'))
spec = importlib.util.spec_from_file_location(
    'quotient_pinned_builder', SNAPSHOT / 'tests/hol_indexed_audit/witnesses.py')
builder = importlib.util.module_from_spec(spec)
spec.loader.exec_module(builder)
from test_metadata_mutations import (materialize, validate_materialized, ndjson_bytes,
                                     json_bytes, checker_snapshot, classify, summarize)
from test_arena import run_process, utc_now

Wire, V, S, C, A, bind = builder.Wire, builder.V, builder.S, builder.C, builder.A, builder.bind
ZERO, ONE = builder.ZERO, builder.ONE
U, VLEVEL = ('param', 'u'), ('param', 'v')
UPSTREAM = 'vendor/lean4lean/Lean4Lean/Quot.lean'


def seed_rows(seed):
    raw = (SNAPSHOT / 'arena' / seed['path']).read_bytes()
    if sha(raw) != seed['sha256'] or len(raw) != seed['size']:
        raise ValueError('seed differs from Arena pin')
    return builder.rows_of(raw), raw


def anonymous_binders(rows):
    rows = copy.deepcopy(rows)
    for row in rows:
        for tag in ('lam', 'forallE'):
            if tag in row:
                row[tag]['name'] = 0
    return rows


def header_mutation(rows, kind, mode):
    wire = Wire(rows)
    h = next(r['quot'] for r in wire.decls if 'quot' in r and r['quot']['kind'] == kind)
    if mode == 'fresh-name':
        h['name'] = wire.name('QuotientAudit.NotCanonical.' + kind)
    elif mode == 'wrong-kind':
        h['kind'] = {'type': 'ctor', 'ctor': 'lift', 'lift': 'ind', 'ind': 'type'}[kind]
    elif mode == 'missing-universe':
        h['levelParams'] = h['levelParams'][:-1]
    elif mode == 'extra-universe':
        h['levelParams'].append(wire.name('audit_extra_universe'))
    elif mode == 'signature-sort':
        h['type'] = wire.expr(S(ZERO))
    elif mode == 'first-domain-prop':
        h['type'] = wire.replace(h['type'], [('forallE', 'type')], wire.expr(S(ZERO)))
    elif mode == 'dotted-single-name':
        assert kind == 'ctor'
        h['name'] = wire.name(('Quot.mk',))
    elif mode == 'duplicate-universes':
        assert kind == 'lift'
        h['levelParams'][1] = h['levelParams'][0]
    elif mode == 'swapped-universes':
        assert kind == 'lift'
        h['levelParams'].reverse()
    elif mode == 'unknown-kind':
        h['kind'] = 'not-a-quotient-kind'
    else:
        raise ValueError('unknown header mutation')
    return wire.finish()


def rename_name(rows, old, new):
    wire = Wire(rows)
    index = wire.name(old)
    row = next(r for r in wire.rows if r.get('in') == index)
    row['str']['str'] = new
    return wire.finish()


def rename_universes(rows):
    rows = copy.deepcopy(rows)
    params = {r['param'] for r in rows if 'il' in r and 'param' in r}
    for row in rows:
        if row.get('in') in params:
            assert row['str']['pre'] == 0
            row['str']['str'] = 'audit_universe_' + str(row['in'])
    return rows


def equality_variant(rows, mode='canonical', include_quot=False):
    """Rebuild Eq coherently; noncanonical variants have their own dependency gates."""
    wire = Wire(rows)
    eq = next(r['inductive'] for r in wire.decls if 'inductive' in r)
    wire.decls = [r for r in wire.decls if 'quot' in r] if include_quot else []
    universe, elim = ('param', 'u_1'), U
    a_type, a, b = V('A'), V('a'), V('b')
    pars = [('A', S(universe)), ('a', a_type)]
    fam = lambda x: A(C('Eq', [universe]), a_type, a, x)
    fields = [('b', a_type)] if mode == 'any-constructor' else []
    result_index = b if fields else a
    constructor = A(C('Eq.refl', [universe]), a_type, a, *([b] if fields else []))
    motive = bind('forallE', [('b', a_type), ('proof', fam(b))], S(elim))
    minor = bind('forallE', fields, A(V('motive'), result_index, constructor))
    recpars = pars + [('motive', motive), ('minor', minor)]
    rectype = bind('forallE', recpars + [('b', a_type), ('proof', fam(b))],
                   A(V('motive'), b, V('proof')))
    rhs = bind('lam', recpars + fields, A(V('minor'), b) if fields else V('minor'))
    i, c, r = copy.deepcopy(eq['types'][0]), copy.deepcopy(eq['ctors'][0]), copy.deepcopy(eq['recs'][0])
    i['type'] = wire.expr(bind('forallE', pars + [('b', a_type)], S(ONE if mode == 'type-valued' else ZERO)))
    c.update(type=wire.expr(bind('forallE', pars + fields, fam(result_index))), numFields=len(fields))
    r.update(type=wire.expr(rectype), k=(mode == 'canonical'),
             rules=[{'ctor': c['name'], 'nfields': len(fields), 'rhs': wire.expr(rhs)}])
    wire.decls.insert(0, {'inductive': {'types': [i], 'ctors': [c], 'recs': [r]}})
    return wire.finish()


def reduction(rows, kind, mode='canonical'):
    """Named-variable reconstruction of genuine 130/131 theorem telescopes."""
    wire = Wire(rows)
    h = next(r['thm'] for r in reversed(wire.decls) if 'thm' in r)
    alpha, rel, beta, branch, x = V('A'), V('r'), V('B'), V('f'), V('x')
    relation = bind('forallE', [('a', alpha), ('b', alpha)], S(ZERO))
    quotient = lambda r: A(C('Quot', [U]), alpha, r)
    mk = lambda r, a, us=(U,): A(C('Quot.mk', us), alpha, r, a)
    params = [('A', S(U)), ('r', relation)]
    if kind == 'lift':
        respect = bind('forallE', [('a', alpha), ('b', alpha), ('hr', A(rel, V('a'), V('b')))],
                       A(C('Eq', [VLEVEL]), beta, A(branch, V('a')), A(branch, V('b'))))
        params += [('B', S(VLEVEL)), ('f', bind('forallE', [('a', alpha)], beta)), ('respect', respect)]
    else:
        params += [('B', bind('forallE', [('q', quotient(rel))], S(ZERO))),
                   ('f', bind('forallE', [('a', alpha)], A(beta, mk(rel, V('a')))))]
    params.append(('x', alpha))
    major = mk(rel, x)
    rhs = A(branch, x)
    result_type = beta if kind == 'lift' else A(beta, major)
    if mode == 'beta-major':
        major = A(bind('lam', [('q', quotient(rel))], V('q')), major)
    elif mode == 'wrong-relation':
        params.append(('s', relation))
        major = mk(V('s'), x)
    elif mode == 'wrong-constructor':
        major = A(C('Eq.refl', [U]), alpha, x)
    elif mode == 'wrong-universe':
        major = mk(rel, x, [VLEVEL if kind == 'lift' else ('succ', U)])
    elif mode == 'wrong-representative':
        assert kind == 'lift'
        params.append(('bad', beta))
        major = mk(rel, V('bad'))
    elif mode == 'overapplied-constructor':
        major = A(major, x)
    elif mode == 'missing-constructor-argument':
        major = A(C('Quot.mk', [U]), alpha, rel)
    elif mode == 'wrong-result':
        params.append(('other', alpha))
        rhs = A(branch, V('other'))
    elif mode == 'neutral-major-proof-control':
        assert kind == 'ind'
        params += [('q', quotient(rel)), ('hq', A(beta, V('q')))]
        major, result_type, rhs = V('q'), A(beta, V('q')), V('hq')
    elif mode != 'canonical':
        raise ValueError('unknown reduction mutation')
    if kind == 'lift':
        lhs = A(C('Quot.lift', [U, VLEVEL]), alpha, rel, beta, branch, V('respect'), major)
        equality_level = VLEVEL
    else:
        lhs = A(C('Quot.ind', [U]), alpha, rel, beta, branch, major)
        equality_level = ZERO
    h['type'] = wire.expr(bind('forallE', params, A(C('Eq', [equality_level]), result_type, lhs, rhs)))
    h['value'] = wire.expr(bind('lam', params, A(C('Eq.refl', [equality_level]), result_type, lhs)))
    return wire.finish()


def plan():
    verify_snapshot()
    manifest = {'version': 1, 'suite': 'hol-quotient-audit', 'review_snapshot_sha256': SNAPSHOT_SHA,
                'upstream_revision': PINS['upstream_revision'],
                'scope': 'Export-claim integrity and typing/reduction witnesses; not a soundness/completeness proof.',
                'header_contract_note': 'Upstream Replay regenerates quotDecl without comparing every quotInfo payload; forged-header expectations concern the explicit local exported-claim integrity contract.',
                'baseline_policy': 'All listed prerequisite gates must return 0 before a case runs; 2 is a gap, never refutation.',
                'baselines': [], 'cases': []}
    files = {}

    def add(family, label, rows, expected, dimension, rationale, seed, baseline=False, raw=None, basis='typing', requires=None):
        data = raw if raw is not None else ndjson_bytes(rows)
        path = ('baselines/' + family if baseline else 'cases/' + family + '/' + label) + '.ndjson'
        entry = {'id': family if baseline else family + '/' + label, 'family': family,
                 'path': path, 'sha256': sha(data), 'size': len(data), 'seed': seed['id'],
                 'seed_sha256': seed['sha256'], 'dimension': dimension, 'rationale': rationale,
                 'expectation_basis': basis, 'upstream': UPSTREAM,
                 'requires': requires or [family]}
        if not baseline:
            entry['expected'] = expected
        manifest['baselines' if baseline else 'cases'].append(entry)
        files[path] = data

    for seed in PINS['seeds']:
        rows, raw = seed_rows(seed)
        family = Path(seed['path']).name[:3]
        add(family, '', rows, 'accept', 'gate', 'Complete byte-identical actual Arena export. 129 retains its explicit Quot.sound object-axiom assumption.', seed, True, raw)
        add(family, 'unchanged', rows, 'accept', 'control', 'Exact baseline bytes.', seed, raw=raw, basis='transport')
        add(family, 'anonymous-binders', anonymous_binders(rows), 'accept', 'control',
            'Only binder display names change; de Bruijn indices, universe identities and declaration claims are unchanged.', seed, basis='transport')
        tables = [r for r in rows if any(k in r for k in ('meta', 'in', 'il', 'ie'))]
        decls = [r for r in rows if not any(k in r for k in ('meta', 'in', 'il', 'ie'))]
        add(family, 'forward-declarations', tables + list(reversed(decls)), 'accept', 'control',
            'Identical expression DAG and declarations in reverse order; implicit Eq prerequisite must still be scheduled.', seed, basis='transport')
        if family == '126':
            reasons = {
                'fresh-name': 'Claimed primitive name differs from the canonical structural name for this kind.',
                'wrong-kind': 'Name/signature are unchanged but the known quotient-kind tag is inconsistent.',
                'missing-universe': 'One required formal universe is missing from the kind-specific header.',
                'extra-universe': 'A fresh extra formal universe changes the canonical arity.',
                'signature-sort': 'A closed Sort replaces the entire canonical function signature.',
                'first-domain-prop': 'Only the first domain becomes Prop instead of Sort u; this is not the canonical universe-polymorphic signature.'}
            for kind in ('type', 'ctor', 'lift', 'ind'):
                for mode, reason in reasons.items():
                    add(family, kind + '-' + mode, header_mutation(rows, kind, mode), 'reject', 'header',
                        reason + ' This is a forged export claim, not an assertion that upstream Replay rejects the ignored payload.', seed, basis='claim-integrity')
            for kind, mode, reason, basis in (
                ('ctor', 'dotted-single-name', 'One root string Quot.mk is not the structural name Quot/mk.', 'claim-integrity'),
                ('lift', 'duplicate-universes', 'Two formal universe slots must be distinct; duplicated u cannot bind independent input and output levels.', 'claim-integrity'),
                ('lift', 'swapped-universes', 'Only the formal list order is reversed; the signature still uses the previous input/output roles.', 'claim-integrity'),
                ('type', 'unknown-kind', 'Unknown discriminator is malformed quotient metadata, not a new logical kind.', 'malformed')):
                add(family, kind + '-' + mode, header_mutation(rows, kind, mode), 'reject', 'header', reason, seed, basis=basis)
            add(family, 'eq-missing', [r for r in rows if 'inductive' not in r], 'reject', 'eq-prerequisite',
                'No Eq declaration remains. Upstream checkEqType requires an authenticated inductive Eq before quotient initialization.', seed)
            add(family, 'eq-coherently-renamed', rename_name(rows, 'Eq', 'AuditEquality'), 'reject', 'eq-prerequisite',
                'The complete equality family and references are coherently renamed; exact reserved Eq is absent.', seed)
            add(family, 'eq-constructor-renamed', rename_name(rows, 'Eq.refl', 'introduction'), 'accept', 'eq-prerequisite',
                'The listed reflexivity constructor is coherently renamed. Upstream checkEqType follows the sole constructor entry and checks its type, not the spelling Eq.refl.', seed)
            add(family, 'universe-alpha-renamed', rename_universes(rows), 'accept', 'control',
                'All universe parameter names and references are coherently renamed, preserving ordered binder roles.', seed, basis='transport')
            for mode in ('any-constructor', 'type-valued'):
                gate = 'eq-' + mode
                add(gate, '', equality_variant(rows, mode), 'accept', 'gate',
                    'Independently well-formed indexed family named Eq: ' +
                    ('one constructor for every index, with generated one-field recursor.' if mode == 'any-constructor' else 'reflexive equality-shaped family in Type, not Prop, with K=false.') +
                    ' Must itself accept before testing the quotient prerequisite.', seed, True)
                add(gate, 'quotient-prerequisite', equality_variant(rows, mode, True), 'reject', 'eq-prerequisite',
                    ('The sole constructor has an extra index field; it is not forall A a, Eq A a a.' if mode == 'any-constructor' else
                     'The inductive returns Sort 1 instead of Prop; it is not the Eq type required by checkEqType.') +
                    ' Both the genuine quotient gate and this altered dependency gate are required.', seed, requires=['126', gate])
        if family in ('130', '131'):
            kind = 'lift' if family == '130' else 'ind'
            modes = [('canonical', 'accept', 'Named-variable reconstruction canonically matches the genuine exported theorem.'),
                     ('beta-major', 'accept', 'An identity beta-redex wraps the constructor major; weak-head reduction exposes the same constructor.'),
                     ('wrong-relation', 'reject', 'Major has type Quot A s, while the eliminator requires Quot A r; r and s are independent variables.'),
                     ('wrong-constructor', 'reject', 'Eq.refl A x is an equality proof, not a Quot A r major.'),
                     ('wrong-universe', 'reject', 'Constructor is instantiated at an incompatible universe while the carrier remains Sort u.'),
                     ('wrong-result', 'reject', 'An unrelated representative changes the claimed result; lift has no equality premise between representatives, and ind has a different dependent proposition.')]
            if kind == 'lift':
                modes += [('wrong-representative', 'reject', 'A B-valued variable is supplied as the A-valued constructor representative; A and B are arbitrary independent types.'),
                          ('overapplied-constructor', 'reject', 'A quotient value is applied as a function; its type is Quot A r, not a function type.')]
            else:
                modes += [('missing-constructor-argument', 'reject', 'Partial Quot.mk A r has function type, not the required quotient-major type.'),
                          ('neutral-major-proof-control', 'accept', 'A neutral q and hq : B q are used; both endpoints are proofs of the same proposition, so proof irrelevance permits equality without quotient computation.')]
            for mode, expected, reason in modes:
                add(family, mode, reduction(rows, kind, mode), expected, 'reduction', reason, seed,
                    basis='proof-irrelevance' if mode == 'neutral-major-proof-control' else 'typing-reduction')
    assert len(manifest['cases']) == 68 and len(manifest['baselines']) == 8
    return manifest, files


def run_suite(manifest, directory, command, timeout, execute=run_process):
    def run(path):
        try:
            return execute(command + [str(path)], path, timeout, 'file', 4096)
        except OSError as exc:
            return {'exit_code': None, 'timed_out': False, 'execution_error': str(exc)}
    baselines, cases, gates = [], [], {}
    for entry in manifest['baselines']:
        result = run(directory / entry['path'])
        accepted = result.get('exit_code') == 0 and not result.get('timed_out')
        gates[entry['family']] = accepted
        baselines.append({'id': entry['id'], 'family': entry['family'], 'sha256': entry['sha256'],
                          **result, 'status': 'accepted' if accepted else 'not_covered'})
    for entry in manifest['cases']:
        record = {k: entry[k] for k in ('id', 'family', 'sha256', 'expected', 'dimension', 'expectation_basis', 'requires')}
        missing = [g for g in entry['requires'] if not gates[g]]
        if missing:
            cases.append({**record, 'exit_code': None, 'status': 'not_covered', 'failed_gates': missing})
            continue
        result = run(directory / entry['path'])
        status = 'execution_error' if 'execution_error' in result else classify(result, entry['expected'])
        cases.append({**record, **result, 'status': status})
    return {'baselines': baselines, 'cases': cases, 'summary': summarize(baselines, cases)}


def runtime_comparison(path, digest):
    raw = path.read_bytes()
    if sha(raw) != digest:
        raise ValueError('runtime provenance hash mismatch')
    r = json.loads(raw)
    snap, start = r['snapshot'], r['startup']
    encoded = (json.dumps(snap, sort_keys=True, ensure_ascii=True, separators=(',', ':')) + '\n').encode('ascii')
    if (r['kind'] != 'hol-runner-startup-provenance' or r['scope'] != 'project-inputs-only'
            or not all(v == sha(encoded) for v in (r['snapshot_sha256'], start['before_snapshot_sha256'], start['ready_snapshot_sha256']))
            or start['comparison'] != 'before-launch-and-at-ready-identical'):
        raise ValueError('runtime provenance self-integrity mismatch')
    def inputs(s):
        result = {e['path']: (e['sha256'], e['size_bytes']) for e in s['inputs']}
        if len(result) != len(s['inputs']):
            raise ValueError('duplicate provenance inputs')
        return result
    actual, reviewed = inputs(snap), inputs(PINS['project'])
    differences = [{'path': p, 'review': reviewed.get(p), 'runtime': actual.get(p)}
                   for p in sorted(actual.keys() | reviewed.keys()) if actual.get(p) != reviewed.get(p)]
    bootstrap = snap['bootstrap'] == PINS['project']['bootstrap']
    return {'manifest_sha256': digest, 'socket': start['socket'], 'differences': differences,
            'matches_review': not differences and bootstrap, 'bootstrap_matches': bootstrap,
            'limitations': r['limitations']}


def atomic_report(path, record):
    path = path.absolute()
    if path.exists() or path.is_symlink():
        raise ValueError('report exists; refusing overwrite')
    data = json_bytes(record)
    if len(data) > 4 * 1024 * 1024:
        raise ValueError('report exceeds bound')
    fd, temp = tempfile.mkstemp(prefix='.quotient-audit-', dir=path.parent)
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
    p.add_argument('--timeout', type=float, default=40)
    p.add_argument('--checker', nargs=argparse.REMAINDER)
    args = p.parse_args(argv)
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        p.error('timeout must be finite and positive')
    manifest, files = plan()
    directory = args.suite_dir.resolve()
    if args.generate:
        materialize(directory, manifest, files)
    else:
        validate_materialized(directory, manifest, files)
    if not args.run:
        print(json.dumps({'baselines': len(manifest['baselines']), 'cases': len(manifest['cases']),
                          'manifest_sha256': sha(json_bytes(manifest)), 'runtime_calls': 0}))
        return 0
    if not all((args.checker, args.report, args.runtime_provenance, args.runtime_sha256)):
        p.error('run requires checker, new report path, and runtime provenance/hash')
    if args.report.exists() or args.report.is_symlink():
        p.error('report already exists')
    runtime = runtime_comparison(args.runtime_provenance, args.runtime_sha256)
    if not runtime['matches_review'] and not args.allow_distinct_snapshot:
        p.error('runtime differs from review; --allow-distinct-snapshot acknowledgement required')
    if '--socket' in args.checker:
        at = args.checker.index('--socket')
        if args.checker[at + 1:at + 2] != [runtime['socket']]:
            p.error('socket differs from READY provenance')
    watched = [Path(__file__), SNAPSHOT / 'manifest.json', args.runtime_provenance] + args.watch_file
    watched += [Path(a) for a in args.checker if Path(a).is_file()]
    def execute(command, *rest):
        result = run_process(command, *rest)
        print(json.dumps({'file': Path(command[-1]).name, 'exit_code': result.get('exit_code'),
                          'elapsed_seconds': result.get('elapsed_seconds')}), flush=True)
        return result
    with checker_snapshot(args.checker, None, watched) as (command, identity):
        result = run_suite(manifest, directory, command, args.timeout, execute=execute)
    validate_materialized(directory, manifest, files)
    verify_snapshot()
    result.update(finished_at=utc_now(), runtime=runtime, checker=identity,
                  review_snapshot_sha256=SNAPSHOT_SHA, manifest_sha256=sha(json_bytes(manifest)),
                  limitations=['Declines are coverage gaps, not refutations.', manifest['header_contract_note'],
                               'Acceptance of 129 is relative to its explicit Quot.sound object-axiom policy.'])
    atomic_report(args.report, result)
    print(json.dumps(result['summary'], sort_keys=True))
    return 1 if result['summary']['failures'] or not identity['unchanged'] else (2 if not result['summary']['complete'] else 0)


if __name__ == '__main__':
    raise SystemExit(main())
