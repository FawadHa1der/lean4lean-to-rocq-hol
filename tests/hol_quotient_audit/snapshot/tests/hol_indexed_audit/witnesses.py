#!/usr/bin/env python3
"""Pinned export mutations for the indexed HOL review; generation is offline."""

import argparse
from collections import Counter
import copy
import hashlib
import json
import math
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
SNAPSHOT_SHA = '7677c7e691c7a42884b0ff7e97577960615396e6d8bfeddb62fba5988c2003fa'
sys.path.insert(0, str(ROOT / 'scripts'))
from test_metadata_mutations import (materialize, validate_materialized, ndjson_bytes,
                                     run_suite, checker_snapshot)
from test_arena import utc_now


def sha(data):
    return hashlib.sha256(data).hexdigest()


def rows_of(data):
    return [json.loads(line) for line in data.splitlines() if line.strip()]


def tables_first(rows):
    return ([r for r in rows if any(k in r for k in ('meta', 'in', 'il', 'ie'))]
            + [r for r in rows if not any(k in r for k in ('meta', 'in', 'il', 'ie'))])


def admission_only(rows):
    return [copy.deepcopy(r) for r in rows
            if any(k in r for k in ('meta', 'in', 'il', 'ie', 'inductive'))]


def blocks(rows):
    return [r['inductive'] for r in rows if 'inductive' in r]


def V(name):
    return ('var', name)


def S(level):
    return ('sort', level)


def C(name, levels=()):
    return ('const', name, tuple(levels))


def A(fn, *args):
    for arg in args:
        fn = ('app', fn, arg)
    return fn


def bind(tag, pars, body):
    for name, typ in reversed(pars):
        body = (tag, name, typ, body)
    return body


ZERO = ('zero',)
ONE = ('succ', ZERO)
U = ('param', 'u')


class Wire:
    """Append-only expression interner; edits copy paths, never shared DAG nodes."""

    def __init__(self, rows):
        ordered = tables_first(copy.deepcopy(rows))
        self.rows = [r for r in ordered if any(k in r for k in ('meta', 'in', 'il', 'ie'))]
        self.decls = [r for r in ordered if not any(k in r for k in ('meta', 'in', 'il', 'ie'))]
        self.names = {(): 0}
        decoded = {0: ()}
        self.levels = {json.dumps({'zero': True}, sort_keys=True): 0}
        self.exprs, self.expressions = {}, {}
        for r in self.rows:
            if 'in' in r:
                p = r.get('str', r.get('num'))
                atom = p['str'] if 'str' in r else p['i']
                decoded[r['in']] = decoded[p['pre']] + (atom,)
                self.names[decoded[r['in']]] = r['in']
            elif 'il' in r:
                self.levels[json.dumps({k: v for k, v in r.items() if k != 'il'}, sort_keys=True)] = r['il']
            elif 'ie' in r:
                body = {k: v for k, v in r.items() if k != 'ie'}
                self.exprs[json.dumps(body, sort_keys=True)] = r['ie']
                self.expressions[r['ie']] = body
        self.next_name = max(decoded) + 1
        self.next_level = max([r.get('il', 0) for r in self.rows]) + 1
        self.next_expr = max(self.expressions, default=-1) + 1

    def finish(self):
        return self.rows + self.decls

    def name(self, text):
        parts = tuple(text.split('.')) if isinstance(text, str) else tuple(text)
        if parts not in self.names:
            pre = self.name(parts[:-1])
            index = self.next_name
            self.next_name += 1
            atom = parts[-1]
            tag, payload = ('num', {'pre': pre, 'i': atom}) if isinstance(atom, int) else (
                'str', {'pre': pre, 'str': atom})
            self.names[parts] = index
            self.rows.append({'in': index, tag: payload})
        return self.names[parts]

    def level(self, term):
        if term == ZERO:
            return 0
        tag = term[0]
        if tag == 'param':
            value = self.name(term[1])
        elif tag == 'succ':
            value = self.level(term[1])
        else:
            value = [self.level(t) for t in term[1:]]
        payload = {tag: value}
        key = json.dumps(payload, sort_keys=True)
        if key not in self.levels:
            self.levels[key] = self.next_level
            self.rows.append({'il': self.next_level, **payload})
            self.next_level += 1
        return self.levels[key]

    def raw(self, payload):
        key = json.dumps(payload, sort_keys=True)
        if key not in self.exprs:
            self.exprs[key] = self.next_expr
            self.expressions[self.next_expr] = payload
            self.rows.append({'ie': self.next_expr, **payload})
            self.next_expr += 1
        return self.exprs[key]

    def expr(self, term, context=()):
        tag = term[0]
        if tag == 'var':
            payload = {'bvar': context.index(term[1])}
        elif tag == 'raw-var':
            payload = {'bvar': term[1]}
        elif tag == 'sort':
            payload = {'sort': self.level(term[1])}
        elif tag == 'const':
            payload = {'const': {'name': self.name(term[1]), 'us': [self.level(u) for u in term[2]]}}
        elif tag == 'app':
            payload = {'app': {'fn': self.expr(term[1], context), 'arg': self.expr(term[2], context)}}
        else:
            if tag not in ('forallE', 'lam'):
                raise ValueError('unsupported named term: ' + tag)
            payload = {tag: {'name': self.name(term[1]), 'type': self.expr(term[2], context),
                             'body': self.expr(term[3], (term[1],) + context), 'binderInfo': 'default'}}
        return self.raw(payload)

    def replace(self, root, path, replacement):
        if not path:
            return replacement
        tag, field = path[0]
        body = copy.deepcopy(self.expressions[root])
        body[tag][field] = self.replace(body[tag][field], path[1:], replacement)
        return self.raw(body)

    def definition(self, name, pars, typ, value):
        n = self.name(name)
        self.decls.append({'def': {'name': n, 'levelParams': [self.name(p) for p in pars],
                                  'type': self.expr(typ), 'value': self.expr(value),
                                  'all': [n], 'hints': 'opaque', 'safety': 'safe'}})


def sort_elim_variant(source, result_kind='swapped', large=True, k=False):
    """Rebuild the genuine SortElimProp block via named variables, not HOL formulas."""
    wire = Wire(admission_only(source))
    wire.decls.pop()  # Keep the exported Bool dependency, replace only SortElimProp.
    b, x, y = V('b'), V('x'), V('y')
    boolean = C('Bool')
    if result_kind == 'swapped':
        result = [y, x]
    elif result_kind == 'in-order':
        result = [x, y]
    elif result_kind == 'hidden':
        result = [y, y]
    elif result_kind == 'nested-only':
        result = [y, A(bind('lam', [('z', boolean)], V('z')), x)]
    else:
        raise ValueError('unknown result-index variant')
    pars, inds, fields = [('b', boolean)], [('i', boolean), ('j', boolean)], [('x', boolean), ('y', boolean)]
    family = lambda indices: A(C('SortElimProp'), b, *indices)
    elim = U if large else ZERO
    motive = bind('forallE', inds + [('major', family([V('i'), V('j')]))], S(elim))
    ctor = A(C('SortElimProp.mk'), b, x, y)
    minor = bind('forallE', fields, A(V('motive'), *result, ctor))
    recpars = pars + [('motive', motive), ('minor', minor)]
    rectype = bind('forallE', recpars + inds + [('major', family([V('i'), V('j')]))],
                   A(V('motive'), V('i'), V('j'), V('major')))
    rhs = bind('lam', recpars + fields, A(V('minor'), x, y))
    n, c, r = [wire.name(n) for n in ('SortElimProp', 'SortElimProp.mk', 'SortElimProp.rec')]
    block = {'types': [{'name': n, 'levelParams': [], 'type': wire.expr(bind('forallE', pars + inds, S(ZERO))),
                        'all': [n], 'ctors': [c], 'numParams': 1, 'numIndices': 2, 'numNested': 0,
                        'isRec': False, 'isReflexive': False, 'isUnsafe': False}],
             'ctors': [{'name': c, 'levelParams': [], 'type': wire.expr(bind('forallE', pars + fields, family(result))),
                        'induct': n, 'cidx': 0, 'numParams': 1, 'numFields': 2, 'isUnsafe': False}],
             'recs': [{'name': r, 'levelParams': [wire.name('u')] if large else [], 'type': wire.expr(rectype),
                       'all': [n], 'numParams': 1, 'numIndices': 2, 'numMotives': 1, 'numMinors': 1,
                       'k': k, 'isUnsafe': False, 'rules': [{'ctor': c, 'nfields': 2, 'rhs': wire.expr(rhs)}]}]}
    wire.decls.append({'inductive': block})
    return wire.finish()


def iota(source, family, mutation=None):
    wire = Wire(admission_only(source))
    a_type, a = V('A'), V('a')
    pars = [('A', S(ONE)), ('a', a_type)]
    if family == 'eq':
        major = A(C('Eq.refl', [ONE]), a_type, a)
        motive = bind('lam', [('index', a_type), ('proof', A(C('Eq', [ONE]), a_type, a, V('index')))], a_type)
        index = a
        if mutation == 'wrong-index':
            pars.append(('other', a_type))
            index = V('other')
        reduction = A(C('Eq.rec', [ONE, ONE]), a_type, a, motive, a, index, major)
    elif family == 'psigma':
        b_type = bind('forallE', [('x', a_type)], S(ONE))
        pars += [('B', b_type), ('b', A(V('B'), a))]
        major = A(C('PSigma.mk', [ONE, ONE]), a_type, V('B'), a, V('b'))
        motive = bind('lam', [('major', A(C('PSigma', [ONE, ONE]), a_type, V('B')))], a_type)
        minor = bind('lam', [('x', a_type), ('y', A(V('B'), V('x')))], V('x'))
        if mutation == 'wrong-dependent-field':
            pars += [('other', a_type), ('otherb', A(V('B'), V('other')))]
            major = A(C('PSigma.mk', [ONE, ONE]), a_type, V('B'), a, V('otherb'))
        reduction = A(C('PSigma.rec', [ONE, ONE, ONE]), a_type, V('B'), motive, minor, major)
    else:
        raise ValueError('unknown iota family')
    witness = a
    if mutation == 'wrong-result':
        pars.append(('other', a_type))
        witness = V('other')
    pars += [('P', bind('forallE', [('x', a_type)], S(ONE))), ('h', A(V('P'), witness))]
    wire.definition('IndexedAudit.' + family + 'Iota', [],
                    bind('forallE', pars, A(V('P'), reduction)), bind('lam', pars, V('h')))
    return wire.finish()


def snapshot():
    raw = (HERE / 'snapshot/manifest.json').read_bytes()
    if sha(raw) != SNAPSHOT_SHA:
        raise ValueError('review manifest pin mismatch')
    manifest = json.loads(raw)
    for e in manifest['inputs']:
        p = HERE / 'snapshot' / e['path']
        if p.is_symlink() or len(p.read_bytes()) != e['size_bytes'] or sha(p.read_bytes()) != e['sha256']:
            raise ValueError('review snapshot changed: ' + e['path'])
    return manifest


def runtime_comparison(raw):
    runtime = json.loads(raw)
    reviewed = {e['path']: e['sha256'] for e in snapshot()['inputs']}
    entries = runtime['snapshot']['inputs']
    differences = [e['path'] for e in entries if reviewed.get(e['path']) != e['sha256']]
    return {'runtime_provenance_sha256': sha(raw), 'review_snapshot_sha256': SNAPSHOT_SHA,
            'compared_inputs': len(entries), 'different_or_missing_inputs': differences,
            'all_runtime_project_inputs_match_review': not differences,
            'scope': 'Project-file hashes only, not runtime state or semantic attestation.'}


def plan():
    snap = snapshot()
    pins = {p['id']: p for p in snap['arena_source_pins']}
    source = {}
    for family, case_id in [('eq', 'tutorial/043_eqType'), ('psigma', 'tutorial/086_PSigma.snd'),
                            ('sortelim', 'tutorial/076_sortElimPropRec'), ('proof-field', 'tutorial/095_projDataIndexRec')]:
        pin = pins[case_id]
        raw = (HERE / 'snapshot/arena' / pin['path']).read_bytes()
        if len(raw) != pin['size'] or sha(raw) != pin['sha256']:
            raise ValueError('seed pin mismatch')
        source[family] = rows_of(raw)
    bases = {f: rows for f, rows in source.items()}
    bases['psigma'] = admission_only(source['psigma'])
    bases['eq-iota'] = iota(source['eq'], 'eq')
    bases['psigma-iota'] = iota(source['psigma'], 'psigma')
    bases['sortelim-coherent'] = sort_elim_variant(source['sortelim'])
    manifest = {'suite': 'hol-indexed-audit-v1', 'version': 1,
                'snapshot_manifest_sha256': SNAPSHOT_SHA, 'source_pins': list(pins.values()),
                'baselines': [], 'cases': [],
                'limitations': ['Declines are gaps, never successful rejections.',
                                'Targeted stale-claim mutations do not isolate every logical premise.',
                                'No checker or exporter is run to select expected verdicts.']}
    files = {}
    for family, rows in bases.items():
        raw = ndjson_bytes(rows)
        path = 'baselines/' + family + '.ndjson'
        files[path] = raw
        derivation = ('Exported inductive blocks, projection definitions removed.' if family == 'psigma' else
                      'Exported blocks plus an independently written named-term iota witness.' if family.endswith('-iota') else
                      'Named-term reconstruction, statically compared with exported metadata modulo binder names.'
                      if family == 'sortelim-coherent' else 'All original exported rows, JSON canonicalized only.')
        manifest['baselines'].append({'id': 'baseline/' + family, 'family': family, 'path': path,
                                      'sha256': sha(raw), 'size': len(raw), 'derivation': derivation})

    def add(family, label, rows, expected, dimension, rationale, coherent=False):
        raw = ndjson_bytes(rows)
        path = 'cases/' + family + '/' + label + '.ndjson'
        if path in files or raw == ndjson_bytes(bases[family]):
            raise ValueError('duplicate path or ineffective mutation: ' + path)
        files[path] = raw
        manifest['cases'].append({'id': family + '/' + label, 'family': family, 'path': path,
                                  'sha256': sha(raw), 'size': len(raw), 'expected': expected,
                                  'dimension': dimension, 'rationale': rationale, 'coherent_claims': coherent,
                                  'baseline_sha256': sha(ndjson_bytes(bases[family]))})

    for family in ('eq', 'psigma', 'sortelim', 'proof-field'):
        rows = copy.deepcopy(bases[family])
        for row in rows:
            for tag in ('forallE', 'lam'):
                if tag in row:
                    row[tag]['name'] = 0
                    row[tag]['binderInfo'] = 'default'
        add(family, 'binder-control', rows, 'accept', 'transport', 'Binder display names and binderInfo are ignored.', True)
        rows = tables_first(copy.deepcopy(bases[family]))
        tables = [r for r in rows if any(k in r for k in ('meta', 'in', 'il', 'ie'))]
        decls = [r for r in rows if not any(k in r for k in ('meta', 'in', 'il', 'ie'))]
        if len(decls) > 1:
            add(family, 'forward-declaration-control', tables + list(reversed(decls)), 'accept', 'replay-order',
                'The whole declaration stream is reversed; replay must schedule actual dependencies.', True)
        rows = copy.deepcopy(bases[family])
        subject = blocks(rows)[-1]['types'][0]['name']
        for row in rows:
            if row.get('in') == subject:
                row['str']['str'] = 'IndexedAudit' + row['str']['str']
        add(family, 'source-name-control', rows, 'accept', 'transport',
            'Structural parent renaming updates every reference through the name table.', True)
        for label, mutation, rationale in (
            ('forged-k', lambda b: b['recs'][0].__setitem__('k', not b['recs'][0]['k']),
             'Upstream isKTarget requires Prop, one constructor, and no fields beyond parameters; proof fields still count.'),
            ('wrong-index-count', lambda b: b['recs'][0].__setitem__('numIndices', b['recs'][0]['numIndices'] + 1),
             'Recursor index count must equal the generated telescope, not arbitrary supplied metadata.'),
            ('missing-rule', lambda b: b['recs'][0]['rules'].clear(), 'Generated recursor rules are required.'),
            ('duplicate-rule', lambda b: b['recs'][0]['rules'].append(copy.deepcopy(b['recs'][0]['rules'][0])),
             'Extra rule membership is not allowed by exact ordered metadata comparison.'),
            ('duplicate-ctor-claim', lambda b: b['ctors'].append(copy.deepcopy(b['ctors'][0])),
             'Claims must be distinct and have exactly the generated length.'),
            ('missing-ctor-claim', lambda b: b['ctors'].clear(), 'A missing generated constructor is not a permitted subset.'),
            ('wrong-all', lambda b: b['recs'][0].__setitem__('all', []), 'The claimed mutual family must exactly match generation.'),
        ):
            rows = copy.deepcopy(bases[family])
            mutation(blocks(rows)[-1])
            add(family, label, rows, 'reject', 'metadata', rationale)

    # Copy only the selected constructor/type path; leave every other table use intact.
    field_mutations = [
        ('snd-captures-parameter', ('raw-var', 1), 'Second field B a is changed to parameter B, which is not itself a type.'),
        ('snd-captures-field', ('app', ('raw-var', 1), ('raw-var', 1)), 'B is applied to B rather than the preceding a : A.'),
        ('snd-captures-type', ('app', ('raw-var', 1), ('raw-var', 2)), 'B is applied to A rather than the preceding a : A.'),
        ('snd-out-of-context', ('raw-var', 3), 'Only A, B, a exist before the second field; index 3 is out of scope.'),
        ('negative-self-field', bind('forallE', [('bad', A(C('PSigma', [('param', 'u'), ('param', 'v')]),
                                                         ('raw-var', 2), ('raw-var', 1)))], ('raw-var', 3)),
         'A function domain contains the new family negatively; its codomain is the existing parameter A.'),
        ('current-ctor-field', C('PSigma.mk', [('param', 'u'), ('param', 'v')]),
         'Current-block constructors are unavailable during field formation, even though present in the final generated environment.'),
        ('current-recursor-field', C('PSigma.rec', [ONE, ('param', 'u'), ('param', 'v')]),
         'The new recursor must not be used to bootstrap field formation.'),
    ]
    for label, term, reason in field_mutations:
        wire = Wire(bases['psigma'])
        ctor = blocks(wire.decls)[-1]['ctors'][0]
        ctor['type'] = wire.replace(ctor['type'], [('forallE', 'body')] * 3 + [('forallE', 'type')], wire.expr(term))
        add('psigma', label, wire.finish(), 'reject', 'dependent-field-context', reason)
    for label, role, depth, term, reason in (
        ('header-current-ctor', 'types', 0, C('Eq.refl', [('param', 'u_1')]), 'Headers are formed in the prior environment, before any generated entry.'),
        ('header-current-recursor', 'types', 0, C('Eq.rec', [ONE, ('param', 'u_1')]), 'Full generated-environment formation cannot replace prior header formation.'),
        ('ctor-parameter-prefix', 'ctors', 1, S(ONE), 'The supplied constructor parameter prefix differs from the header; candidate extraction must not discard it.'),
        ('index-context-overflow', 'types', 2, ('raw-var', 2), 'At the index binder only A and a are in scope.'),
    ):
        wire = Wire(bases['eq'])
        claim = blocks(wire.decls)[0][role][0]
        claim['type'] = wire.replace(claim['type'], [('forallE', 'body')] * depth + [('forallE', 'type')], wire.expr(term))
        add('eq', label, wire.finish(), 'reject', 'formation-environment', reason)

    family = C('SortElimProp')
    bv = lambda n: ('raw-var', n)
    for label, typ, reason in (
        ('nonuniform-recursive-parameter', A(family, bv(0), bv(0), bv(0)),
         'Before field y the parameter b is index 1; replacing it with preceding field x is nonuniform recursion.'),
        ('recursive-index-contains-self', A(family, bv(1), bv(0), A(family, bv(1), bv(0), bv(0))),
         'A recursive index contains the inductive being declared; positivity forbids this even before type checking.'),
        ('recursive-index-arity', A(family, bv(1), bv(0)),
         'A recursive application has only one of its two required indices.'),
    ):
        wire = Wire(bases['sortelim'])
        ctor = blocks(wire.decls)[-1]['ctors'][0]
        ctor['type'] = wire.replace(ctor['type'], [('forallE', 'body')] * 2 + [('forallE', 'type')], wire.expr(typ))
        add('sortelim', label, wire.finish(), 'reject', 'recursive-indices',
            reason + ' Targeted edit leaves recursor metadata unchanged; this is not an isolated positivity proof.')

    for label, result, large, expected, reason in (
        ('in-order-indices', 'in-order', True, 'accept', 'Both non-Prop fields occur directly as result indices; their order need not equal field order.'),
        ('hidden-data-prop-only', 'hidden', False, 'accept', 'One data field is hidden, so only Prop elimination is generated.'),
        ('hidden-data-forged-large', 'hidden', True, 'reject', 'A hidden non-Prop field forbids large elimination even in a singleton Prop inductive.'),
        ('nested-index-prop-only', 'nested-only', False, 'accept', 'Upstream checks exact argument occurrence, not occurrences nested below applications or beta reduction.'),
        ('nested-index-forged-large', 'nested-only', True, 'reject', 'A field only beneath a lambda application is not a direct result-index argument.'),
        ('lost-large-universe', 'swapped', False, 'reject', 'Restricting an actually large eliminator is still wrong exported recursor metadata.'),
    ):
        add('sortelim-coherent', label, sort_elim_variant(source['sortelim'], result, large), expected,
            'large-elimination', reason, True)

    for family in ('eq', 'psigma'):
        base = family + '-iota'
        rows = copy.deepcopy(bases[base])
        for row in rows:
            for tag in ('forallE', 'lam'):
                if tag in row:
                    row[tag]['name'] = 0
        add(base, 'binder-control', rows, 'accept', 'iota', 'Renaming binders preserves the typed iota identity.', True)
        for change in ('wrong-result', 'wrong-index' if family == 'eq' else 'wrong-dependent-field'):
            add(base, change, iota(source[family], family, change), 'reject', 'iota',
                'The changed term does not type-check: arbitrary distinct variables cannot replace the index, dependent field, or reduction result.', True)

    # A two-constructor prerequisite gives a real, non-identity permutation control.
    for label, key, expected in [('prerequisite-ctor-presentation', 'ctors', 'accept'),
                                  ('prerequisite-rules-order', 'rules', 'reject')]:
        rows = copy.deepcopy(bases['sortelim'])
        block = blocks(rows)[0]
        (block['ctors'] if key == 'ctors' else block['recs'][0]['rules']).reverse()
        add('sortelim', label, rows, expected, 'metadata-order',
            'Outer constructor claim order is presentational; the recursor rules list remains ordered generated metadata.', key == 'ctors')
    return manifest, files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--generate', action='store_true')
    parser.add_argument('--verify', action='store_true')
    parser.add_argument('--timeout', type=float, default=25)
    parser.add_argument('--report', type=Path)
    parser.add_argument('--runtime-provenance', type=Path)
    parser.add_argument('--runtime-sha256')
    parser.add_argument('--record-runtime', action='store_true')
    parser.add_argument('--checker', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if not math.isfinite(args.timeout) or not 0 < args.timeout <= 86400:
        raise ValueError('timeout must be finite and in (0,86400]')
    manifest, files = plan()
    if args.generate:
        materialize(HERE, manifest, files)
    validate_materialized(HERE, manifest, files)
    if args.record_runtime:
        if not args.runtime_provenance or not args.runtime_sha256:
            raise ValueError('recording requires READY provenance path and digest')
        raw = args.runtime_provenance.read_bytes()
        if sha(raw) != args.runtime_sha256:
            raise ValueError('runtime provenance digest mismatch')
        comparison = runtime_comparison(raw)
        for name, data in [('indexed-startup-provenance.json', raw),
                           ('runtime-comparison.json', (json.dumps(comparison, indent=2, sort_keys=True) + '\n').encode())]:
            path = HERE / name
            if path.is_symlink() or path.exists():
                raise ValueError('refusing to overwrite runtime record: ' + name)
            with path.open('xb') as stream:
                stream.write(data)
    if not args.checker:
        print(json.dumps({'baselines': len(manifest['baselines']), 'cases': len(manifest['cases']),
                          'expected': Counter(c['expected'] for c in manifest['cases'])}, sort_keys=True))
        return 0
    if not args.report or not args.runtime_provenance or not args.runtime_sha256:
        raise ValueError('execution requires new --report and READY --runtime-provenance/--runtime-sha256')
    report_path = args.report.resolve()
    if report_path.parent != HERE or report_path.suffix != '.json' or report_path.exists():
        raise ValueError('report must be a new top-level JSON file in the owned audit directory')
    raw = args.runtime_provenance.read_bytes()
    if sha(raw) != args.runtime_sha256:
        raise ValueError('runtime provenance digest mismatch')
    identity = json.loads(raw)
    comparison = runtime_comparison(raw)
    if not comparison['all_runtime_project_inputs_match_review']:
        raise ValueError('runtime is not the reviewed indexed snapshot')
    if '--socket' in args.checker:
        i = args.checker.index('--socket') + 1
        if args.checker[i:i + 1] != [identity['startup']['socket']]:
            raise ValueError('checker socket differs from READY identity')
    watches = [Path(__file__), ROOT / 'scripts/hol-check.py', ROOT / 'scripts/test_metadata_mutations.py',
               ROOT / 'scripts/test_arena.py', args.runtime_provenance]
    with checker_snapshot(args.checker, None, watches) as (command, identities):
        report = run_suite(manifest, HERE, command, args.timeout, 4096)
    validate_materialized(HERE, manifest, files)
    if plan() != (manifest, files):
        raise ValueError('audit inputs changed during execution')
    report.update(finished_at=utc_now(), checker_identity=identities, valid=identities['unchanged'],
                  runtime_comparison=comparison, runtime_startup=identity['startup'])
    if not report['valid']:
        report['summary'].update(covered=0, complete=False)
    report['observed_codes'] = {group: dict(Counter(str(c.get('exit_code')) for c in report[group]))
                                for group in ('baselines', 'cases')}
    with report_path.open('x') as stream:
        json.dump(report, stream, indent=2, sort_keys=True)
        stream.write('\n')
    print(json.dumps(report['summary'], sort_keys=True))
    return 3 if not report['valid'] else 1 if report['summary']['failures'] else 0 if report['summary']['complete'] else 2


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError) as exc:
        print('audit fault: ' + str(exc), file=sys.stderr)
        sys.exit(3)
