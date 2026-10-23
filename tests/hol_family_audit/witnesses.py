#!/usr/bin/env python3
"""Named-term family witnesses; static generation never runs a checker."""

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
sys.path.insert(0, str(ROOT / 'scripts'))
from test_metadata_mutations import (materialize, validate_materialized, ndjson_bytes,
                                     run_suite, checker_snapshot)
from test_arena import utc_now

Z = ('zero',)
U = ('param', 'u')
V = ('param', 'v')
SU = ('succ', U)
ONE = ('succ', Z)
REC = ('recursive',)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def var(name):
    return ('var', name)


def sort(level):
    return ('sort', level)


def const(name, levels=()):
    return ('const', tuple(name.split('.')), tuple(levels))


def apps(fn, *args):
    for arg in args:
        fn = ('app', fn, arg)
    return fn


def bind(tag, parameters, body):
    for name, typ in reversed(parameters):
        body = (tag, name, typ, body)
    return body


class Wire:
    def __init__(self):
        self.rows = [{'meta': {'format': {'version': '3.1.0'},
                              'exporter': {'name': 'hol-family-audit-synthetic', 'version': '1'},
                              'lean': {'version': 'synthetic-audit-not-an-export', 'githash': ''}}}]
        self.names, self.levels, self.exprs = {(): 0}, {Z: 0}, {}

    def name(self, parts):
        parts = tuple(parts.split('.')) if isinstance(parts, str) else tuple(parts)
        if parts not in self.names:
            prefix = self.name(parts[:-1])
            index = len(self.names)
            self.names[parts] = index
            self.rows.append({'in': index, 'str': {'pre': prefix, 'str': parts[-1]}})
        return self.names[parts]

    def level(self, level):
        if level not in self.levels:
            if level[0] == 'param':
                payload = {'param': self.name(level[1])}
            elif level[0] == 'succ':
                payload = {'succ': self.level(level[1])}
            else:
                payload = {level[0]: {'lhs': self.level(level[1]), 'rhs': self.level(level[2])}}
            index = len(self.levels)
            self.levels[level] = index
            self.rows.append({'il': index, **payload})
        return self.levels[level]

    def expr(self, expr, context=()):
        tag = expr[0]
        if tag == 'var':
            payload = {'bvar': context.index(expr[1])}
        elif tag == 'raw-var':
            payload = {'bvar': expr[1]}
        elif tag == 'sort':
            payload = {'sort': self.level(expr[1])}
        elif tag == 'const':
            payload = {'const': {'name': self.name(expr[1]), 'us': [self.level(x) for x in expr[2]]}}
        elif tag == 'app':
            payload = {'app': {'fn': self.expr(expr[1], context), 'arg': self.expr(expr[2], context)}}
        else:
            assert tag in ('forallE', 'lam')
            payload = {tag: {'name': self.name(expr[1]), 'type': self.expr(expr[2], context),
                             'body': self.expr(expr[3], (expr[1],) + context), 'binderInfo': 'default'}}
        key = json.dumps(payload, sort_keys=True)
        if key not in self.exprs:
            index = len(self.exprs)
            self.exprs[key] = index
            self.rows.append({'ie': index, **payload})
        return self.exprs[key]

    def definition(self, name, levels, typ, value):
        header = {'name': self.name(name), 'levelParams': [self.name(x) for x in levels],
                  'type': self.expr(typ), 'value': self.expr(value)}
        self.rows.append({'def': {**header, 'all': [header['name']], 'hints': 'opaque', 'safety': 'safe'}})


def specifications():
    def spec(name, parameters, level, constructors, large, k=False, universes=()):
        return {'name': 'FamilyAudit.' + name, 'parameters': parameters, 'level': level,
                'constructors': constructors, 'large': large, 'k': k, 'universes': list(universes)}
    return {
        'wrap': spec('Wrap', [('A', sort(SU))], SU, [('mk', [var('A')])], True, universes=['u']),
        'chain': spec('Chain', [('A', sort(SU))], SU,
                      [('tip', [var('A')]), ('link', [var('A'), REC, REC])], True, universes=['u']),
        'dependent': spec('Dependent', [('A', sort(ONE)), ('a', var('A'))], ONE,
                          [('mk', [var('A')])], True),
        'data-prop': spec('DataProp', [('A', sort(ONE))], Z, [('mk', [var('A')])], False),
        'proof-prop': spec('ProofProp', [('P', sort(Z))], Z, [('mk', [var('P')])], True),
        'choice-prop': spec('ChoiceProp', [('P', sort(Z))], Z,
                            [('left', [var('P')]), ('right', [var('P')])], False),
        'parameter-prop': spec('ParameterProp', [('P', sort(Z)), ('h', var('P'))], Z,
                               [('mk', [])], True, True),
        'varying': spec('Varying', [('A', sort(U))], U, [('mk', [var('A')])], False, universes=['u']),
        'empty-varying': spec('EmptyVarying', [('A', sort(U))], U, [], True, universes=['u']),
    }


def emit_family(spec):
    """Build using named binders, independently of HOL's de Bruijn arithmetic."""
    wire = Wire()
    name, ps, pars = spec['name'], spec['universes'], spec['parameters']
    levels = [('param', x) for x in ps]
    arguments = [var(n) for n, _ in pars]
    family = apps(const(name, levels), *arguments)
    fresh = 'u'
    index = 1
    while fresh in ps:
        fresh, index = 'u_' + str(index), index + 1
    rec_ps = [fresh] + ps if spec['large'] else ps
    motive = bind('forallE', [('major', family)], sort(('param', fresh) if spec['large'] else Z))
    minors, ctor_headers, rules = [], [], []
    constructors = spec['constructors']
    for j, (suffix, fields) in enumerate(constructors):
        field_binders = [('f' + str(k), family if field == REC else field) for k, field in enumerate(fields)]
        field_vars = [var(n) for n, _ in field_binders]
        ihs = [('ih' + str(k), apps(var('motive'), var('f' + str(k))))
               for k, field in enumerate(fields) if field == REC]
        ctor = apps(const(name + '.' + suffix, levels), *arguments, *field_vars)
        minor = bind('forallE', field_binders + ihs, apps(var('motive'), ctor))
        minors.append(('minor' + str(j), minor))
        ctor_headers.append({'name': wire.name(name + '.' + suffix),
                             'levelParams': [wire.name(x) for x in ps],
                             'type': wire.expr(bind('forallE', pars + field_binders, family)),
                             'induct': wire.name(name), 'cidx': j, 'numParams': len(pars),
                             'numFields': len(fields), 'isUnsafe': False})
    for j, (suffix, fields) in enumerate(constructors):
        field_binders = [('f' + str(k), family if field == REC else field) for k, field in enumerate(fields)]
        rec = apps(const(name + '.rec', [('param', x) for x in rec_ps]),
                   *arguments, var('motive'), *[var(n) for n, _ in minors])
        ihs = [apps(rec, var('f' + str(k))) for k, field in enumerate(fields) if field == REC]
        body = apps(var('minor' + str(j)), *[var(n) for n, _ in field_binders], *ihs)
        rhs = bind('lam', pars + [('motive', motive)] + minors + field_binders, body)
        rules.append({'ctor': wire.name(name + '.' + suffix), 'nfields': len(fields), 'rhs': wire.expr(rhs)})
    rec_type = bind('forallE', pars + [('motive', motive)] + minors + [('major', family)],
                    apps(var('motive'), var('major')))
    header = {'name': wire.name(name), 'levelParams': [wire.name(x) for x in ps],
              'type': wire.expr(bind('forallE', pars, sort(spec['level']))), 'all': [wire.name(name)],
              'ctors': [wire.name(name + '.' + suffix) for suffix, _ in constructors],
              'numParams': len(pars), 'numIndices': 0, 'numNested': 0,
              'isRec': any(REC in fields for _, fields in constructors),
              'isReflexive': False, 'isUnsafe': False}
    recursor = {'name': wire.name(name + '.rec'), 'levelParams': [wire.name(x) for x in rec_ps],
                'type': wire.expr(rec_type), 'all': [wire.name(name)], 'numParams': len(pars),
                'numIndices': 0, 'numMotives': 1, 'numMinors': len(constructors),
                'rules': rules, 'k': spec['k'], 'isUnsafe': False}
    wire.rows.append({'inductive': {'types': [header], 'ctors': ctor_headers, 'recs': [recursor]}})
    return wire


def iota_witness(spec, mutation=None):
    wire = emit_family(spec)
    name = spec['name']
    A, B, a, b = map(var, ('A', 'B', 'a', 'b'))
    pars = [('A', sort(SU)), ('B', sort(SU)), ('a', A), ('b', B)]
    family = apps(const(name, [U]), A)
    motive = bind('lam', [('w', family)], A)
    minor = bind('lam', [('x', A)], var('x'))
    major = apps(const(name + '.mk', [U]), *( [B, b] if mutation == 'wrong-parameter' else [A, a]))
    reduction = apps(const(name + '.rec', [SU, U]), A, motive, minor, major)
    if mutation == 'wrong-parameter':
        wire.definition('FamilyAudit.iotaWrongParameter', ['u'], bind('forallE', pars, A),
                        bind('lam', pars, reduction))
    else:
        pars += [('P', bind('forallE', [('x', A)], sort(ONE))), ('h', apps(var('P'), a))]
        result = apps(var('P'), reduction)
        if mutation == 'wrong-result':
            # The conclusion is P(reduce(mk A a)); only the premise changes to P(a2).
            pars.insert(3, ('a2', A))
            pars[-1] = ('h', apps(var('P'), var('a2')))
        wire.definition('FamilyAudit.iotaIdentity', ['u'], bind('forallE', pars, result),
                        bind('lam', pars, var('h')))
    return wire.rows


def verify_snapshot():
    raw = (HERE / 'snapshot/manifest.json').read_bytes()
    manifest = json.loads(raw)
    for entry in manifest['inputs']:
        path = HERE / 'snapshot' / entry['path']
        if path.is_symlink() or sha(path.read_bytes()) != entry['sha256']:
            raise ValueError('review snapshot changed: ' + entry['path'])
    return sha(raw)


def plan():
    snapshot_hash = verify_snapshot()
    specs = specifications()
    baselines = {family: emit_family(spec).rows for family, spec in specs.items()}
    baselines['iota'] = iota_witness(specs['wrap'])
    manifest = {'suite': 'hol-family-audit-v1', 'version': 1, 'snapshot_manifest_sha256': snapshot_hash,
                'baselines': [], 'cases': [], 'runtime_status': 'not-run-until-server-release'}
    files = {}
    for family, rows in baselines.items():
        data = ndjson_bytes(rows)
        path = 'baselines/' + family + '.ndjson'
        files[path] = data
        manifest['baselines'].append({'id': 'baseline/' + family, 'family': family,
                                      'path': path, 'sha256': sha(data), 'size': len(data)})

    def add(family, label, rows, expected, dimension, reason):
        data = ndjson_bytes(rows)
        path = 'cases/' + family + '/' + label + '.ndjson'
        assert path not in files
        files[path] = data
        manifest['cases'].append({'id': family + '/' + label, 'family': family, 'path': path,
                                  'sha256': sha(data), 'size': len(data), 'expected': expected,
                                  'baseline_sha256': sha(ndjson_bytes(baselines[family])),
                                  'dimension': dimension, 'rationale': reason})

    for family, spec in specs.items():
        rows = copy.deepcopy(baselines[family])
        for row in rows:
            for tag in ('lam', 'forallE'):
                if tag in row:
                    row[tag]['name'] = 0
        add(family, 'binder-control', rows, 'accept', 'transport', 'Binder display names are not semantic.')
        changed = {**spec, 'large': not spec['large']}
        add(family, 'forged-elimination', emit_family(changed).rows, 'reject', 'elimination',
            'Coherently change recursor universe, type, and RHS contrary to upstream isLargeEliminator.')
        changed = {**spec, 'k': not spec['k']}
        add(family, 'forged-k', emit_family(changed).rows, 'reject', 'elimination',
            'K requires a universally Prop-valued singleton with no constructor fields beyond parameters.')

    for label, transform, expected, reason in (
        ('ctor-permutation', lambda block: block['ctors'].reverse(), 'accept',
         'Presentation order changes, not logical constructor list, indices, or rules.'),
        ('duplicate-claim', lambda block: block['ctors'].__setitem__(1, copy.deepcopy(block['ctors'][0])), 'reject',
         'Same total claim count cannot hide a missing distinct constructor.'),
        ('rule-permutation', lambda block: block['recs'][0]['rules'].reverse(), 'reject',
         'Recursor rules are ordered generated metadata, unlike the outer claim table.'),
        ('missing-claim', lambda block: block['ctors'].pop(), 'reject', 'All generated constructor claims are required.'),
        ('extra-claim', lambda block: block['ctors'].append(copy.deepcopy(block['ctors'][0])), 'reject',
         'Extra duplicate claims fail both length and uniqueness.'),
    ):
        rows = copy.deepcopy(baselines['chain'])
        transform(rows[-1]['inductive'])
        add('chain', label, rows, expected, 'metadata-order', reason)

    changed = {**specs['wrap'], 'level': ('succ', V), 'universes': ['u', 'v']}
    add('wrap', 'cross-universe-bound', emit_family(changed).rows, 'reject', 'universes',
        'Field level succ u is not universally at most result level succ v; equal sample valuations are insufficient.')
    changed = {**specs['wrap'], 'constructors': [('mk', [sort(('succ', SU))])]}
    add('wrap', 'oversized-field', emit_family(changed).rows, 'reject', 'universes',
        'A field whose type has universe succ(succ(succ u)) exceeds result succ u.')
    changed = {**specs['dependent'], 'parameters': [('A', sort(ONE)), ('a', sort(ONE))]}
    # Only the inductive parameter telescope is changed; supplied constructor/recursor prefixes remain original.
    wire = emit_family(specs['dependent'])
    block = wire.rows.pop()
    block['inductive']['types'][0]['type'] = wire.expr(
        bind('forallE', changed['parameters'], sort(ONE)))
    wire.rows.append(block)
    add('dependent', 'mismatched-constructor-prefix', wire.rows, 'reject', 'parameter-context',
        'Removing constructor parameter binders in ML must not discard their incompatible supplied types.')
    changed = {**specs['dependent'], 'parameters': [('A', sort(ONE)), ('a', ('raw-var', 1))]}
    add('dependent', 'out-of-scope-parameter', emit_family(changed).rows, 'reject', 'parameter-context',
        'The second parameter type refers outside its preceding context, even though later full binders exist.')

    for label, field, reason in (
        ('negative-recursion', bind('forallE', [('bad', apps(const('FamilyAudit.Wrap', [U]), var('A')))], var('A')),
         'A function domain contains the new family negatively and is unavailable in the prior environment.'),
        ('nonuniform-recursion', apps(const('FamilyAudit.Wrap', [U]),
                                     apps(const('FamilyAudit.Wrap', [U]), var('A'))),
         'Recursive occurrence changes uniform parameter A into Wrap A.'),
        ('self-ctor-field', const('FamilyAudit.Wrap.mk', [U]),
         'A current-block constructor cannot be used as a prior-environment data-field type.'),
    ):
        changed = {**specs['wrap'], 'constructors': [('mk', [field])]}
        add('wrap', label, emit_family(changed).rows, 'reject', 'prior-environment', reason)

    add('iota', 'wrong-parameter', iota_witness(specs['wrap'], 'wrong-parameter'), 'reject', 'iota',
        'A major of Wrap B must not reduce as though it had the recursor prefix parameter A.')
    add('iota', 'wrong-result', iota_witness(specs['wrap'], 'wrong-result'), 'reject', 'iota',
        'The correct reduction returns a; an independent arbitrary a2 cannot supply P(a).')
    return manifest, files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--generate', action='store_true')
    parser.add_argument('--verify', action='store_true')
    parser.add_argument('--timeout', type=float, default=25)
    parser.add_argument('--report', type=Path)
    parser.add_argument('--runtime-provenance', type=Path)
    parser.add_argument('--runtime-sha256')
    parser.add_argument('--checker', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if not math.isfinite(args.timeout) or not 0 < args.timeout <= 86400:
        raise ValueError('timeout must be finite and in (0, 86400]')
    manifest, files = plan()
    if args.generate:
        materialize(HERE, manifest, files)
    validate_materialized(HERE, manifest, files)
    if not args.checker:
        print(json.dumps({'baselines': len(manifest['baselines']), 'cases': len(manifest['cases']),
                          'expected': Counter(c['expected'] for c in manifest['cases'])}, sort_keys=True))
        return 0
    if not args.report or not args.runtime_provenance or not args.runtime_sha256:
        raise ValueError('runtime requires a new --report, --runtime-provenance, and --runtime-sha256 from READY')
    report_path = args.report.resolve()
    if report_path.parent != HERE or report_path.suffix != '.json' or report_path.exists():
        raise ValueError('report must be a new top-level JSON file in this audit directory')
    provenance = args.runtime_provenance.read_bytes()
    if sha(provenance) != args.runtime_sha256:
        raise ValueError('runtime provenance digest mismatch')
    identity = json.loads(provenance)
    if '--socket' in args.checker:
        socket_index = args.checker.index('--socket') + 1
        if args.checker[socket_index:socket_index + 1] != [identity['startup']['socket']]:
            raise ValueError('checker socket does not match supplied startup provenance')
    watches = [Path(__file__), ROOT / 'scripts/hol-check.py', ROOT / 'scripts/test_metadata_mutations.py',
               ROOT / 'scripts/test_arena.py', args.runtime_provenance]
    with checker_snapshot(args.checker, None, watches) as (command, identities):
        report = run_suite(manifest, HERE, command, args.timeout, 4096)
    validate_materialized(HERE, manifest, files)
    if plan() != (manifest, files):
        raise ValueError('audit snapshot or plan changed while running')
    report.update(finished_at=utc_now(), checker_identity=identities,
                  runtime_provenance_sha256=args.runtime_sha256, runtime_startup=identity['startup'],
                  review_snapshot_sha256=manifest['snapshot_manifest_sha256'],
                  provenance_note='Runtime startup and distinct review snapshot are separate identities.',
                  valid=identities['unchanged'])
    if not report['valid']:
        report['summary'].update(covered=0, complete=False)
    report['observed_codes'] = {group: dict(Counter(str(c.get('exit_code')) for c in report[group]))
                                for group in ('baselines', 'cases')}
    with report_path.open('x') as stream:
        json.dump(report, stream, indent=2, sort_keys=True)
        stream.write('\n')
    print(json.dumps(report['summary'], sort_keys=True))
    if not report['valid']:
        return 3
    return 1 if report['summary']['failures'] else 0 if report['summary']['complete'] else 2


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError) as exc:
        print('audit fault: ' + str(exc), file=sys.stderr)
        sys.exit(3)
