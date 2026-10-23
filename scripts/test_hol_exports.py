#!/usr/bin/env python3
# Copyright (c) 2026 Fawad Haider. All rights reserved.
"""Baseline-gated HOL export transport, replay, and certificate-path regressions."""

import argparse
from collections import Counter
import copy
import json
import math
from pathlib import Path
import sys

from test_arena import digest, utc_now, write_json
from test_metadata_mutations import (
    Parser, checker_snapshot, classify, materialize, ndjson_bytes, run_suite,
    sha256, validate_materialized,
)
from test_coherent_mutations import WireBuilder, names_of, rename_names, rows_of, safe_suite_dir as coherent_dir

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = ROOT / 'arena/manifest.json'
DEFAULT_SUITE = ROOT / 'tests/hol_exports'
DEFAULT_PINS = DEFAULT_SUITE / 'source-pins.json'
SUITE_NAME = 'hol-export-regressions-v1'
LARGE_VALUES = {'literal53': 2 ** 53, 'literal63': 2 ** 63, 'literal256': 2 ** 256}


def safe_suite_dir(path, source):
    path = coherent_dir(path, source)
    old = (ROOT / 'tests/coherent').resolve()
    if path == old or path in old.parents or old in path.parents:
        raise ValueError('HOL export output must not overlap the coherent suite')
    return path


def load_sources(source, pins_path):
    pins = json.loads(pins_path.read_bytes())
    manifest = json.loads(source.read_bytes())
    if pins.get('pin_version') != 1 or manifest.get('manifest_version') != 1:
        raise ValueError('unsupported pin or source manifest version')
    for pin in pins['reference_sources']:
        path = (ROOT / pin['path']).resolve()
        if ROOT not in path.parents or digest(path) != pin['sha256']:
            raise ValueError('reference source hash mismatch: ' + pin['path'])
    seeds = {}
    for pin in pins['seeds']:
        found = [entry for entry in manifest['cases'] if entry['id'] == pin['id']]
        if (len(found) != 1 or found[0]['availability'] != 'available' or
                any(found[0][k] != pin[k] for k in ('path', 'size', 'sha256'))):
            raise ValueError('source manifest pin mismatch: ' + pin['id'])
        path = (source.parent / pin['path']).resolve()
        if (source.parent.resolve() not in path.parents or pin['size'] > 65536 or
                path.stat().st_size != pin['size']):
            raise ValueError('seed must be a pinned small local file')
        raw = path.read_bytes()
        if sha256(raw) != pin['sha256'] or pin['family'] in seeds:
            raise ValueError('seed hash mismatch or duplicate family')
        seeds[pin['family']] = (pin, raw)
    if set(seeds) != {'nat', 'bool', 'empty'}:
        raise ValueError('exactly canonical Nat, Bool, and Empty seeds are required')
    return pins, seeds


class Writer(WireBuilder):
    def var(self, index):
        return self.expr('bvar', index)

    def apps(self, fn, args):
        for arg in args:
            fn = self.app(fn, arg)
        return fn

    def binds(self, tag, types, body):
        for typ in reversed(types):
            body = self.bind(tag, typ, body)
        return body

    def define(self, parts, typ, value):
        name = self.name(parts)
        self.rows.append({'def': {'name': name, 'levelParams': [], 'type': typ, 'value': value,
                                 'all': [name], 'hints': 'opaque', 'safety': 'safe'}})


def derived(rows):
    rows = copy.deepcopy(rows)
    rows[0]['meta']['exporter']['name'] = 'hol-regression-derived-from-lean4export'
    return rows


def nat_baseline(raw):
    rows = derived(rows_of(raw))
    block, = [r['inductive'] for r in rows if 'inductive' in r]
    nat = block['types'][0]['name']
    sort_type = block['types'][0]['type']
    nat_expr = next(r['ie'] for r in rows if r.get('const') == {'name': nat, 'us': []})
    rows = [r for r in rows if 'natVal' not in r]
    definition, = [r['def'] for r in rows if 'def' in r]
    definition.update(type=sort_type, value=nat_expr)
    rows, _ = rename_names(rows, [(['aNatLit'], ['HolExports', 'natType'])])
    return rows


def tree_baseline(empty):
    """Empty plus Tree.tip, Tree.label : Empty -> Tree, and Tree.node : Tree -> Tree -> Tree."""
    writer = Writer(derived(rows_of(empty)))
    tree = writer.name(['HolExports', 'Tree'])
    names = [writer.name(['HolExports', 'Tree', n]) for n in ('tip', 'label', 'node')]
    rec = writer.name(['HolExports', 'Tree', 'rec'])
    empty_name = writer.name(['Empty'])
    empty_expr, tree_expr = writer.const(empty_name), writer.const(tree)
    # None marks a direct recursive field; every other field is a closed type expression.
    fields = [[], [empty_expr], [None, None]]
    field_types = [[tree_expr if item is None else item for item in fs] for fs in fields]
    old = next(r['inductive'] for r in writer.rows if 'inductive' in r)
    elim, = old['recs'][0]['levelParams']
    elim_level = next(r['il'] for r in writer.rows if r.get('param') == elim)
    motive = writer.bind('forallE', tree_expr, writer.expr('sort', elim_level))
    minors = []
    for j, fs in enumerate(fields):
        k = len(fs)
        positions = [p for p, item in enumerate(fs) if item is None]
        ih_types = [writer.app(writer.var(j + k + h), writer.var(k - 1 - p + h))
                    for h, p in enumerate(positions)]
        constructor = writer.apps(writer.const(names[j]),
                                  [writer.var(k - 1 - p + len(positions)) for p in range(k)])
        body = writer.app(writer.var(j + k + len(positions)), constructor)
        minors.append(writer.binds('forallE', field_types[j] + ih_types, body))
    m = len(fields)
    rec_type = writer.binds('forallE', [motive] + minors + [tree_expr],
                           writer.app(writer.var(m + 1), writer.var(0)))
    rules, ctors = [], []
    for j, fs in enumerate(fields):
        k = len(fs)
        field_vars = [writer.var(k - 1 - p) for p in range(k)]
        rec_const = writer.expr('const', {'name': rec, 'us': [elim_level]})
        recur = writer.apps(rec_const, [writer.var(k + m)] +
                            [writer.var(k + m - 1 - p) for p in range(m)])
        ihs = [writer.app(recur, field_vars[p]) for p, item in enumerate(fs) if item is None]
        body = writer.apps(writer.var(k + m - 1 - j), field_vars + ihs)
        rhs = writer.binds('lam', [motive] + minors + field_types[j], body)
        rules.append({'ctor': names[j], 'nfields': k, 'rhs': rhs})
        ctors.append({'name': names[j], 'levelParams': [],
                      'type': writer.binds('forallE', field_types[j], tree_expr),
                      'induct': tree, 'cidx': j, 'numParams': 0, 'numFields': k, 'isUnsafe': False})
    writer.rows.append({'inductive': {
        'types': [{'name': tree, 'levelParams': [], 'type': old['types'][0]['type'], 'all': [tree],
                   'ctors': names, 'numParams': 0, 'numIndices': 0, 'numNested': 0,
                   'isRec': True, 'isReflexive': False, 'isUnsafe': False}],
        'ctors': ctors,
        'recs': [{'name': rec, 'levelParams': [elim], 'type': rec_type, 'all': [tree],
                  'numParams': 0, 'numIndices': 0, 'numMotives': 1, 'numMinors': m,
                  'rules': rules, 'k': False, 'isUnsafe': False}],
    }})
    writer.define(['HolExports', 'treeType'], old['types'][0]['type'], tree_expr)
    return writer.rows


def indexed_identity(writer, domain, before, after, name):
    level_one = next(r['il'] for r in writer.rows if r.get('succ') == 0)
    predicate = writer.bind('forallE', domain, writer.expr('sort', level_one))
    premise = writer.app(writer.var(0), before)
    conclusion = writer.app(writer.var(1), after)
    typ = writer.binds('forallE', [predicate, premise], conclusion)
    body = writer.binds('lam', [predicate, premise], writer.var(0))
    writer.define(name, typ, body)


def literal_witness(nat_rows, before, after, leading_zero=False):
    writer = Writer(derived(nat_rows))
    nat = writer.const(writer.name(['Nat']))
    left = writer.expr('natVal', ('000' if leading_zero else '') + str(before))
    right = writer.expr('natVal', str(after))
    indexed_identity(writer, nat, left, right, ['HolExports', 'literalIdentity'])
    return writer.rows


def tree_iota_witness(rows):
    writer = Writer(rows)
    tree = writer.const(writer.name(['HolExports', 'Tree']))
    empty = writer.const(writer.name(['Empty']))
    tip = writer.const(writer.name(['HolExports', 'Tree', 'tip']))
    node = writer.const(writer.name(['HolExports', 'Tree', 'node']))
    level_one = next(r['il'] for r in rows if r.get('succ') == 0)
    rec = writer.expr('const', {'name': writer.name(['HolExports', 'Tree', 'rec']), 'us': [level_one]})
    folded = writer.apps(rec, [writer.bind('lam', tree, tree), tip,
                             writer.bind('lam', empty, tip),
                             writer.binds('lam', [tree] * 4, writer.var(1)),
                             writer.apps(node, [tip, tip])])
    indexed_identity(writer, tree, tip, folded, ['HolExports', 'treeIotaIdentity'])
    return writer.rows


def reorder(rows, reverse=False):
    nodes = [r for r in rows if any(k in r for k in ('in', 'il', 'ie'))]
    declarations = [r for r in rows if not any(k in r for k in ('meta', 'in', 'il', 'ie'))]
    if reverse:
        declarations.reverse()
    else:
        nodes = [r for key in ('in', 'il', 'ie') for r in nodes if key in r]
    return [copy.deepcopy(rows[0])] + copy.deepcopy(nodes + declarations)


def renumber(rows):
    maps = {}
    for key in ('in', 'il', 'ie'):
        ids = [r[key] for r in rows if key in r]
        maps[key] = {old: 100 + len(ids) - i for i, old in enumerate(ids)}
        if key != 'ie':
            maps[key][0] = 0
    n, u, e = (maps[k].__getitem__ for k in ('in', 'il', 'ie'))
    output = copy.deepcopy(rows)
    def header(item):
        item.update(name=n(item['name']), levelParams=list(map(n, item['levelParams'])), type=e(item['type']))
    for row in output:
        if 'in' in row:
            row['in'] = n(row['in'])
            row['str']['pre'] = n(row['str']['pre'])
        elif 'il' in row:
            row['il'] = u(row['il'])
            if 'param' in row:
                row['param'] = n(row['param'])
            elif 'succ' in row:
                row['succ'] = u(row['succ'])
            else:
                raise ValueError('unexpected level shape in bounded fixtures')
        elif 'ie' in row:
            row['ie'] = e(row['ie'])
            if 'sort' in row:
                row['sort'] = u(row['sort'])
            if 'const' in row:
                row['const']['name'] = n(row['const']['name'])
                row['const']['us'] = list(map(u, row['const']['us']))
            if 'app' in row:
                row['app'] = {k: e(v) for k, v in row['app'].items()}
            for tag in ('lam', 'forallE'):
                if tag in row:
                    value = row[tag]
                    value.update(name=n(value['name']), type=e(value['type']), body=e(value['body']))
        elif 'inductive' in row:
            block = row['inductive']
            for kind in ('types', 'ctors', 'recs'):
                for item in block[kind]:
                    header(item)
                    for key in ('all', 'ctors'):
                        if key in item:
                            item[key] = list(map(n, item[key]))
                    if 'induct' in item:
                        item['induct'] = n(item['induct'])
                    for rule in item.get('rules', []):
                        rule.update(ctor=n(rule['ctor']), rhs=e(rule['rhs']))
        elif 'def' in row:
            header(row['def'])
            row['def']['value'] = e(row['def']['value'])
            row['def']['all'] = list(map(n, row['def']['all']))
    return output


def mutations(family, rows, nat_rows):
    def edited(label, path, value, boundary, rationale):
        out = copy.deepcopy(rows)
        target = out
        for key in path[:-1]:
            target = target[key]
        if target[path[-1]] == value:
            raise ValueError('no-op mutation ' + label)
        target[path[-1]] = value
        return label, out, 'reject', boundary, rationale, {'path': path, 'value': value}
    def renamed(label, source, target, expected, rationale):
        out, affected = rename_names(rows, [(source, target)])
        return label, out, expected, 'names', rationale, {'affected_names': affected}
    if family in LARGE_VALUES:
        value = LARGE_VALUES[family]
        for label, left, right, expected in (
            ('control-next-exact', value + 1, value + 1, 'accept'),
            ('unequal-next', value, value + 1, 'reject'),
            ('unequal-previous', value, value - 1, 'reject'),
            ('unequal-word-wrap', value, value + 2 ** 64, 'reject'),
        ):
            yield label, literal_witness(nat_rows, left, right), expected, 'literal-conversion', \
                'The identity requires P(left) and P(right) to convert; exact distinct naturals must not merge.', \
                {'left_decimal': str(left), 'right_decimal': str(right)}
        yield ('control-leading-zero', literal_witness(nat_rows, value, value, True), 'accept',
               'literal-transport', 'Decimal leading zeros denote the same exact natural.', {'value': str(value)})
        yield ('control-forward-declarations', reorder(rows, True), 'accept', 'replay',
               'Replay must schedule Nat before a dependent literal definition despite serialized order.', {})
        line = next(i for i, r in enumerate(rows) if 'natVal' in r)
        yield edited('malformed-json-number', [line, 'natVal'], value, 'wire',
                     'Export natVal requires decimal text, not a JSON number.')
        yield edited('malformed-exponent', [line, 'natVal'], '1e80', 'wire',
                     'Scientific notation is not decimal natural-literal text in the wire contract.')
        return
    definition = next(r['def'] for r in reversed(rows) if 'def' in r)
    yield renamed('control-definition-name', list(names_of(rows)[definition['name']]),
                  ['HolExports', 'renamedDefinition'], 'accept', 'Only the ordinary declaration name changes coherently.')
    for label, field, value in (('binder-name', 'name', 0), ('binder-info', 'binderInfo', 'instImplicit')):
        out = copy.deepcopy(rows)
        for row in out:
            for tag in ('lam', 'forallE'):
                if tag in row:
                    row[tag][field] = value
        yield 'control-' + label, out, 'accept', 'binding', 'Bound expressions use de Bruijn indices, not binder display metadata.', {}
    yield 'control-table-ids', renumber(rows), 'accept', 'wire', 'Bijective name/level/expression ID renumbering preserves references and logical syntax.', {}
    yield 'control-grouped-tables', reorder(rows), 'accept', 'wire', 'Group the backward-defined name, level, and expression tables without changing declarations.', {}
    yield 'control-forward-declarations', reorder(rows, True), 'accept', 'replay', 'Reverse complete declaration records while keeping every wire reference defined before use.', {}
    line = max(i for i, row in enumerate(rows) if 'inductive' in row)
    block = rows[line]['inductive']
    ind, rec = block['types'][0], block['recs'][0]
    root = list(names_of(rows)[ind['name']])
    yield renamed('control-family-name', root, ['HolExports', 'Renamed' + family.title()],
                  'accept', 'Consistently rename the family and generated names; the literal-free Nat baseline has no implicit Nat dependency.')
    if len(block['ctors']) > 1:
        out = copy.deepcopy(rows)
        out[line]['inductive']['ctors'].reverse()
        yield ('control-constructor-table-order', out, 'accept', 'claim-transport',
               'Constructor table presentation changes, but logical ctor order, indices, and ordered rules do not.', {})
    base = [line, 'inductive']
    for label, path, value in (
        ('metadata-indices', ['types', 0, 'numIndices'], 1),
        ('metadata-recursive-flag', ['types', 0, 'isRec'], not ind['isRec']),
        ('metadata-minors', ['recs', 0, 'numMinors'], rec['numMinors'] + 1),
        ('metadata-k', ['recs', 0, 'k'], not rec['k']),
    ):
        yield edited(label, base + path, value, 'metadata', 'This one metadata claim is not justified by the unchanged declaration. Proof-search decline is not a rejection certificate.')
    if block['ctors']:
        yield edited('metadata-ctor-index', base + ['ctors', 0, 'cidx'], 1, 'metadata', 'Change one constructor index without changing logical constructor order.')
        yield edited('metadata-rule-missing', base + ['recs', 0, 'rules'], rec['rules'][1:], 'metadata', 'A supplied recursor is missing a generated reduction rule.')
        yield edited('metadata-rule-rhs', base + ['recs', 0, 'rules', 0, 'rhs'], ind['type'], 'metadata', 'An existing sort expression is not the generated lambda rule body; references remain defined.')
    if len(rec['rules']) > 1:
        yield edited('metadata-rule-order', base + ['recs', 0, 'rules'], list(reversed(rec['rules'])), 'metadata', 'Replay metadata authenticates ordered rules even though reduction looks them up by constructor.')
    if family == 'empty':
        for primitive in ('Nat', 'Bool'):
            yield renamed('false-empty-' + primitive.lower(), ['Empty'], [primitive], 'reject', 'Exact empty claims still do not have the required primitive constructor shape.')
        for label, target in (('structural', ['_nested', 'T']), ('dotted', ['_nested.T'])):
            yield renamed('control-empty-nested-' + label, ['Empty'], target, 'accept', 'Without constructors the upstream constructor-expression prefix restriction is vacuous.')
    if family in ('nat', 'bool'):
        target = 'Bool' if family == 'nat' else 'Nat'
        yield renamed('false-other-primitive', root, [target], 'reject', 'A coherent family rename cannot authorize the wrong primitive shape.')
    if family == 'tree':
        yield ('control-iota-dependent-index', tree_iota_witness(rows), 'accept', 'iota-conversion',
               'An identity from P(tip) to P(fold(node tip tip)) requires the generated recursive iota rule.', {})
        yield renamed('nested-result', root, ['_nested', 'T'], 'reject', 'Constructor result constants have the structural reserved prefix.')
        yield renamed('nested-field', ['Empty'], ['_nested', 'Payload'], 'reject', 'The empty dependency is legal, but Tree.label now has a prefixed constant in its domain.')
        yield renamed('control-dotted-result', root, ['_nested.T'], 'accept', 'One dotted component is not the structural reserved namespace.')
        yield renamed('control-dotted-field', ['Empty'], ['_nested.Payload'], 'accept', 'A dotted single string does not have the reserved root prefix.')
        for item in ('add', 'zero'):
            yield renamed('false-ctor-nat-' + item, root + ['tip'], ['Nat', item], 'reject', 'An unrelated constructor cannot occupy a protected primitive name.')
        yield renamed('control-dotted-ctor', root + ['tip'], ['Nat.add'], 'accept', 'The single string Nat.add is not the protected hierarchical name.')


def plan_suite(source=DEFAULT_MANIFEST, pins_path=DEFAULT_PINS):
    pins, seeds = load_sources(source, pins_path)
    nat_rows = nat_baseline(seeds['nat'][1])
    bases = {'nat': nat_rows, 'bool': rows_of(seeds['bool'][1]), 'empty': rows_of(seeds['empty'][1]),
             'tree': tree_baseline(seeds['empty'][1])}
    bases.update({family: literal_witness(nat_rows, value, value) for family, value in LARGE_VALUES.items()})
    manifest = {'suite_version': 1, 'suite': SUITE_NAME, 'upstream_revision': pins['upstream_revision'],
                'source_pins_sha256': digest(pins_path), 'reference_sources': pins['reference_sources'],
                'source_manifest_sha256_at_pinning': pins['source_manifest_sha256'], 'baselines': [], 'cases': []}
    files = {}
    for family, rows in bases.items():
        source_family = 'nat' if family in LARGE_VALUES else 'empty' if family == 'tree' else family
        pin, raw = seeds[source_family]
        data = raw if family in ('bool', 'empty') else ndjson_bytes(rows)
        baseline = {'id': 'hol-exports/' + family, 'family': family, 'path': 'baselines/' + family + '.ndjson',
                    'size': len(data), 'sha256': sha256(data), 'source_id': pin['id'], 'source_sha256': pin['sha256'],
                    'derivation': 'exact bytes' if family in ('bool', 'empty') else 'deterministic fixture construction v1'}
        manifest['baselines'].append(baseline)
        files[baseline['path']] = data
        hashes = set()
        for label, changed, expected, boundary, rationale, recipe in mutations(family, rows, nat_rows):
            payload = ndjson_bytes(changed)
            ident = family + '/' + label
            case = {'id': ident, 'family': family, 'baseline_id': baseline['id'], 'baseline_sha256': baseline['sha256'],
                    'path': 'cases/' + ident + '.ndjson', 'size': len(payload), 'sha256': sha256(payload),
                    'expected': expected, 'dimension': boundary, 'rationale': rationale, 'recipe': recipe}
            if case['path'] in files or case['sha256'] in hashes or changed == rows:
                raise ValueError('duplicate or no-op fixture: ' + ident)
            hashes.add(case['sha256'])
            manifest['cases'].append(case)
            files[case['path']] = payload
    return manifest, files


def observed_codes(records):
    counts = Counter('timeout' if r.get('timed_out') else
                     str(r['exit_code']) if r.get('exit_code') in (0, 1, 2, 3) else
                     'other_fault' if 'execution_error' in r else
                     'not_run' if r.get('status') == 'not_covered' else 'other_fault' for r in records)
    return {key: counts[key] for key in ('0', '1', '2', '3', 'timeout', 'not_run', 'other_fault')}


def main(argv=None):
    parser = Parser(description=__doc__)
    parser.add_argument('--manifest', type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument('--pins', type=Path, default=DEFAULT_PINS)
    parser.add_argument('--suite-dir', type=Path, default=DEFAULT_SUITE)
    parser.add_argument('--generate', action='store_true')
    parser.add_argument('--verify', action='store_true')
    parser.add_argument('--timeout', type=float, default=45)
    parser.add_argument('--max-log-bytes', type=int, default=4096)
    parser.add_argument('--watch-file', type=Path, action='append', default=[])
    parser.add_argument('--report', type=Path)
    parser.add_argument('--runtime-note', default='', help='server startup/version provenance, stored only in report')
    parser.add_argument('--checker', nargs=argparse.REMAINDER, help='literal argv, last option; filepath appended')
    args = parser.parse_args(argv)
    try:
        if not math.isfinite(args.timeout) or args.timeout <= 0 or args.max_log_bytes < 0:
            raise ValueError('positive finite timeout and nonnegative log bound required')
        directory = safe_suite_dir(args.suite_dir, args.manifest)
        manifest, files = plan_suite(args.manifest, args.pins)
        if args.generate:
            materialize(directory, manifest, files)
        validate_materialized(directory, manifest, files)
        if not args.checker:
            if not (args.generate or args.verify):
                raise ValueError('supply --generate, --verify, or --checker ARGV...')
            print(json.dumps({'baselines': len(manifest['baselines']), 'mutations': len(manifest['cases']),
                              'verified_inputs': len(files)}, sort_keys=True))
            return 0
        report_path = (args.report or directory / 'report.json').resolve()
        protected = {(directory / name).resolve() for name in files} | {directory / 'manifest.json', args.pins.resolve()}
        if directory not in report_path.parents or report_path.suffix != '.json' or report_path in protected:
            raise ValueError('report must be a separate JSON file within the HOL export suite')
        report = {'report_version': 1, 'suite': SUITE_NAME, 'started_at': utc_now(),
                  'checker_argv': args.checker, 'runtime_note': args.runtime_note, 'timeout_seconds': args.timeout,
                  'suite_manifest_sha256': digest(directory / 'manifest.json'), 'valid': False,
                  'provenance_limit': 'Client/current-source hashes do not attest which files a warm HOL server loaded.'}
        watch = args.watch_file + [Path(__file__)] + [ROOT / 'scripts' / name for name in
                ('test_arena.py', 'test_metadata_mutations.py', 'test_coherent_mutations.py')]
        with checker_snapshot(args.checker, None, watch) as (command, identity):
            report.update(run_suite(manifest, directory, command, args.timeout, args.max_log_bytes))
        report.update(checker_identity=identity, finished_at=utc_now(), valid=identity['unchanged'])
        report['observed_codes'] = {'baselines': observed_codes(report['baselines']), 'mutations': observed_codes(report['cases'])}
        if not report['valid']:
            report['invalid_reason'] = 'checker client or watched dependencies changed during execution'
        try:
            if plan_suite(args.manifest, args.pins) != (manifest, files):
                raise ValueError('source pins or plan changed during execution')
            validate_materialized(directory, manifest, files)
            report['inputs_unchanged'] = True
        except (OSError, KeyError, ValueError) as exc:
            report.update(valid=False, inputs_unchanged=False, invalid_reason='input integrity failure: ' + str(exc))
        if not report['valid']:
            report['summary'].update(complete=False, covered=0)
        write_json(report_path, report)
        print(json.dumps({'valid': report['valid'], **report['summary'], 'observed_codes': report['observed_codes'],
                          'report': str(report_path)}, sort_keys=True))
        if not report['valid']:
            return 3
        if report['summary']['failures']:
            return 1
        return 0 if report['summary']['complete'] else 2
    except (OSError, KeyError, ValueError) as exc:
        print('HOL export suite error: ' + str(exc), file=sys.stderr)
        return 3


if __name__ == '__main__':
    sys.exit(main())
