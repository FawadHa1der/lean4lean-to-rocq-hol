#!/usr/bin/env python3
# Copyright (c) 2026 Fawad Haider. All rights reserved.
"""Generate and run baseline-gated coherent declaration-name mutations."""

import argparse
import copy
import json
import math
from pathlib import Path
import sys

from test_arena import digest, utc_now, write_json
from test_metadata_mutations import (
    Parser, checker_snapshot, classify, materialize, ndjson_bytes, run_suite,
    safe_suite_dir as metadata_safe_suite_dir, sha256, validate_materialized,
)


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = ROOT / 'arena/manifest.json'
DEFAULT_SUITE = ROOT / 'tests/coherent'
DEFAULT_PINS = DEFAULT_SUITE / 'source-pins.json'
SUITE_NAME = 'coherent-declaration-names-v1'
RULES = {
    'primitive-shape': ['Lean4Lean/Primitive.lean:584', 'Lean4Lean/Environment.lean:127'],
    'reserved-name': ['Lean4Lean/Environment/Basic.lean:34', 'Lean4Lean/Inductive/Add.lean:246'],
    'nested-expression': ['Lean4Lean/Inductive/Add.lean:726', 'Lean4Lean/Inductive/Add.lean:736'],
    'ordinary-renaming': ['Lean4Lean/Inductive/Add.lean:142', 'Lean4Lean/Inductive/Add.lean:237'],
}


def safe_suite_dir(path, manifest_path):
    path = metadata_safe_suite_dir(path, manifest_path)
    old = (ROOT / 'tests/metadata').resolve()
    if path == old or path in old.parents or old in path.parents:
        raise ValueError('coherent output must not overlap the existing metadata suite')
    return path


def load_sources(manifest_path, pins_path):
    pins = json.loads(pins_path.read_bytes())
    manifest = json.loads(manifest_path.read_bytes())
    if pins.get('pin_version') != 1 or manifest.get('manifest_version') != 1:
        raise ValueError('unsupported source pin or Arena manifest version')
    for pin in pins['upstream_files']:
        path = (ROOT / pin['path']).resolve()
        if (ROOT / 'vendor/lean4lean').resolve() not in path.parents or digest(path) != pin['sha256']:
            raise ValueError('pinned upstream source changed: ' + pin['path'])
    seeds = {}
    for pin in pins['seeds']:
        matches = [entry for entry in manifest['cases'] if entry['id'] == pin['id']]
        if len(matches) != 1 or matches[0]['availability'] != 'available':
            raise ValueError('missing or duplicate available seed: ' + pin['id'])
        if any(matches[0][key] != pin[key] for key in ('path', 'size', 'sha256')):
            raise ValueError('seed differs from pinned manifest entry: ' + pin['id'])
        path = (manifest_path.parent / pin['path']).resolve()
        if (manifest_path.parent.resolve() not in path.parents or pin['size'] > 65536 or
                path.stat().st_size != pin['size']):
            raise ValueError('seed must be a pinned small local file')
        data = path.read_bytes()
        if sha256(data) != pin['sha256'] or pin['family'] in seeds:
            raise ValueError('seed SHA mismatch or duplicate family: ' + pin['id'])
        seeds[pin['family']] = (pin, data)
    if set(seeds) != {'empty', 'singleton', 'enum'}:
        raise ValueError('exactly Empty, PUnit, and Bool seeds are required')
    return pins, seeds


def rows_of(data):
    return [json.loads(line) for line in data.splitlines()]


def names_of(rows):
    names = {0: ()}
    for row in rows:
        if 'in' in row:
            if 'str' not in row or row['in'] in names:
                raise ValueError('these seeds require distinct string-name IDs')
            item = row['str']
            names[row['in']] = names[item['pre']] + (item['str'],)
    return names


def rename_names(rows, changes):
    """Retarget name nodes; all expression/header/rule references retain their IDs."""
    before = names_of(rows)
    targets = {}
    for source, replacement in changes:
        matches = [key for key, value in before.items() if value == tuple(source)]
        if len(matches) != 1 or not replacement or tuple(source) == tuple(replacement):
            raise ValueError('rename must identify one nonempty, changed structural name')
        if matches[0] in targets:
            raise ValueError('duplicate rename target')
        targets[matches[0]] = tuple(replacement)
    output = []
    next_id = max(before) + 1
    for row in copy.deepcopy(rows):
        replacement = targets.get(row.get('in'))
        if replacement is not None:
            prefix = 0
            # Fresh prefixes precede their use, even when their numeric IDs are larger.
            for component in replacement[:-1]:
                output.append({'in': next_id, 'str': {'pre': prefix, 'str': component}})
                prefix, next_id = next_id, next_id + 1
            row['str'] = {'pre': prefix, 'str': replacement[-1]}
        output.append(row)
    after = names_of(output)
    affected = [{'name_id': key, 'before': list(value), 'after': list(after[key])}
                for key, value in before.items() if after[key] != value]
    return output, affected


class WireBuilder:
    """Small NDJSON interner for the single, closed-field positive fixture."""

    def __init__(self, rows):
        self.rows = copy.deepcopy(rows)
        self.names = {value: key for key, value in names_of(rows).items()}
        self.next_name = max(self.names.values()) + 1
        self.next_expr = max(row.get('ie', -1) for row in rows) + 1
        self.expressions = {}

    def name(self, components):
        parts = tuple(components)
        if parts not in self.names:
            prefix = self.name(parts[:-1])
            key = self.next_name
            self.next_name += 1
            self.rows.append({'in': key, 'str': {'pre': prefix, 'str': parts[-1]}})
            self.names[parts] = key
        return self.names[parts]

    def expr(self, tag, value):
        key = json.dumps({tag: value}, sort_keys=True)
        if key not in self.expressions:
            index = self.next_expr
            self.next_expr += 1
            self.rows.append({'ie': index, tag: value})
            self.expressions[key] = index
        return self.expressions[key]

    def const(self, name):
        return self.expr('const', {'name': name, 'us': []})

    def app(self, fn, arg):
        return self.expr('app', {'fn': fn, 'arg': arg})

    def bind(self, tag, typ, body):
        return self.expr(tag, {'name': 0, 'type': typ, 'body': body, 'binderInfo': 'default'})


def closed_field_baseline(empty):
    rows = rows_of(empty)
    block, = [row['inductive'] for row in rows if 'inductive' in row]
    ind, = block['types']
    if block['ctors'] or ind['levelParams'] or names_of(rows)[ind['name']] != ('Empty',):
        raise ValueError('closed-field derivation requires the pinned monomorphic Empty')
    writer = WireBuilder(rows)
    writer.rows[0]['meta']['exporter']['name'] = 'coherent-test-fixture-derived-from-lean4export'
    empty_type = writer.const(ind['name'])
    box = writer.name(['Coherent', 'Box'])
    ctor = writer.name(['Coherent', 'Box', 'mk'])
    rec = writer.name(['Coherent', 'Box', 'rec'])
    elim, = block['recs'][0]['levelParams']
    elim_level, = [row['il'] for row in rows if row.get('param') == elim]
    box_type, constructor = writer.const(box), writer.const(ctor)
    b0, b1, b2 = [writer.expr('bvar', index) for index in range(3)]
    motive = writer.bind('forallE', box_type, writer.expr('sort', elim_level))
    ctor_type = writer.bind('forallE', empty_type, box_type)
    minor = writer.bind('forallE', empty_type, writer.app(b1, writer.app(constructor, b0)))
    rec_type = writer.bind('forallE', motive, writer.bind('forallE', minor,
        writer.bind('forallE', box_type, writer.app(b2, b0))))
    rhs = writer.bind('lam', motive, writer.bind('lam', minor,
        writer.bind('lam', empty_type, writer.app(b1, b0))))
    writer.rows.append({'inductive': {
        'types': [{'name': box, 'levelParams': [], 'type': ind['type'], 'all': [box],
                   'ctors': [ctor], 'numParams': 0, 'numIndices': 0, 'numNested': 0,
                   'isRec': False, 'isReflexive': False, 'isUnsafe': False}],
        'ctors': [{'name': ctor, 'levelParams': [], 'type': ctor_type, 'induct': box,
                   'cidx': 0, 'numParams': 0, 'numFields': 1, 'isUnsafe': False}],
        'recs': [{'name': rec, 'levelParams': [elim], 'type': rec_type, 'all': [box],
                  'numParams': 0, 'numIndices': 0, 'numMotives': 1, 'numMinors': 1,
                  'k': False, 'isUnsafe': False,
                  'rules': [{'ctor': ctor, 'nfields': 1, 'rhs': rhs}]}],
    }})
    name = writer.name(['Coherent', 'boxType'])
    writer.rows.append({'def': {'name': name, 'levelParams': [], 'type': ind['type'],
                               'value': box_type, 'all': [name], 'hints': 'opaque', 'safety': 'safe'}})
    return ndjson_bytes(writer.rows)


def mutation_specs(family):
    def one(label, old, new, expected, rule, rationale):
        return label, [(old, new)], expected, rule, rationale

    root = {'empty': ['Empty'], 'singleton': ['PUnit'], 'enum': ['Bool'], 'field': ['Empty']}[family]
    if family in ('empty', 'singleton', 'enum'):
        for primitive in ('Nat', 'Bool'):
            if root == [primitive]:
                continue
            yield one('type-as-' + primitive.lower(), root, [primitive], 'reject', 'primitive-shape',
                      'A coherent rename does not make this constructor/universe shape canonical for ' + primitive + '.')
        yield one('control-ordinary-type', root, ['Coherent', family.title()], 'accept', 'ordinary-renaming',
                  'Consistently rename the entire family to an ordinary fresh structural name.')
    if family == 'empty':
        yield one('type-as-nat-add', root, ['Nat', 'add'], 'reject', 'reserved-name',
                  'An empty datatype cannot occupy the reserved primitive operation name Nat.add.')
        for label, target in (('root', ['_nested']), ('child', ['_nested', 'T']),
                              ('deep', ['_nested', 'Deep', 'T'])):
            yield one('control-empty-nested-' + label, root, target, 'accept', 'nested-expression',
                      'There are no constructors, so the upstream constructor-expression prefix check is vacuous.')
        for label, target in (('nested', ['_nested.T']), ('primitive', ['Nat.add'])):
            yield one('control-dotted-' + label, root, target, 'accept', 'reserved-name',
                      'One string component containing a dot is not the corresponding hierarchical name.')
    if family in ('singleton', 'enum', 'field'):
        for label, target in (('root', ['_nested']), ('child', ['_nested', 'T']),
                              ('deep', ['_nested', 'Deep', 'T'])):
            yield one('nested-' + label, root, target, 'reject', 'nested-expression',
                      ('Only the empty dependency is renamed; the later Box constructor field now refers to '
                       'a reserved-prefix constant. The dependency itself has no constructors.' if family == 'field' else
                       'Constructor result types now contain a constant with the structural _nested prefix.'))
        for label, target in (('dotted', ['_nested.T']), ('nonroot', ['Coherent', '_nested', 'T']),
                              ('near-prefix', ['_nestedSuffix', 'T'])):
            yield one('control-nested-' + label, root, target, 'accept', 'nested-expression',
                      'The structural name does not have root component _nested; textual matching would be wrong.')
    if family == 'singleton':
        source = ['PUnit', 'unit']
        for target in (['Nat', 'add'], ['Nat', 'zero'], ['Nat', 'succ'], ['Bool', 'false'],
                       ['Bool', 'true'], ['String', 'ofList'], ['Char', 'ofNat']):
            yield one('ctor-as-' + '-'.join(target).lower(), source, target, 'reject', 'reserved-name',
                      'All references and rules follow this constructor rename, but an unrelated constructor '
                      'cannot use an upstream reserved primitive name.')
        for label, target in (('dotted-add', ['Nat.add']), ('dotted-zero', ['Nat.zero']),
                              ('nat-child', ['Nat', 'custom']), ('nested', ['_nested', 'mk']),
                              ('nonroot-primitive', ['User', 'Nat', 'zero'])):
            yield one('control-ctor-' + label, source, target, 'accept', 'reserved-name',
                      'This constructor name is not a protected primitive. The _nested guard traverses '
                      'constructor types, not the constructor name or generated recursor expressions.')
    if family == 'enum':
        yield ('swap-bool-constructor-names', [(['Bool', 'false'], ['Bool', 'true']),
                (['Bool', 'true'], ['Bool', 'false'])], 'reject', 'primitive-shape',
               'Swap names and all shared references coherently; Bool still requires false then true.')
    if family == 'field':
        yield one('control-field-ordinary', root, ['Coherent', 'Payload'], 'accept', 'ordinary-renaming',
                  'Rename the empty dependency consistently through the later constructor field and recursor.')
        yield one('control-ctor-name-only', ['Coherent', 'Box', 'mk'], ['_nested', 'mk'],
                  'accept', 'nested-expression',
                  'A prefixed constructor name is allowed when its type has no prefixed Const or Proj owner.')


def plan_suite(manifest_path=DEFAULT_MANIFEST, pins_path=DEFAULT_PINS):
    pins, seeds = load_sources(manifest_path, pins_path)
    manifest = {'suite_version': 1, 'suite': SUITE_NAME, 'upstream_revision': pins['upstream_revision'],
                'upstream_files': pins['upstream_files'], 'source_pins_sha256': digest(pins_path),
                'source_manifest_sha256_at_pinning': pins['source_manifest_sha256'],
                'baselines': [], 'cases': []}
    files = {}
    for family in ('empty', 'singleton', 'enum', 'field'):
        pin, seed = seeds['empty' if family == 'field' else family]
        data = closed_field_baseline(seed) if family == 'field' else seed
        baseline = {'id': 'derived/closed-field' if family == 'field' else pin['id'],
                    'family': family, 'path': 'baselines/' + family + '.ndjson',
                    'sha256': sha256(data), 'size': len(data), 'source_id': pin['id'],
                    'source_path': pin['path'], 'source_sha256': pin['sha256'],
                    'derivation': 'Empty plus Box.mk : Empty -> Box, dependent recursor; v1'
                    if family == 'field' else 'exact pinned bytes'}
        files[baseline['path']] = data
        manifest['baselines'].append(baseline)
        hashes = set()
        for label, changes, expected, rule, rationale in mutation_specs(family):
            changed, affected = rename_names(rows_of(data), changes)
            payload = ndjson_bytes(changed)
            case_id = family + '/' + label
            case = {'id': case_id, 'family': family, 'baseline_id': baseline['id'],
                    'baseline_sha256': baseline['sha256'], 'path': 'cases/' + case_id + '.ndjson',
                    'expected': expected, 'rationale': rationale, 'dimension': rule,
                    'upstream_evidence': RULES[rule], 'sha256': sha256(payload), 'size': len(payload),
                    'renames': [{'before': old, 'after': new} for old, new in changes],
                    'affected_names': affected}
            if case['path'] in files or case['sha256'] in hashes or not affected:
                raise ValueError('duplicate or empty coherent mutation: ' + case_id)
            hashes.add(case['sha256'])
            files[case['path']] = payload
            manifest['cases'].append(case)
    return manifest, files


def main(argv=None):
    parser = Parser(description=__doc__)
    parser.add_argument('--manifest', type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument('--pins', type=Path, default=DEFAULT_PINS)
    parser.add_argument('--suite-dir', type=Path, default=DEFAULT_SUITE)
    parser.add_argument('--generate', action='store_true')
    parser.add_argument('--verify', action='store_true')
    parser.add_argument('--timeout', type=float, default=10)
    parser.add_argument('--max-log-bytes', type=int, default=4096)
    parser.add_argument('--report', type=Path)
    parser.add_argument('--snapshot-binary', type=Path)
    parser.add_argument('--watch-file', type=Path, action='append', default=[])
    parser.add_argument('--checker', nargs=argparse.REMAINDER,
                        help='literal argv; last option; the input filepath is appended')
    args = parser.parse_args(argv)
    try:
        if not math.isfinite(args.timeout) or args.timeout <= 0 or args.max_log_bytes < 0:
            raise ValueError('timeout must be positive/finite and log limit nonnegative')
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
        protected = {(directory / name).resolve() for name in files}
        protected.update({directory / 'manifest.json', args.pins.resolve()})
        if directory not in report_path.parents or report_path.suffix != '.json' or report_path in protected:
            raise ValueError('report must be a separate JSON file inside the coherent suite')
        report = {'report_version': 1, 'suite': SUITE_NAME, 'started_at': utc_now(),
                  'checker_argv': args.checker, 'timeout_seconds': args.timeout, 'valid': False,
                  'suite_manifest_sha256': digest(directory / 'manifest.json'),
                  'source_manifest_sha256': digest(args.manifest),
                  'upstream_revision': manifest['upstream_revision']}
        watch = args.watch_file + [Path(__file__), ROOT / 'scripts/test_metadata_mutations.py',
                                   ROOT / 'scripts/test_arena.py']
        with checker_snapshot(args.checker, args.snapshot_binary, watch) as (command, identity):
            report.update(run_suite(manifest, directory, command, args.timeout, args.max_log_bytes))
        report['checker_identity'] = identity
        report['finished_at'] = utc_now()
        report['valid'] = identity['unchanged']
        if not report['valid']:
            report['invalid_reason'] = 'checker or watched dependency changed during execution'
        try:
            if plan_suite(args.manifest, args.pins) != (manifest, files):
                raise ValueError('source pins or generated plan changed during execution')
            validate_materialized(directory, manifest, files)
            report['inputs_unchanged'] = True
        except (OSError, ValueError, KeyError) as exc:
            report['inputs_unchanged'] = False
            report['valid'] = False
            report['invalid_reason'] = 'input integrity failure: ' + str(exc)
        if not report['valid']:
            report['summary'].update(complete=False, covered=0)
        write_json(report_path, report)
        print(json.dumps({'valid': report['valid'], **report['summary'], 'report': str(report_path)}, sort_keys=True))
        if not report['valid']:
            return 3
        if report['summary']['failures']:
            return 1
        return 0 if report['summary']['complete'] else 2
    except (OSError, ValueError, KeyError) as exc:
        print('coherent suite error: ' + str(exc), file=sys.stderr)
        return 3


if __name__ == '__main__':
    sys.exit(main())
