#!/usr/bin/env python3
# Copyright (c) 2026 Fawad Haider. All rights reserved.
"""Generate and run pinned inductive-metadata mutations, independently of Arena."""

import argparse
from collections import Counter
from contextlib import contextmanager
import copy
import hashlib
import json
import math
import os
from pathlib import Path
import shutil
import sys
import tempfile

from test_arena import digest, run_process, utc_now, write_json


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = ROOT / 'arena/manifest.json'
DEFAULT_SUITE = ROOT / 'tests/metadata'
DEFAULT_PINS = DEFAULT_SUITE / 'baseline-pins.json'
SUITE_NAME = 'inductive-metadata-mutations-v1'
FAILURES = {'false_accept', 'false_reject', 'fault', 'execution_error'}
GAPS = {'declined', 'timeout', 'not_covered'}


class Parser(argparse.ArgumentParser):
    def error(self, message):
        self.exit(3, self.prog + ': error: ' + message + '\n')


def json_bytes(value):
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + '\n').encode()


def ndjson_bytes(rows):
    return b''.join((json.dumps(row, separators=(',', ':'), ensure_ascii=True) + '\n').encode()
                    for row in rows)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def safe_suite_dir(path, manifest_path):
    path = path.resolve()
    for forbidden in (manifest_path.resolve().parent, ROOT / 'arena', ROOT / 'tests/arena'):
        forbidden = forbidden.resolve()
        if path == forbidden or path in forbidden.parents or forbidden in path.parents:
            raise ValueError('suite output must not overlap the Arena corpus or existing Arena tests')
    return path


def pinned_baselines(manifest_path, pins_path):
    pins = json.loads(pins_path.read_bytes())
    manifest = json.loads(manifest_path.read_bytes())
    if pins.get('pin_version') != 1 or manifest.get('manifest_version') != 1:
        raise ValueError('unsupported pin/manifest version')
    entries = manifest['cases']
    output = []
    for pin in pins['baselines']:
        found = [entry for entry in entries if entry['id'] == pin['id']]
        if len(found) != 1:
            raise ValueError('missing or duplicate baseline manifest entry: ' + pin['id'])
        entry = found[0]
        if (entry['availability'] != 'available' or
                any(entry[key] != pin[key] for key in ('path', 'size', 'sha256'))):
            raise ValueError('baseline pin differs from manifest: ' + pin['id'])
        path = (manifest_path.parent / pin['path']).resolve()
        if manifest_path.parent.resolve() not in path.parents or pin['size'] > 65536:
            raise ValueError('baseline must be a small, local corpus file')
        if path.stat().st_size != pin['size']:
            raise ValueError('baseline size mismatch: ' + pin['id'])
        data = path.read_bytes()
        if sha256(data) != pin['sha256']:
            raise ValueError('baseline SHA-256 mismatch: ' + pin['id'])
        output.append((pin, data))
    if {p['family'] for p, _ in output} != {'bool', 'nat', 'eq', 'prod', 'empty'} or len(output) != 5:
        raise ValueError('exactly the five pinned fixture families are required')
    return pins, output


def family_cases(pin, raw):
    rows = [json.loads(line) for line in raw.splitlines()]
    blocks = [(i, row['inductive']) for i, row in enumerate(rows) if 'inductive' in row]
    if len(blocks) != 1:
        raise ValueError('baseline must have exactly one inductive declaration')
    line, block = blocks[0]
    if len(block['types']) != 1 or len(block['recs']) != 1:
        raise ValueError('these mutations target single-family inductive fixtures')
    ind, rec = block['types'][0], block['recs'][0]
    ctor_names = [c['name'] for c in block['ctors']]
    occupied = {ind['name'], rec['name'], *ctor_names, *ind['levelParams'], *rec['levelParams']}
    foreign = next(row['in'] for row in rows[:line] if 'in' in row and row['in'] not in occupied)
    cases = []

    def emit(label, path, after, rationale, dimension, expected='reject', record=line):
        changed = copy.deepcopy(rows)
        target = changed[record]
        for part in path[:-1]:
            target = target[part]
        before = copy.deepcopy(target[path[-1]])
        if before == after:
            raise ValueError('no-op mutation: ' + label)
        target[path[-1]] = copy.deepcopy(after)
        payload = ndjson_bytes(changed)
        case_id = pin['family'] + '/' + label
        cases.append(({
            'id': case_id, 'family': pin['family'], 'baseline_id': pin['id'],
            'baseline_sha256': pin['sha256'], 'path': 'cases/' + case_id + '.ndjson',
            'expected': expected, 'rationale': rationale, 'dimension': dimension,
            'sha256': sha256(payload), 'size': len(payload),
            'edit': {'record': record + 1, 'path': path, 'before': before, 'after': after},
        }, payload))

    def metadata(label, path, after, rationale, dimension, expected='reject'):
        emit(label, ['inductive'] + path, after, rationale, dimension, expected)

    for group, objects, counts, flags in (
        ('types', block['types'], ('numParams', 'numIndices', 'numNested'),
         ('isRec', 'isReflexive', 'isUnsafe')),
        ('ctors', block['ctors'], ('cidx', 'numParams', 'numFields'), ('isUnsafe',)),
        ('recs', block['recs'], ('numParams', 'numIndices', 'numMotives', 'numMinors'),
         ('k', 'isUnsafe')),
    ):
        for index, obj in enumerate(objects):
            stem = f'{group}-{index}'
            for field in counts:
                metadata(stem + '-' + field.lower(), [group, index, field], obj[field] + 1,
                         f'Increase only {group}[{index}].{field}; the unchanged declaration '
                         'and generated metadata do not justify this count.', group + '.' + field)
            for field in flags:
                rationale = (f'Flip only {group}[{index}].{field}; it must not override derived metadata.'
                             if field != 'isUnsafe' else
                             'An exported unsafe flag must not be silently accepted under the safe '
                             'checker policy. Decline is recorded as a gap, not a rejection.')
                metadata(stem + '-' + field.lower(), [group, index, field], not obj[field],
                         rationale, group + '.' + field)
            params = obj['levelParams']
            metadata(stem + '-universe-arity', [group, index, 'levelParams'],
                     params[:-1] if params else [foreign],
                     'Change the universe-parameter arity of one header without changing its '
                     'type, constants, or sibling headers.', group + '.levelParams.arity')
            if group in ('types', 'recs'):
                for kind, names in (('missing', []), ('extra', obj['all'] + [obj['all'][0]]),
                                    ('wrong', [foreign])):
                    metadata(stem + '-all-' + kind, [group, index, 'all'], names,
                             'The exported all-list must name exactly the actual inductive block.',
                             group + '.all.' + kind)
            if group == 'ctors':
                metadata(stem + '-parent', [group, index, 'induct'], foreign,
                         'Point a constructor at an existing name that is not its inductive parent.',
                         'ctors.induct')

    if ind['ctors']:
        metadata('type-ctor-list-missing', ['types', 0, 'ctors'], ind['ctors'][:-1],
                 'Omit a constructor from the type header while keeping its exported declaration.',
                 'types.ctors.missing')
        extra = ind['ctors'] + [ind['ctors'][-1]]
    else:
        extra = [rec['name']]
    metadata('type-ctor-list-extra', ['types', 0, 'ctors'], extra,
             'Claim a duplicate or nonexistent constructor in the type header.', 'types.ctors.extra')
    if len(ind['ctors']) > 1:
        metadata('type-ctor-list-reordered', ['types', 0, 'ctors'], list(reversed(ind['ctors'])),
                 'Change constructor order without changing cidx or recursor rules.',
                 'types.ctors.order')
        metadata('control-constructor-table-order', ['ctors'], list(reversed(block['ctors'])),
                 'The constructor table is looked up by name; keep the logical ctor-list and '
                 'indices unchanged while changing only table presentation order.',
                 'control.constructor-table-order', 'accept')

    metadata('recursor-name', ['recs', 0, 'name'], foreign,
             'Rename only the recursor header to an existing, nondeclaration name; the expected '
             'family.rec declaration is now absent.', 'recs.name')
    metadata('recursor-type-body', ['recs', 0, 'type'], ind['type'],
             'Replace the recursor type by the already-defined inductive type expression.', 'recs.type')
    metadata('recursor-universe-extra', ['recs', 0, 'levelParams'], rec['levelParams'] + [foreign],
             'Add an unused recursor universe parameter without changing the generated recursor.',
             'recs.levelParams.extra')
    metadata('recursor-universe-duplicate', ['recs', 0, 'levelParams'],
             rec['levelParams'] + [rec['levelParams'][0]],
             'Duplicate a recursor universe parameter; headers must bind distinct parameters.',
             'recs.levelParams.duplicate')
    if len(rec['levelParams']) > 1:
        metadata('recursor-universe-order', ['recs', 0, 'levelParams'],
                 list(reversed(rec['levelParams'])),
                 'Reorder the universe binders but not their uses; this is not consistent alpha-renaming.',
                 'recs.levelParams.order')
    metadata('recursor-declaration-missing', ['recs'], [],
             'Omit the required generated recursor declaration.', 'recs.missing')
    metadata('recursor-declaration-extra', ['recs'], block['recs'] + [copy.deepcopy(rec)],
             'Duplicate the recursor declaration; matching one copy is insufficient.', 'recs.extra')

    rules = rec['rules']
    extra_rule = copy.deepcopy(rules[-1]) if rules else {'ctor': foreign, 'nfields': 0, 'rhs': ind['type']}
    metadata('rules-extra', ['recs', 0, 'rules'], rules + [extra_rule],
             'Append an extra reduction rule; Empty must have none and other families no duplicates.',
             'rules.extra')
    if len(rules) > 1:
        metadata('rules-reordered', ['recs', 0, 'rules'], list(reversed(rules)),
                 'The supplied rule sequence must match the independently generated constructor order.',
                 'rules.order')
    for index, rule in enumerate(rules):
        stem = f'rule-{index}'
        metadata(stem + '-missing', ['recs', 0, 'rules'], rules[:index] + rules[index + 1:],
                 'Remove one constructor reduction rule, retaining all constructors.', 'rules.missing')
        metadata(stem + '-ctor', ['recs', 0, 'rules', index, 'ctor'], foreign,
                 'Assign a rule to an existing name that is not a constructor.', 'rules.ctor')
        metadata(stem + '-fields', ['recs', 0, 'rules', index, 'nfields'], rule['nfields'] + 1,
                 'Lie about a rule field count without changing its constructor or lambda body.',
                 'rules.nfields')
        other_body = rules[1 - index]['rhs'] if len(rules) == 2 else ind['type']
        metadata(stem + '-body', ['recs', 0, 'rules', index, 'rhs'], other_body,
                 'Replace one recursor rule body with the other branch body, or an existing sort/type '
                 'expression for a single-constructor family. All wire references remain defined.',
                 'rules.rhs')

    # These change only presentation metadata, not logical declaration fields.
    emit('control-exporter-label', ['meta', 'exporter', 'name'], 'metadata-control',
         'Exporter branding is provenance metadata, not a logical admission premise.',
         'control.exporter', 'accept', record=0)
    definition_line = next(i for i, row in enumerate(rows) if 'def' in row)
    emit('control-reducibility-hint', ['def', 'hints'], 'abbrev',
         'Reducibility hints do not affect kernel validity of this unchanged safe definition.',
         'control.hints', 'accept', record=definition_line)
    binders = [(i, tag) for i, row in enumerate(rows[:line]) for tag in ('lam', 'forallE') if tag in row]
    binder_line, tag = binders[-1]
    emit('control-binder-info', [tag, 'binderInfo'],
         'implicit' if rows[binder_line][tag]['binderInfo'] == 'default' else 'default',
         'Binder implicitness is elaboration metadata, ignored by kernel alpha equality.',
         'control.binderInfo', 'accept', record=binder_line)
    emit('control-binder-name', [tag, 'name'], 0,
         'A de Bruijn-bound variable does not depend on its display name; use the anonymous name.',
         'control.binderName', 'accept', record=binder_line)
    universe_line = next(i for i, row in enumerate(rows) if row.get('in') == rec['levelParams'][0])
    emit('control-universe-alpha-name', ['str', 'str'], 'metadata_elim_universe',
         'Consistently rename the recursor elimination universe through its shared name-table entry; '
         'parameter arity, binding, and all uses stay unchanged.',
         'control.universe-alpha', 'accept', record=universe_line)
    return cases


def plan_suite(manifest_path, pins_path):
    pins, baselines = pinned_baselines(manifest_path, pins_path)
    manifest = {'suite_version': 1, 'suite': SUITE_NAME,
                'source_manifest_sha256_at_pinning': pins['source_manifest_sha256'],
                'baseline_pins_sha256': digest(pins_path), 'baselines': [], 'cases': []}
    files = {}
    for pin, data in baselines:
        path = 'baselines/' + pin['family'] + '.ndjson'
        files[path] = data
        manifest['baselines'].append({**pin, 'source_path': pin['path'], 'path': path})
        payload_hashes = set()
        for case, payload in family_cases(pin, data):
            if case['path'] in files or case['sha256'] in payload_hashes:
                raise ValueError('duplicate mutation ID or payload: ' + case['id'])
            payload_hashes.add(case['sha256'])
            files[case['path']] = payload
            manifest['cases'].append(case)
    return manifest, files


def materialize(suite_dir, manifest, files):
    # Refuse to silently replace either another suite or hand-edited generated files.
    planned = {**files, 'manifest.json': json_bytes(manifest)}
    for relative, data in planned.items():
        target = suite_dir / relative
        if target.is_symlink() or (target.exists() and target.read_bytes() != data):
            raise ValueError('refusing to overwrite changed generated file: ' + str(target))
        if suite_dir not in target.resolve().parents:
            raise ValueError('generated path escapes the suite directory')
    for relative, data in planned.items():
        target = suite_dir / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists():
            target.write_bytes(data)


def validate_materialized(suite_dir, manifest, files):
    if json.loads((suite_dir / 'manifest.json').read_bytes()) != manifest:
        raise ValueError('generated manifest differs from pinned deterministic mutation plan')
    for relative, data in files.items():
        target = suite_dir / relative
        if target.is_symlink() or suite_dir not in target.resolve().parents or target.read_bytes() != data:
            raise ValueError('generated case/baseline integrity mismatch: ' + relative)


def classify(result, expected):
    if result.get('timed_out'):
        return 'timeout'
    code = result.get('exit_code')
    if code == 2:
        return 'declined'
    if code not in (0, 1):
        return 'fault'
    actual = 'accept' if code == 0 else 'reject'
    return ('correct_' if actual == expected else 'false_') + actual


def summarize(baselines, cases):
    counts = Counter(case['status'] for case in cases)
    baseline_gaps = sum(b['status'] != 'accepted' for b in baselines)
    failures = sum(counts[key] for key in FAILURES)
    gaps = sum(counts[key] for key in GAPS)
    return {'total': len(cases), 'statuses': dict(sorted(counts.items())),
            'baselines_accepted': len(baselines) - baseline_gaps, 'baseline_gaps': baseline_gaps,
            'executed': sum(case.get('exit_code') is not None for case in cases),
            'covered': counts['correct_accept'] + counts['correct_reject'],
            'failures': failures, 'coverage_gaps': gaps,
            'complete': not (failures or gaps or baseline_gaps)}


def run_suite(manifest, suite_dir, checker, timeout, max_log_bytes, execute=run_process):
    def run(path):
        try:
            return execute(checker + [str(path)], path, timeout, 'file', max_log_bytes)
        except OSError as exc:
            return {'exit_code': None, 'timed_out': False, 'execution_error': str(exc)}

    baselines, results, gates = [], [], {}
    for baseline in manifest['baselines']:
        result = run(suite_dir / baseline['path'])
        accepted = result.get('exit_code') == 0 and not result.get('timed_out')
        gates[baseline['family']] = accepted
        baselines.append({'id': baseline['id'], 'family': baseline['family'],
                          'sha256': baseline['sha256'], **result,
                          'status': 'accepted' if accepted else 'not_covered'})
    for case in manifest['cases']:
        record = {key: case[key] for key in ('id', 'family', 'expected', 'sha256', 'dimension')}
        if not gates[case['family']]:
            results.append({**record, 'exit_code': None, 'status': 'not_covered',
                            'reason': 'positive baseline did not first accept; mutation was not run'})
            continue
        result = run(suite_dir / case['path'])
        status = 'execution_error' if 'execution_error' in result else classify(result, case['expected'])
        results.append({**record, **result, 'status': status})
    return {'baselines': baselines, 'cases': results, 'summary': summarize(baselines, results)}


def binary_identity(path):
    path = path.resolve(strict=True)
    info = path.stat()
    return {'path': str(path), 'sha256': digest(path), 'size': info.st_size,
            'mtime_ns': info.st_mtime_ns, 'inode': info.st_ino, 'device': info.st_dev}


@contextmanager
def checker_snapshot(command, snapshot_binary, watch_files):
    executable = shutil.which(command[0])
    if executable is None:
        raise ValueError('checker executable was not found: ' + command[0])
    executable = Path(executable).resolve()
    watched = list(dict.fromkeys([executable] + [path.resolve() for path in watch_files]))
    before = [binary_identity(path) for path in watched]
    details = {'before': before, 'after': [], 'unchanged': None, 'snapshotted': False}
    with tempfile.TemporaryDirectory(prefix='metadata-checker-', dir='/private/tmp') as directory:
        actual = list(command)
        if snapshot_binary is not None:
            if snapshot_binary.resolve() != executable:
                raise ValueError('--snapshot-binary must identify the first checker argv element')
            with executable.open('rb') as stream:
                magic = stream.read(4)
            if magic not in (b'\x7fELF', b'\xfe\xed\xfa\xce', b'\xce\xfa\xed\xfe',
                             b'\xfe\xed\xfa\xcf', b'\xcf\xfa\xed\xfe',
                             b'\xca\xfe\xba\xbe', b'\xbe\xba\xfe\xca',
                             b'\xca\xfe\xba\xbf', b'\xbf\xba\xfe\xca'):
                raise ValueError('snapshot requires a native executable; use --watch-file for scripts')
            copy_path = Path(directory) / 'checker'
            shutil.copyfile(executable, copy_path)
            copy_path.chmod(0o500)
            if digest(copy_path) != before[0]['sha256'] or binary_identity(executable) != before[0]:
                raise ValueError('checker changed while creating the executable snapshot')
            actual[0] = str(copy_path)
            details['snapshotted'] = True
            details['snapshot_sha256'] = digest(copy_path)
        try:
            yield actual, details
        finally:
            for path in watched:
                try:
                    details['after'].append(binary_identity(path))
                except OSError as exc:
                    details['after'].append({'path': str(path), 'error': str(exc)})
            details['unchanged'] = before == details['after']
            if snapshot_binary is not None:
                details['snapshot_unchanged'] = digest(copy_path) == details['snapshot_sha256']
                details['unchanged'] = details['unchanged'] and details['snapshot_unchanged']


def main(argv=None):
    parser = Parser(description=__doc__)
    parser.add_argument('--manifest', type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument('--pins', type=Path, default=DEFAULT_PINS)
    parser.add_argument('--suite-dir', type=Path, default=DEFAULT_SUITE)
    parser.add_argument('--generate', action='store_true', help='materialize pinned baselines and mutations')
    parser.add_argument('--verify', action='store_true', help='verify persisted inputs without a checker')
    parser.add_argument('--timeout', type=float, default=10)
    parser.add_argument('--max-log-bytes', type=int, default=4096)
    parser.add_argument('--report', type=Path, help='defaults to SUITE_DIR/report.json')
    parser.add_argument('--snapshot-binary', type=Path, help='copy this native checker executable before running')
    parser.add_argument('--watch-file', type=Path, action='append', default=[],
                        help='also hash a checker script/dependency before and after (repeatable)')
    parser.add_argument('--checker', nargs=argparse.REMAINDER,
                        help='literal argv, last option; input filename is appended, never shell-evaluated')
    args = parser.parse_args(argv)
    try:
        if not math.isfinite(args.timeout) or args.timeout <= 0 or args.max_log_bytes < 0:
            raise ValueError('timeout must be finite/positive and log limit nonnegative')
        suite_dir = safe_suite_dir(args.suite_dir, args.manifest)
        manifest, files = plan_suite(args.manifest, args.pins)
        if args.generate:
            materialize(suite_dir, manifest, files)
        validate_materialized(suite_dir, manifest, files)
        if not args.checker:
            if not (args.generate or args.verify):
                raise ValueError('supply --generate, --verify, or --checker ARGV...')
            print(json.dumps({'verified_inputs': len(files), 'mutations': len(manifest['cases']),
                              'baselines': len(manifest['baselines'])}, sort_keys=True))
            return 0
        report_path = (args.report or suite_dir / 'report.json').resolve()
        if (suite_dir not in report_path.parents or report_path.suffix != '.json' or
                report_path == suite_dir / 'manifest.json'):
            raise ValueError('report must be a JSON file inside the separate suite, not its manifest')
        if report_path in [(suite_dir / name).resolve() for name in files] or report_path == args.pins.resolve():
            raise ValueError('report must not replace a pinned input')
        report = {'report_version': 1, 'suite': SUITE_NAME, 'started_at': utc_now(),
                  'checker_argv': args.checker, 'timeout_seconds': args.timeout,
                  'suite_manifest_sha256': digest(suite_dir / 'manifest.json'),
                  'source_manifest_sha256': digest(args.manifest), 'valid': False}
        with checker_snapshot(args.checker, args.snapshot_binary, args.watch_file) as (checker, identity):
            report.update(run_suite(manifest, suite_dir, checker, args.timeout, args.max_log_bytes))
        report['checker_identity'] = identity
        report['finished_at'] = utc_now()
        report['valid'] = identity['unchanged']
        if not report['valid']:
            report['invalid_reason'] = 'checker executable or watched dependency changed during the run'
        try:
            validate_materialized(suite_dir, manifest, files)
            report['inputs_unchanged'] = True
        except (OSError, ValueError) as exc:
            report['inputs_unchanged'] = False
            report['valid'] = False
            report['invalid_reason'] = 'suite inputs changed during the run: ' + str(exc)
        if not report['valid']:
            report['summary']['complete'] = False
            report['summary']['covered'] = 0
        write_json(report_path, report)
        print(json.dumps({'valid': report['valid'], **report['summary'], 'report': str(report_path)}, sort_keys=True))
        if not report['valid']:
            return 3
        if report['summary']['failures']:
            return 1
        return 0 if report['summary']['complete'] else 2
    except (OSError, ValueError, KeyError, StopIteration) as exc:
        print('metadata suite error: ' + str(exc), file=sys.stderr)
        return 3


if __name__ == '__main__':
    sys.exit(main())
