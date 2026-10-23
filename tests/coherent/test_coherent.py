# Copyright (c) 2026 Fawad Haider. All rights reserved.
import copy
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
import test_coherent_mutations as suite


def result(code, timeout=False):
    return {'exit_code': code, 'timed_out': timeout, 'stdout': '', 'stderr': '', 'elapsed_seconds': 0}


class CoherentTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest, cls.files = suite.plan_suite()
        cls.baselines = {b['family']: b for b in cls.manifest['baselines']}

    def case(self, name):
        case = next(c for c in self.manifest['cases'] if c['id'] == name)
        return case, suite.rows_of(self.files[case['path']])

    def test_deterministic_hashes_and_only_name_nodes_change(self):
        self.assertEqual((self.manifest, self.files), suite.plan_suite())
        self.assertEqual(len(self.manifest['cases']), 47)
        self.assertEqual(sum(c['expected'] == 'accept' for c in self.manifest['cases']), 24)
        for case in self.manifest['cases']:
            with self.subTest(case=case['id']):
                baseline = self.baselines[case['family']]
                before = suite.rows_of(self.files[baseline['path']])
                after = suite.rows_of(self.files[case['path']])
                self.assertEqual([r for r in before if 'in' not in r],
                                 [r for r in after if 'in' not in r])
                rebuilt, affected = suite.rename_names(before,
                    [(r['before'], r['after']) for r in case['renames']])
                self.assertEqual(after, rebuilt)
                self.assertEqual(affected, case['affected_names'])
                self.assertEqual(suite.sha256(self.files[case['path']]), case['sha256'])
                self.assertEqual(case['baseline_sha256'], baseline['sha256'])
                self.assertTrue(case['upstream_evidence'])
                self.assertTrue(case['rationale'])
                self.assertFalse(any('expected' in row for row in after))

    def test_structural_prefix_is_not_a_dotted_string(self):
        negative, rows = self.case('singleton/nested-child')
        positive, dotted = self.case('singleton/control-nested-dotted')
        names, dotted_names = suite.names_of(rows), suite.names_of(dotted)
        ind = next(r['inductive']['types'][0] for r in rows if 'inductive' in r)
        self.assertEqual(names[ind['name']], ('_nested', 'T'))
        self.assertEqual(dotted_names[ind['name']], ('_nested.T',))
        self.assertEqual(negative['expected'], 'reject')
        self.assertEqual(positive['expected'], 'accept')
        self.assertEqual(names[next(r['inductive']['recs'][0]['name'] for r in rows if 'inductive' in r)],
                         ('_nested', 'T', 'rec'))

    def test_empty_prefixed_type_and_ctor_name_only_are_controls(self):
        for name in ('empty/control-empty-nested-root', 'empty/control-empty-nested-child',
                     'empty/control-empty-nested-deep', 'singleton/control-ctor-nested',
                     'field/control-ctor-name-only', 'singleton/control-ctor-dotted-add'):
            self.assertEqual(self.case(name)[0]['expected'], 'accept')

    def test_field_case_isolates_the_later_constructor_domain(self):
        case, rows = self.case('field/nested-child')
        blocks = [row['inductive'] for row in rows if 'inductive' in row]
        expressions = {r['ie']: r for r in rows if 'ie' in r}
        names = suite.names_of(rows)
        self.assertEqual(blocks[0]['ctors'], [])
        self.assertEqual(names[blocks[0]['types'][0]['name']], ('_nested', 'T'))
        self.assertEqual(names[blocks[1]['types'][0]['name']], ('Coherent', 'Box'))
        ctor_type = expressions[blocks[1]['ctors'][0]['type']]['forallE']
        self.assertEqual(names[expressions[ctor_type['type']]['const']['name']], ('_nested', 'T'))
        self.assertEqual(names[expressions[ctor_type['body']]['const']['name']], ('Coherent', 'Box'))
        self.assertEqual(case['expected'], 'reject')

    def test_derived_recursor_has_independent_expected_debruijn_shape(self):
        rows = suite.rows_of(self.files[self.baselines['field']['path']])
        names = suite.names_of(rows)
        expressions = {r['ie']: r for r in rows if 'ie' in r}
        def expr(key):
            row = expressions[key]
            if 'const' in row:
                return ('const', names[row['const']['name']])
            if 'bvar' in row:
                return ('var', row['bvar'])
            if 'sort' in row:
                return ('sort', row['sort'])
            if 'app' in row:
                return ('app', expr(row['app']['fn']), expr(row['app']['arg']))
            for tag in ('forallE', 'lam'):
                if tag in row:
                    return (tag, expr(row[tag]['type']), expr(row[tag]['body']))
            self.fail('unexpected expression in the bounded fixture')
        block = [r['inductive'] for r in rows if 'inductive' in r][1]
        v0, v1, v2 = ('var', 0), ('var', 1), ('var', 2)
        empty, box, mk = ('const', ('Empty',)), ('const', ('Coherent', 'Box')), ('const', ('Coherent', 'Box', 'mk'))
        elim = next(r['il'] for r in rows if r.get('param') == block['recs'][0]['levelParams'][0])
        motive = ('forallE', box, ('sort', elim))
        minor = ('forallE', empty, ('app', v1, ('app', mk, v0)))
        self.assertEqual(expr(block['ctors'][0]['type']), ('forallE', empty, box))
        self.assertEqual(expr(block['recs'][0]['type']),
                         ('forallE', motive, ('forallE', minor, ('forallE', box, ('app', v2, v0)))))
        self.assertEqual(expr(block['recs'][0]['rules'][0]['rhs']),
                         ('lam', motive, ('lam', minor, ('lam', empty, ('app', v1, v0)))))

    def test_all_wire_references_precede_use_and_metadata_stays_coherent(self):
        for path, data in self.files.items():
            with self.subTest(path=path):
                names, levels, expressions = {0}, {0}, set()
                for row in suite.rows_of(data):
                    if 'in' in row:
                        self.assertIn(row['str']['pre'], names)
                        self.assertNotIn(row['in'], names)
                        names.add(row['in'])
                    elif 'il' in row:
                        self.assertIn(row.get('param', row.get('succ')),
                                      names if 'param' in row else levels)
                        self.assertNotIn(row['il'], levels)
                        levels.add(row['il'])
                    elif 'ie' in row:
                        if 'sort' in row:
                            self.assertIn(row['sort'], levels)
                        if 'const' in row:
                            self.assertIn(row['const']['name'], names)
                            self.assertTrue(set(row['const']['us']) <= levels)
                        if 'app' in row:
                            self.assertTrue(set(row['app'].values()) <= expressions)
                        for tag in ('forallE', 'lam'):
                            if tag in row:
                                self.assertIn(row[tag]['name'], names)
                                self.assertTrue({row[tag]['type'], row[tag]['body']} <= expressions)
                        self.assertNotIn(row['ie'], expressions)
                        expressions.add(row['ie'])
                    elif 'inductive' in row:
                        block = row['inductive']
                        ind, rec = block['types'][0], block['recs'][0]
                        for item in block['types'] + block['ctors'] + block['recs']:
                            self.assertIn(item['name'], names)
                            self.assertIn(item['type'], expressions)
                            self.assertTrue(set(item['levelParams']) <= names)
                        self.assertEqual(ind['all'], [ind['name']])
                        self.assertEqual(rec['all'], [ind['name']])
                        self.assertEqual(ind['ctors'], [c['name'] for c in block['ctors']])
                        self.assertEqual(ind['ctors'], [r['ctor'] for r in rec['rules']])
                        for index, (ctor, rule) in enumerate(zip(block['ctors'], rec['rules'])):
                            self.assertEqual(ctor['induct'], ind['name'])
                            self.assertEqual(ctor['cidx'], index)
                            self.assertEqual(ctor['numFields'], rule['nfields'])
                            self.assertIn(rule['rhs'], expressions)
                    elif 'def' in row:
                        self.assertIn(row['def']['name'], names)
                        self.assertTrue({row['def']['type'], row['def']['value']} <= expressions)
                resolved = suite.names_of(suite.rows_of(data))
                for row in suite.rows_of(data):
                    if 'inductive' in row:
                        block = row['inductive']
                        self.assertEqual(resolved[block['recs'][0]['name']],
                                         resolved[block['types'][0]['name']] + ('rec',))

    def test_nonaccepting_baseline_never_credits_mutations(self):
        for outcome in (result(1), result(2), result(3), result(-9, True)):
            calls = []
            def execute(command, *args):
                calls.append(command)
                return outcome
            report = suite.run_suite(self.manifest, Path('/private/tmp/coherent-fake'),
                                     ['checker'], 1, 50, execute=execute)
            self.assertEqual(len(calls), 4)
            self.assertEqual(report['summary']['covered'], 0)
            self.assertEqual(report['summary']['statuses'], {'not_covered': 47})
            self.assertFalse(report['summary']['complete'])

    def test_argv_preserved_and_reject_all_accept_all_both_fail(self):
        for mutation_code in (0, 1):
            calls = []
            command = ['checker', '--socket', '/private/tmp/space ; $(literal)']
            def execute(argv, *args):
                calls.append(argv)
                return result(0 if len(calls) <= 4 else mutation_code)
            report = suite.run_suite(self.manifest, Path('/private/tmp/coherent-fake'),
                                     command, 1, 50, execute=execute)
            self.assertTrue(all(call[:-1] == command for call in calls))
            self.assertEqual(report['summary']['failures'], 23 if mutation_code == 0 else 24)
        self.assertEqual(suite.classify(result(2), 'reject'), 'declined')
        self.assertEqual(suite.classify(result(3), 'accept'), 'fault')
        self.assertEqual(suite.classify(result(-9, True), 'reject'), 'timeout')

    def test_pins_and_old_suite_output_are_protected(self):
        for path in (ROOT, ROOT / 'arena', ROOT / 'tests/arena', ROOT / 'tests/metadata',
                     ROOT / 'tests/metadata/new'):
            with self.assertRaises(ValueError):
                suite.safe_suite_dir(path, suite.DEFAULT_MANIFEST)
        for section in ('seeds', 'upstream_files'):
            pins = json.loads(suite.DEFAULT_PINS.read_bytes())
            pins[section][0]['sha256'] = '0' * 64
            with tempfile.TemporaryDirectory(dir='/private/tmp') as directory:
                path = Path(directory) / 'pins.json'
                path.write_text(json.dumps(pins))
                with self.assertRaises(ValueError):
                    suite.plan_suite(suite.DEFAULT_MANIFEST, path)

    def test_tampered_artifacts_refuse_overwrite_and_validation(self):
        with tempfile.TemporaryDirectory(dir='/private/tmp') as directory:
            path = Path(directory)
            suite.materialize(path, self.manifest, self.files)
            suite.validate_materialized(path, self.manifest, self.files)
            target = path / self.manifest['cases'][0]['path']
            target.write_bytes(target.read_bytes() + b'\n')
            with self.assertRaises(ValueError):
                suite.materialize(path, self.manifest, self.files)
            with self.assertRaises(ValueError):
                suite.validate_materialized(path, self.manifest, self.files)

    def test_changed_dependency_invalidates_report(self):
        with tempfile.TemporaryDirectory(dir='/private/tmp') as directory:
            path = Path(directory)
            watched = path / 'dependency'
            watched.write_text('before')
            def fake_run(*args):
                watched.write_text('after')
                return {'baselines': [], 'cases': [], 'summary': {
                    'complete': True, 'covered': 47, 'failures': 0}}
            with patch.object(suite, 'run_suite', side_effect=fake_run), redirect_stdout(io.StringIO()):
                code = suite.main(['--generate', '--suite-dir', directory,
                                   '--snapshot-binary', '/usr/bin/true', '--watch-file', str(watched),
                                   '--checker', '/usr/bin/true'])
            self.assertEqual(code, 3)
            report = json.loads((path / 'report.json').read_bytes())
            self.assertFalse(report['valid'])
            self.assertFalse(report['summary']['complete'])
            self.assertEqual(report['summary']['covered'], 0)

    def test_report_cannot_overwrite_pins_or_manifest(self):
        with tempfile.TemporaryDirectory(dir='/private/tmp') as directory:
            path = Path(directory)
            pins = path / 'pins.json'
            pins.write_bytes(suite.DEFAULT_PINS.read_bytes())
            for target in ('pins.json', 'manifest.json'):
                with patch.object(suite, 'run_suite') as execute:
                    code = suite.main(['--generate', '--suite-dir', directory, '--pins', str(pins),
                                       '--report', str(path / target), '--checker', '/usr/bin/true'])
                self.assertEqual(code, 3)
                execute.assert_not_called()


if __name__ == '__main__':
    unittest.main(verbosity=2)
