# Copyright (c) 2026 Fawad Haider. All rights reserved.
import copy
import hashlib
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
import test_metadata_mutations as suite


def result(code, timed_out=False):
    return {'exit_code': code, 'timed_out': timed_out, 'stdout': '', 'stderr': '',
            'elapsed_seconds': 0.0}


class MutationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest, cls.files = suite.plan_suite(suite.DEFAULT_MANIFEST, suite.DEFAULT_PINS)

    def test_substantial_deterministic_single_edit_suite(self):
        repeated, files = suite.plan_suite(suite.DEFAULT_MANIFEST, suite.DEFAULT_PINS)
        self.assertEqual((self.manifest, self.files), (repeated, files))
        self.assertGreaterEqual(len(self.manifest['cases']), 100)
        self.assertEqual(len(self.manifest['baselines']), 5)
        self.assertGreaterEqual(sum(c['expected'] == 'accept' for c in self.manifest['cases']), 20)
        for case in self.manifest['cases']:
            with self.subTest(case=case['id']):
                raw = self.files[case['path']]
                self.assertEqual(hashlib.sha256(raw).hexdigest(), case['sha256'])
                baseline = next(b for b in self.manifest['baselines'] if b['family'] == case['family'])
                rows = [json.loads(line) for line in self.files[baseline['path']].splitlines()]
                edit = case['edit']
                target = rows[edit['record'] - 1]
                for part in edit['path'][:-1]:
                    target = target[part]
                self.assertEqual(target[edit['path'][-1]], edit['before'])
                self.assertNotEqual(edit['before'], edit['after'])
                target[edit['path'][-1]] = copy.deepcopy(edit['after'])
                self.assertEqual([json.loads(line) for line in raw.splitlines()], rows)
                self.assertTrue(case['rationale'])

    def test_declines_never_count_as_rejections(self):
        for expected in ('accept', 'reject'):
            self.assertEqual(suite.classify(result(2), expected), 'declined')
            self.assertEqual(suite.classify(result(3), expected), 'fault')
            self.assertEqual(suite.classify(result(-9, True), expected), 'timeout')
        self.assertEqual(suite.classify(result(0), 'reject'), 'false_accept')
        self.assertEqual(suite.classify(result(1), 'accept'), 'false_reject')

    def test_every_wire_reference_remains_defined(self):
        def refs(value, names, levels, expressions, kind):
            if kind == 'header':
                self.assertIn(value['name'], names)
                self.assertTrue(set(value['levelParams']) <= names)
                self.assertIn(value['type'], expressions)
        for case in self.manifest['cases']:
            with self.subTest(case=case['id']):
                names, levels, expressions = {0}, {0}, set()
                for row in map(json.loads, self.files[case['path']].splitlines()):
                    if 'in' in row:
                        item = row.get('str', row.get('num'))
                        self.assertIn(item['pre'], names)
                        names.add(row['in'])
                    elif 'il' in row:
                        if 'param' in row:
                            self.assertIn(row['param'], names)
                        elif 'succ' in row:
                            self.assertIn(row['succ'], levels)
                        else:
                            self.assertTrue(set(row.get('max', row.get('imax'))) <= levels)
                        levels.add(row['il'])
                    elif 'ie' in row:
                        if 'sort' in row:
                            self.assertIn(row['sort'], levels)
                        if 'const' in row:
                            self.assertIn(row['const']['name'], names)
                            self.assertTrue(set(row['const']['us']) <= levels)
                        if 'app' in row:
                            self.assertTrue(set(row['app'].values()) <= expressions)
                        for tag in ('lam', 'forallE'):
                            if tag in row:
                                self.assertIn(row[tag]['name'], names)
                                self.assertIn(row[tag]['type'], expressions)
                                self.assertIn(row[tag]['body'], expressions)
                        expressions.add(row['ie'])
                    elif 'inductive' in row:
                        for kind in ('types', 'ctors', 'recs'):
                            for item in row['inductive'][kind]:
                                refs(item, names, levels, expressions, 'header')
                                if 'all' in item:
                                    self.assertTrue(set(item['all']) <= names)
                                if 'ctors' in item:
                                    self.assertTrue(set(item['ctors']) <= names)
                                if 'induct' in item:
                                    self.assertIn(item['induct'], names)
                                for rule in item.get('rules', []):
                                    self.assertIn(rule['ctor'], names)
                                    self.assertIn(rule['rhs'], expressions)
                    elif 'def' in row:
                        refs(row['def'], names, levels, expressions, 'header')
                        self.assertIn(row['def']['value'], expressions)

    def test_nonaccepting_baselines_gate_every_mutation(self):
        for code in (1, 2, 3):
            calls = []
            def execute(command, path, *args):
                calls.append((command, path))
                return result(code)
            report = suite.run_suite(self.manifest, Path('/private/tmp/synthetic-suite'),
                                     ['checker', '--flag', 'value with spaces'], 1, 100,
                                     execute=execute)
            self.assertEqual(len(calls), 5)
            self.assertTrue(all(c['status'] == 'not_covered' for c in report['cases']))
            self.assertEqual(report['summary']['covered'], 0)
            self.assertFalse(report['summary']['complete'])

    def test_argv_is_preserved_and_expectations_not_passed(self):
        calls = []
        def execute(command, path, *args):
            calls.append(command)
            return result(0)
        command = ['checker', '--option', 'value with spaces; $(not-shell)']
        report = suite.run_suite(self.manifest, Path('/private/tmp/synthetic-suite'), command,
                                 1, 100, execute=execute)
        self.assertTrue(all(c[:-1] == command for c in calls))
        self.assertEqual(report['summary']['statuses']['false_accept'],
                         sum(c['expected'] == 'reject' for c in self.manifest['cases']))
        self.assertFalse(report['summary']['complete'])

    def test_pin_mismatch_fails_closed(self):
        pins = json.loads(suite.DEFAULT_PINS.read_text())
        pins['baselines'][0]['sha256'] = '0' * 64
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'pins.json'
            path.write_text(json.dumps(pins))
            with self.assertRaises(ValueError):
                suite.plan_suite(suite.DEFAULT_MANIFEST, path)

    def test_unsafe_output_location_refused(self):
        for path in (ROOT / 'arena', ROOT / 'tests/arena', ROOT):
            with self.assertRaises(ValueError):
                suite.safe_suite_dir(path, suite.DEFAULT_MANIFEST)

    def test_changed_persisted_file_is_never_overwritten_or_executed(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory).resolve()
            suite.materialize(path, self.manifest, self.files)
            suite.validate_materialized(path, self.manifest, self.files)
            target = path / self.manifest['cases'][0]['path']
            target.write_bytes(target.read_bytes() + b'\n')
            with self.assertRaises(ValueError):
                suite.validate_materialized(path, self.manifest, self.files)
            with self.assertRaises(ValueError):
                suite.materialize(path, self.manifest, self.files)

    def test_changed_checker_dependency_invalidates_report(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            watched = path / 'checker-dependency'
            watched.write_text('before')
            def fake_run(*args):
                watched.write_text('after')
                return {'baselines': [], 'cases': [], 'summary': {
                    'complete': True, 'covered': 100, 'failures': 0}}
            with patch.object(suite, 'run_suite', side_effect=fake_run), redirect_stdout(io.StringIO()):
                code = suite.main(['--generate', '--suite-dir', directory,
                                   '--snapshot-binary', '/usr/bin/true', '--watch-file', str(watched),
                                   '--checker', '/usr/bin/true'])
            self.assertEqual(code, 3)
            report = json.loads((path / 'report.json').read_bytes())
            self.assertFalse(report['valid'])
            self.assertFalse(report['summary']['complete'])
            self.assertEqual(report['summary']['covered'], 0)
            self.assertFalse(report['checker_identity']['unchanged'])

    def test_script_snapshot_is_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            script = Path(directory) / 'checker'
            script.write_text('#!/bin/sh\nexit 0\n')
            script.chmod(0o700)
            with self.assertRaises(ValueError):
                with suite.checker_snapshot([str(script)], script, []):
                    self.fail('script snapshot must not be used')


if __name__ == '__main__':
    unittest.main(verbosity=2)
