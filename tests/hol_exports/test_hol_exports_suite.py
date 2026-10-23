# Copyright (c) 2026 Fawad Haider. All rights reserved.
from collections import Counter
import copy
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from contextlib import redirect_stdout, redirect_stderr
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
import test_hol_exports as suite


def result(code, timeout=False):
    return {'exit_code': code, 'timed_out': timeout, 'stdout': '', 'stderr': '', 'elapsed_seconds': 0}


def decode(rows):
    """Resolve wire references and erase only binder annotations; this is not a type checker."""
    names, levels, exprs = {0: ()}, {0: ('zero',)}, {}
    declarations = []
    def header(item):
        out = copy.deepcopy(item)
        out.update(name=names[item['name']], levelParams=[names[n] for n in item['levelParams']], type=exprs[item['type']])
        for field in ('all', 'ctors'):
            if field in item:
                out[field] = [names[n] for n in item[field]]
        if 'induct' in item:
            out['induct'] = names[item['induct']]
        if 'value' in item:
            out['value'] = exprs[item['value']]
        if 'rules' in item:
            out['rules'] = [{'ctor': names[r['ctor']], 'nfields': r['nfields'], 'rhs': exprs[r['rhs']]} for r in item['rules']]
        return out
    for row in rows:
        if 'in' in row:
            assert row['in'] not in names
            names[row['in']] = names[row['str']['pre']] + (row['str']['str'],)
        elif 'il' in row:
            assert row['il'] not in levels
            levels[row['il']] = ('succ', levels[row['succ']]) if 'succ' in row else ('param', names[row['param']])
        elif 'ie' in row:
            assert row['ie'] not in exprs
            if 'bvar' in row:
                value = ('var', row['bvar'])
            elif 'sort' in row:
                value = ('sort', levels[row['sort']])
            elif 'natVal' in row:
                value = ('literal', row['natVal'])
            elif 'const' in row:
                value = ('const', names[row['const']['name']], tuple(levels[u] for u in row['const']['us']))
            elif 'app' in row:
                value = ('app', exprs[row['app']['fn']], exprs[row['app']['arg']])
            else:
                tag = next(k for k in ('lam', 'forallE') if k in row)
                names[row[tag]['name']]
                assert row[tag]['binderInfo'] in ('default', 'implicit', 'strictImplicit', 'instImplicit')
                value = (tag, exprs[row[tag]['type']], exprs[row[tag]['body']])
            exprs[row['ie']] = value
        elif 'inductive' in row:
            block = {kind: [header(item) for item in row['inductive'][kind]] for kind in ('types', 'ctors', 'recs')}
            block['ctors'].sort(key=lambda c: c['name'])
            declarations.append(('inductive', block))
        elif 'def' in row:
            declarations.append(('def', header(row['def'])))
        else:
            assert 'meta' in row
    return declarations


def closed(expr, depth=0):
    if expr[0] == 'var':
        return 0 <= expr[1] < depth
    if expr[0] in ('const', 'sort', 'literal'):
        return True
    if expr[0] == 'app':
        return closed(expr[1], depth) and closed(expr[2], depth)
    return closed(expr[1], depth) and closed(expr[2], depth + 1)


class HolExportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest, cls.files = suite.plan_suite()
        cls.baselines = {b['family']: b for b in cls.manifest['baselines']}

    def rows(self, case_id):
        case = next(c for c in self.manifest['cases'] if c['id'] == case_id)
        return suite.rows_of(self.files[case['path']])

    def baseline(self, family):
        return suite.rows_of(self.files[self.baselines[family]['path']])

    def test_deterministic_persisted_metadata_and_hashes(self):
        self.assertEqual((self.manifest, self.files), suite.plan_suite())
        self.assertEqual(len(self.manifest['baselines']), 7)
        self.assertEqual(len(self.manifest['cases']), 97)
        self.assertEqual(Counter(c['expected'] for c in self.manifest['cases']), {'accept': 46, 'reject': 51})
        for case in self.manifest['cases']:
            self.assertEqual(case['sha256'], suite.sha256(self.files[case['path']]))
            self.assertEqual(case['size'], len(self.files[case['path']]))
            self.assertEqual(case['baseline_sha256'], self.baselines[case['family']]['sha256'])
            self.assertTrue(case['rationale'])
            self.assertTrue(case['dimension'])

    def test_every_reference_is_backward_defined_and_terms_are_closed(self):
        for path, raw in self.files.items():
            with self.subTest(path=path):
                for kind, declaration in decode(suite.rows_of(raw)):
                    if kind == 'def':
                        self.assertTrue(closed(declaration['type']))
                        self.assertTrue(closed(declaration['value']))
                    else:
                        for group in declaration.values():
                            for entry in group:
                                self.assertTrue(closed(entry['type']))
                                for rule in entry.get('rules', []):
                                    self.assertTrue(closed(rule['rhs']))

    def test_transport_controls_preserve_decoded_declarations(self):
        for family in ('nat', 'bool', 'empty', 'tree'):
            before = decode(self.baseline(family))
            for label in ('table-ids', 'grouped-tables', 'binder-name', 'binder-info', 'forward-declarations'):
                with self.subTest(family=family, label=label):
                    after = decode(self.rows(family + '/control-' + label))
                    self.assertCountEqual(after, before)
            if family != 'empty':
                self.assertEqual(decode(self.rows(family + '/control-constructor-table-order')), before)

    def test_forward_cases_move_uses_before_owner_declarations_not_wire_nodes(self):
        for family in self.baselines:
            rows = self.rows(family + '/control-forward-declarations')
            decls = [r for r in rows if 'def' in r or 'inductive' in r]
            self.assertIn('def', decls[0])
            self.assertIn('inductive', decls[-1])
            first_decl = next(i for i, r in enumerate(rows) if 'def' in r or 'inductive' in r)
            self.assertFalse(any(any(key in row for key in ('in', 'il', 'ie')) for row in rows[first_decl:]))
            decode(rows)

    def test_nat_baseline_is_canonical_but_literal_free(self):
        rows = self.baseline('nat')
        self.assertFalse(any('natVal' in r for r in rows))
        block = next(d for kind, d in decode(rows) if kind == 'inductive')
        self.assertEqual(block['types'][0]['name'], ('Nat',))
        self.assertEqual(block['types'][0]['ctors'], [('Nat', 'zero'), ('Nat', 'succ')])

    def test_tree_has_independent_expected_minor_and_recursive_rule_shape(self):
        block = [d for kind, d in decode(self.baseline('tree')) if kind == 'inductive'][1]
        const = lambda parts: ('const', tuple(parts), ())
        var = lambda i: ('var', i)
        app = lambda f, a: ('app', f, a)
        pi = lambda a, b: ('forallE', a, b)
        lam = lambda a, b: ('lam', a, b)
        tree, empty = const(['HolExports', 'Tree']), const(['Empty'])
        tip, label, node = [const(['HolExports', 'Tree', n]) for n in ('tip', 'label', 'node')]
        motive = pi(tree, ('sort', ('param', ('u',))))
        m0 = app(var(0), tip)
        m1 = pi(empty, app(var(2), app(label, var(0))))
        m2 = pi(tree, pi(tree, pi(app(var(4), var(1)), pi(app(var(5), var(1)),
                   app(var(6), app(app(node, var(3)), var(2)))))))
        expected_type = pi(motive, pi(m0, pi(m1, pi(m2, pi(tree, app(var(4), var(0)))))))
        self.assertEqual(block['recs'][0]['type'], expected_type)
        recur = ('const', ('HolExports', 'Tree', 'rec'), (('param', ('u',)),))
        for index in (5, 4, 3, 2):
            recur = app(recur, var(index))
        rhs = app(app(app(app(var(2), var(1)), var(0)), app(recur, var(1))), app(recur, var(0)))
        expected_rhs = lam(motive, lam(m0, lam(m1, lam(m2, lam(tree, lam(tree, rhs))))))
        self.assertEqual(block['recs'][0]['rules'][2]['rhs'], expected_rhs)
        self.assertEqual(block['recs'][0]['rules'][2]['nfields'], 2)

    def test_tree_iota_case_requires_conversion_in_a_dependent_type(self):
        declaration = decode(self.rows('tree/control-iota-dependent-index'))[-1][1]
        typ, body = declaration['type'], declaration['value']
        self.assertEqual(typ[0], 'forallE')
        self.assertEqual(body[0], 'lam')
        self.assertEqual(body[2][2], ('var', 0))
        self.assertNotEqual(typ[2][1][2], typ[2][2][2])
        self.assertIn('HolExports', repr(typ[2][2]))
        self.assertIn("'rec'", repr(typ[2][2]))

    def test_large_literals_remain_exact_decimal_text_and_unequal_indices(self):
        for family, n in suite.LARGE_VALUES.items():
            baseline = self.baseline(family)
            self.assertTrue(all(r['natVal'] == str(n) for r in baseline if 'natVal' in r))
            for label, other in (('unequal-next', n + 1), ('unequal-previous', n - 1), ('unequal-word-wrap', n + 2 ** 64)):
                rows = self.rows(family + '/' + label)
                values = {r['natVal'] for r in rows if 'natVal' in r}
                self.assertEqual(values, {str(n), str(other)})
                self.assertTrue(all(isinstance(v, str) and v.isdecimal() for v in values))
                decl = decode(rows)[-1][1]
                premise = decl['type'][2][1][2]
                conclusion = decl['type'][2][2][2]
                self.assertEqual(premise, ('literal', str(n)))
                self.assertEqual(conclusion, ('literal', str(other)))
                self.assertEqual(decl['value'][2][2], ('var', 0))
            leading = self.rows(family + '/control-leading-zero')
            self.assertEqual({int(r['natVal']) for r in leading if 'natVal' in r}, {n})

    def test_nested_guards_distinguish_structural_and_dotted_names(self):
        bad = decode(self.rows('tree/nested-field'))
        first = bad[0][1]
        self.assertEqual(first['types'][0]['name'], ('_nested', 'Payload'))
        self.assertEqual(first['ctors'], [])
        tree = [d for kind, d in bad if kind == 'inductive'][1]
        label = next(c for c in tree['ctors'] if c['name'][-1] == 'label')
        self.assertEqual(label['type'][1], ('const', ('_nested', 'Payload'), ()))
        dotted = decode(self.rows('tree/control-dotted-field'))[0][1]
        self.assertEqual(dotted['types'][0]['name'], ('_nested.Payload',))

    def test_nonaccepting_baselines_gate_and_decline_never_becomes_rejection(self):
        for outcome in (result(1), result(2), result(3), result(-9, True)):
            calls = []
            def execute(command, *args):
                calls.append(command)
                return outcome
            report = suite.run_suite(self.manifest, Path('/private/tmp/fake-hol-suite'), ['checker'], 1, 32, execute=execute)
            self.assertEqual(len(calls), 7)
            self.assertEqual(report['summary']['covered'], 0)
            self.assertEqual(report['summary']['statuses'], {'not_covered': 97})
        calls = []
        def decline_after_baselines(command, *args):
            calls.append(command)
            return result(0 if len(calls) <= 7 else 2)
        report = suite.run_suite(self.manifest, Path('/private/tmp/fake-hol-suite'), ['checker'], 1, 32,
                                 execute=decline_after_baselines)
        self.assertEqual(report['summary']['statuses'], {'declined': 97})
        self.assertEqual(report['summary']['covered'], 0)
        self.assertFalse(report['summary']['complete'])
        self.assertEqual(suite.observed_codes(report['cases'])['2'], 97)
        self.assertEqual(suite.observed_codes(report['cases'])['1'], 0)

    def test_codes_faults_and_literal_argv_are_distinct(self):
        self.assertEqual(suite.classify(result(0), 'reject'), 'false_accept')
        self.assertEqual(suite.classify(result(1), 'accept'), 'false_reject')
        self.assertEqual(suite.classify(result(2), 'reject'), 'declined')
        self.assertEqual(suite.classify(result(3), 'reject'), 'fault')
        self.assertEqual(suite.classify(result(-9, True), 'reject'), 'timeout')
        command = ['checker', '--socket', '/private/tmp/spaces ; $(literal)']
        calls = []
        def execute(argv, *args):
            calls.append(argv)
            return result(0)
        report = suite.run_suite(self.manifest, Path('/private/tmp/fake-hol-suite'), command, 1, 32, execute=execute)
        self.assertTrue(all(call[:-1] == command for call in calls))
        self.assertEqual(report['summary']['statuses']['false_accept'], 51)
        self.assertEqual(suite.observed_codes([{'execution_error': 'missing', 'status': 'not_covered'}])['other_fault'], 1)

    def test_old_suites_pin_mismatch_and_changed_artifacts_are_protected(self):
        for name in ('arena', 'tests/arena', 'tests/metadata', 'tests/coherent'):
            with self.assertRaises(ValueError):
                suite.safe_suite_dir(ROOT / name, suite.DEFAULT_MANIFEST)
        with tempfile.TemporaryDirectory(dir='/private/tmp') as directory:
            path = Path(directory)
            suite.materialize(path, self.manifest, self.files)
            suite.validate_materialized(path, self.manifest, self.files)
            first = path / self.manifest['cases'][0]['path']
            first.write_bytes(first.read_bytes() + b'\n')
            with self.assertRaises(ValueError):
                suite.materialize(path, self.manifest, self.files)
            with self.assertRaises(ValueError):
                suite.validate_materialized(path, self.manifest, self.files)
            pins = json.loads(suite.DEFAULT_PINS.read_bytes())
            pins['seeds'][0]['sha256'] = '0' * 64
            pinfile = path / 'pins.json'
            pinfile.write_text(json.dumps(pins))
            with self.assertRaises(ValueError):
                suite.plan_suite(suite.DEFAULT_MANIFEST, pinfile)

    def test_changed_watched_input_invalidates_and_zeroes_coverage(self):
        with tempfile.TemporaryDirectory(dir='/private/tmp') as directory:
            path = Path(directory)
            watched = path / 'loaded-source'
            watched.write_text('before')
            def fake_run(*args):
                watched.write_text('after')
                return {'baselines': [], 'cases': [], 'summary': {'complete': True, 'covered': 97, 'failures': 0}}
            with patch.object(suite, 'run_suite', side_effect=fake_run), redirect_stdout(io.StringIO()):
                code = suite.main(['--generate', '--suite-dir', directory, '--watch-file', str(watched),
                                   '--checker', '/usr/bin/true'])
            self.assertEqual(code, 3)
            report = json.loads((path / 'report.json').read_bytes())
            self.assertFalse(report['valid'])
            self.assertEqual(report['summary']['covered'], 0)
            self.assertIn('warm HOL', report['provenance_limit'])

    def test_report_cannot_overwrite_manifest(self):
        with tempfile.TemporaryDirectory(dir='/private/tmp') as directory:
            with patch.object(suite, 'run_suite') as execute, redirect_stderr(io.StringIO()):
                code = suite.main(['--generate', '--suite-dir', directory, '--report', directory + '/manifest.json',
                                   '--checker', '/usr/bin/true'])
            self.assertEqual(code, 3)
            execute.assert_not_called()


if __name__ == '__main__':
    unittest.main(verbosity=2)
