"""Offline source/harness checks, not HOL or Arena proof tests."""
import unittest

import run


class SourceTests(unittest.TestCase):
    def setUp(self):
        self.root = run.ROOT
        self.before = (self.root / 'tests/hol_add_body/baseline/primitive_validation.ml').read_text()
        self.after = (self.root / 'hol/primitive_validation.ml').read_text()

    def test_only_three_production_insertions(self):
        prefix = self.after.index('let l4_prim_checked_conversion = prove')
        suffix = self.after.index('module Lean4hol_primitive : sig', prefix)
        restored = self.after[:prefix] + self.after[suffix:]
        prefix = restored.index('  let add_body_typing fuel env b ty hop =')
        suffix = restored.index('  let check_definition ?(fuel=100000)', prefix)
        restored = restored[:prefix] + restored[suffix:]
        restored = run.replace_once(restored,
            'let hb=if op=0 then add_body_typing fuel env b d.Env.typ hop\n'
            '        else if (op=4 || op=5)', 'let hb=if (op=4 || op=5)')
        self.assertEqual(restored, self.before)

    def test_native_and_admission_rule_counts_not_changed(self):
        import json
        pins = json.loads((self.root / 'tests/hol_add_body/baseline/source-pins.json').read_text())['source_sha256']
        for path in ('hol/environment_rules.ml', 'hol/primitive_contracts.ml', 'hol/environment.ml'):
            self.assertEqual(run.composition.digest(self.root / path), pins[path])

    def test_probe_is_exact_source_plus_declared_instrumentation(self):
        probe = run.instrument(self.after)
        self.assertEqual(probe.count('module Add_body_probe : sig'), 1)
        self.assertEqual(probe.count('val add_body_typing :'), 1)
        self.assertIn('Lean4hol_env.check ?fuel env g b ty', probe)
        self.assertIn('None -> Lean4hol_env.convert ?fuel env g a b ty', probe)
        self.assertNotIn('add_body_probe_conversion_override', self.after)
        self.assertNotIn('val add_body_typing :', self.after)

    def test_changed_or_duplicate_anchor_fails(self):
        with self.assertRaises(ValueError):
            run.instrument(self.after.replace('  module Env = Lean4hol_env', '  module Env = Other'))
        with self.assertRaises(ValueError):
            run.instrument(self.after + '\n  module Env = Lean4hol_env\n')

    def test_all_jobs_bounded(self):
        jobs = run.jobs()
        self.assertEqual(set(jobs), set(run.PHASES))
        self.assertEqual(len(jobs), 6)
        self.assertTrue(all(job['limit'] == 180 for job in jobs.values()))

    def test_markers_fail_closed(self):
        for phase, job in run.jobs().items():
            valid = ('HOL_PRIMITIVE_FACTORY_REQUIRED_PASSED\nHOL_PRIMITIVE_FACTORY_TESTS_PASSED 64\n'
                     if phase == 'factory' else f'ADD_BODY_TESTS_PASSED {phase} 30\n')
            self.assertTrue(run.composition.inspect_log(valid, job['markers'])[2])
            self.assertFalse(run.composition.inspect_log('', job['markers'])[2])
            self.assertFalse(run.composition.inspect_log(valid + valid, job['markers'])[2])
            self.assertFalse(run.composition.inspect_log(valid + 'Exception: Failure "bad"\n', job['markers'])[2])


if __name__ == '__main__':
    unittest.main()
