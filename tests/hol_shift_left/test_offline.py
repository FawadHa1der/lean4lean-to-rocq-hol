"""Offline harness/source checks, not native proof verification."""
from pathlib import Path
import unittest

import run


class OfflineTests(unittest.TestCase):
    def test_all_native_jobs_are_bounded_and_source_exists(self):
        self.assertEqual(len(run.jobs()), 10)
        for job in run.jobs().values():
            self.assertEqual(job['limit'], 180)
            self.assertTrue((run.ROOT / 'tests/hol_composition/drivers' / job['source_file']).is_file())

    def test_marker_protocol(self):
        for phase, job in run.jobs().items():
            valid = f'SHIFT_LEFT_DERIVED_PASSED {phase} 7\n'
            for prefix in ('', '#   '):
                self.assertTrue(run.composition.inspect_log(prefix + valid, job['markers'])[2])
            for bad in ('', valid + valid, valid + 'Exception: Failure "bad"\n'):
                self.assertFalse(run.composition.inspect_log(bad, job['markers'])[2])

    def test_no_rule_or_axiom_definitions_in_new_modules(self):
        for name in ('shift_left_context_evaluation.ml', 'derived_shift_left.ml', 'shift_left_budget.ml'):
            source = (run.ROOT / 'hol' / name).read_text()
            for forbidden in ('new_axiom', 'new_inductive_definition', 'Obj.magic'):
                self.assertNotIn(forbidden, source)

    def test_allocation_guard_precedes_numeric_quotation(self):
        source = (run.ROOT / 'hol/derived_shift_left.ml').read_text()
        evaluate = source[source.index('  let evaluate ?'):source.index('  let check_result ?')]
        self.assertLess(evaluate.index('allocation_bound'), evaluate.index('natural left'))
        self.assertIn('REWRITE_CONV [MULT_CLAUSES] THENC NUM_REDUCE_CONV', evaluate)

    def test_changed_input_induction_is_generalized(self):
        source = (run.ROOT / 'hol/shift_left_context_evaluation.ml').read_text()
        self.assertIn('let induction_goal k=mk_forall(m,goal m k)', source)
        self.assertIn('SPEC doubled ih', source)
        self.assertIn('l4_edef_instantiation', source)
        self.assertIn('typed_nat one', source)

    def test_explicit_resource_tests_do_not_count_as_proof_acceptances(self):
        source = (run.ROOT / 'tests/hol_composition/drivers/shift_left_cases_tests.ml').read_text()
        self.assertIn('Error {kind=Resource;_}->true', source)
        self.assertIn('assumed full premise remains conditional', source)
        self.assertIn('every exact typed or scope premise required', source)

    def test_probe_only_renames_and_observes_numeric_conversion(self):
        source = (run.ROOT / 'hol/derived_shift_left.ml').read_text()
        probe = run.evaluation_probe(source)
        self.assertTrue(probe.startswith(run.PROBE_PREFIX))
        restored = probe[len(run.PROBE_PREFIX):].replace(
            'module Shift_left_evaluation_probe : sig', 'module Lean4hol_derived_shift_left : sig')
        restored = restored.replace('THENC shift_left_probe_num_reduce) expression in',
                                    'THENC NUM_REDUCE_CONV) expression in')
        self.assertEqual(source, restored)
        self.assertNotIn('shift_left_probe', source)
        self.assertIn('NUM_REDUCE_CONV tm', run.PROBE_PREFIX)
        self.assertIn('not(aconv tm `0`)', run.PROBE_PREFIX)

    def test_changed_or_repeated_probe_anchor_is_refused(self):
        source = (run.ROOT / 'hol/derived_shift_left.ml').read_text()
        with self.assertRaises(ValueError):
            run.evaluation_probe(source.replace('THENC NUM_REDUCE_CONV) expression in',
                                                'THENC OTHER_CONV) expression in'))
        with self.assertRaises(ValueError):
            run.evaluation_probe(source + '\nmodule Lean4hol_derived_shift_left : sig\n')

    def test_preflight_has_no_logical_judgment_or_proof_dependency(self):
        source = (run.ROOT / 'hol/shift_left_budget.ml').read_text()
        self.assertIn('type decision = Allowed | Invalid of string | Exhausted of string', source)
        for forbidden in ('thm', 'l4_checked', 'l4_edef', 'NUM_REDUCE_CONV',
                          'Lean4hol_env', 'new_axiom', 'needs ', 'prove('):
            self.assertNotIn(forbidden, source)

    def test_future_native_gate_checks_conversion_boundary_and_classification(self):
        source = (run.ROOT / 'tests/hol_composition/drivers/shift_left_cases_tests.ml').read_text()
        self.assertIn('shift_left_probe_require_zero:=true', source)
        self.assertIn('shift_left_probe_forbid_numeric:=true', source)
        self.assertIn('!shift_left_probe_numeric_inputs=[`0`]', source)
        self.assertIn('actual result fits but conservative bound declines', source)
        self.assertIn('allocation permission is not a claimed-result verdict', source)


if __name__ == '__main__':
    unittest.main()
