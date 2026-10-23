"""Offline regression tests for routine-suite scope. No source files are edited."""
from contextlib import contextmanager
from copy import deepcopy
import hashlib
from pathlib import Path
import unittest
from unittest.mock import patch

import run
import test_offline


@contextmanager
def changed_source(relative, transform):
    path = run.ROOT / relative
    original = path.read_text()
    changed = transform(original)
    if changed == original:
        raise AssertionError('Mutation did not change the source: ' + relative)
    read_text, read_bytes = Path.read_text, Path.read_bytes

    def text(p, *args, **kwargs):
        return changed if p == path else read_text(p, *args, **kwargs)

    def binary(p, *args, **kwargs):
        return changed.encode() if p == path else read_bytes(p, *args, **kwargs)

    with patch.object(Path, 'read_text', text), patch.object(Path, 'read_bytes', binary):
        yield original, changed


class Maintenance(unittest.TestCase):
    def routine_result(self, method=None):
        suite = (unittest.TestSuite([test_offline.Offline(method)]) if method else
                 unittest.defaultTestLoader.loadTestsFromTestCase(test_offline.Offline))
        result = unittest.TestResult()
        suite.run(result)
        self.assertEqual(result.errors, [], 'Mutation caused an infrastructure error, not an assertion failure')
        self.assertGreater(result.testsRun, 0)
        return result

    def require_routine_pass(self):
        result = self.routine_result()
        self.assertEqual(result.failures, [])
        self.assertTrue(result.wasSuccessful())

    def require_routine_failure(self, method):
        result = self.routine_result(method)
        self.assertFalse(result.wasSuccessful())
        self.assertEqual(len(result.failures), 1)

    def test_unrelated_registered_job_allowed(self):
        original = run.composition.jobs()
        self.assertNotIn('unrelated-safety-maintenance-probe', original)
        extended = dict(original, **{'unrelated-safety-maintenance-probe': {
            'limit': 17, 'source': 'not executed', 'markers': [], 'options': {}}})
        with patch.object(run.composition, 'jobs', return_value=extended):
            self.assertEqual(len(run.composition.jobs()), len(original) + 1)
            self.require_routine_pass()

    def test_unrelated_core_comment_allowed(self):
        with changed_source('hol/core.ml', lambda s: s + '\n(* Unrelated maintenance comment. *)\n') as (old, new):
            self.assertNotEqual(hashlib.sha256(old.encode()).hexdigest(),
                                run.composition.digest(run.ROOT / 'hol/core.ml'))
            self.assertEqual((run.ROOT / 'hol/core.ml').read_text(), new)
            self.require_routine_pass()

    def test_unrelated_frontend_comments_allowed(self):
        for relative in ('frontend/hol_check.ml', 'frontend/hol_server.ml'):
            with self.subTest(path=relative), changed_source(relative, lambda s: s + '\n(* Unrelated frontend change. *)\n'):
                self.require_routine_pass()

    def test_unrelated_environment_comment_allowed(self):
        with changed_source('hol/environment.ml', lambda s: s + '\n(* Outside fragment_check. *)\n'):
            self.require_routine_pass()

    def test_routine_never_reads_historical_baseline(self):
        read_text, read_bytes = Path.read_text, Path.read_bytes

        def text(path, *args, **kwargs):
            self.assertNotIn('baseline', path.parts)
            return read_text(path, *args, **kwargs)

        def binary(path, *args, **kwargs):
            self.assertNotIn('baseline', path.parts)
            return read_bytes(path, *args, **kwargs)

        with patch.object(Path, 'read_text', text), patch.object(Path, 'read_bytes', binary):
            self.require_routine_pass()

    def test_safety_job_violations_fail(self):
        for mutation in ('missing', 'renamed', 'wrong_phase', 'extra'):
            jobs = deepcopy(run.jobs())
            if mutation == 'missing':
                jobs.pop('single')
            elif mutation == 'renamed':
                jobs['not-general'] = jobs.pop('general')
            elif mutation == 'wrong_phase':
                jobs['single']['options']['SAFETY_GROUP'] = 'general'
            else:
                jobs['extra-safety-group'] = deepcopy(jobs['general'])
            with self.subTest(mutation=mutation), patch.object(run, 'jobs', return_value=jobs):
                self.require_routine_failure('test_limits_and_separate_registry')

    def test_safety_cap_violations_fail(self):
        for phase in ('general', 'arena'):
            jobs = deepcopy(run.jobs())
            jobs[phase]['limit'] = 181
            with self.subTest(phase=phase), patch.object(run, 'jobs', return_value=jobs):
                self.require_routine_failure('test_limits_and_separate_registry')
        with patch.object(run, 'LIMIT', 181):
            self.require_routine_failure('test_limits_and_separate_registry')

    def test_safety_guard_violations_fail(self):
        for mutation in ('hyp th<>[] || ', 'exact(body_term frag r)h',
                         'canonical_fresh=get(check_fresh s canonical)', 'temporary fragment identity'):
            with self.subTest(mutation=mutation), changed_source('hol/safety_admission.ml',
                    lambda s, m=mutation: s.replace(m, 'MUTATED_GUARD', 1)):
                self.require_routine_failure('test_hypothesis_and_view_guards')

    def test_helper_obligation_violations_fail(self):
        for mutation in ('List.iter (fun d -> validate st [] (validation_terms d)) entries;',
                         'let ctx=Native.context st g in', 'ignore(Native.infer_sort st g a);',
                         'let h=Native.check_i st g e a in', 'guarded (mk_conj(node "l4_econtext" [qe;qg],'):
            with self.subTest(mutation=mutation), changed_source('hol/environment.ml',
                    lambda s, m=mutation: self.mutate_helper(s, m)):
                self.require_routine_failure('test_fragment_helper_contract')

    @staticmethod
    def mutate_helper(source, mutation):
        start = source.index('  let fragment_check ')
        return source[:start] + source[start:].replace(mutation, 'MUTATED_OBLIGATION', 1)

    def test_loading_guard_violation_fails(self):
        jobs = deepcopy(run.jobs())
        jobs['general']['markers'].remove(run.LOAD_MARKERS[0])
        with patch.object(run, 'jobs', return_value=jobs):
            self.require_routine_failure('test_loading_markers_required_not_quoted')


if __name__ == '__main__':
    unittest.main()
