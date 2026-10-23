#!/usr/bin/env python3
"""Focused synthetic unified harness controls, not logical verdict tests."""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('unified_wrapper', ROOT / 'scripts/test-hol-unified.py')
wrapper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(wrapper)
runner = wrapper.driver
EVIDENCE = Path(tempfile.mkdtemp(prefix='unified-runner-synthetic-', dir='/private/tmp'))
RESULTS = []


class ProcessTests(unittest.TestCase):
    def session(self, mode, cap=2.0):
        directory = EVIDENCE / mode
        directory.mkdir()
        stages = wrapper.fixture_stages('unified_tests.ml', 'UNIFIED_SETUP_READY')
        stages.append(dict(stage='synthetic-2', kind='synthetic', command='SYNTHETIC_ONLY;;',
                           marker=r'UNIFIED_WORK_PASS synthetic-2 1'))
        with contextlib.redirect_stdout(io.StringIO()):
            report = runner.run_session([sys.executable,
                str(ROOT / 'tests/hol_reflection/unified_synthetic_backend.py'), mode], ROOT,
                directory, stages, cap, cleanup_cap=3.0)
        (directory / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        RESULTS.append({'mode': mode, 'report': str(directory / 'report.json')})
        self.assertTrue(report['parent_reaped'])
        self.assertTrue(report['group_absent'])
        self.assertFalse(runner.group_exists(report['pid']))
        self.assertEqual(report['cleanup_errors'], [])
        return report

    def test_separate_loads_and_unified_work(self):
        r = self.session('clean')
        self.assertTrue(r['passed'], r)
        self.assertEqual([s['marker_count'] for s in r['stages']], [1, 1, 1])

    def test_duplicate(self):
        self.assertFalse(self.session('duplicate')['passed'])

    def test_out_of_order_readiness(self):
        self.assertFalse(self.session('out-of-order')['passed'])

    def test_unexpected_unified(self):
        self.assertFalse(self.session('unexpected')['passed'])

    def test_missing(self):
        self.assertFalse(self.session('missing')['passed'])

    def test_completion_before_pass(self):
        self.assertFalse(self.session('completion-first')['passed'])

    def test_wrong_nonce(self):
        self.assertFalse(self.session('wrong-nonce')['passed'])

    def test_explicit_failure(self):
        r = self.session('failure')
        self.assertFalse(r['passed'])
        self.assertTrue(r['final_log_errors'])

    def test_late_failure(self):
        r = self.session('late-failure')
        self.assertTrue(r['stages'][-1]['passed'])
        self.assertFalse(r['passed'])
        self.assertTrue(r['final_log_errors'])

    def test_late_hol_error(self):
        self.assertFalse(self.session('late-error')['passed'])

    def test_unfinished_not_restarted(self):
        r = self.session('unfinished', cap=0.2)
        self.assertFalse(r['passed'])
        self.assertTrue(r['stages'][-1]['timed_out'])
        self.assertEqual(r['stages'][-1]['completion_count'], 0)


class InventoryTests(unittest.TestCase):
    def setUp(self):
        directory = EVIDENCE / self._testMethodName
        self.root, self.snapshot = directory / 'root', directory / 'snapshot'
        names = ['hol/reflection.ml', 'tests/hol_reflection/library_smoke.ml',
            'tests/hol_reflection/SOURCE_PINS.json', 'scripts/test-hol-reflection.py',
            'scripts/toolchain-exec.sh', 'scripts/toolchain-env.sh', 'scripts/test-hol-unified.py',
            'tests/hol_reflection/test_unified_runner.py',
            'tests/hol_reflection/unified_synthetic_backend.py']
        for rel in names:
            path = self.root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('synthetic source ' + rel)
        (self.root / 'toolchain').mkdir()
        self.before = runner.inventory(self.root)

    def test_wrapper_is_root_aware(self):
        runner.freeze_sources(self.root, self.snapshot, self.before)
        self.assertEqual(runner.inventory(self.snapshot), self.before)
        self.assertEqual(self.before['scripts/test-hol-unified.py'],
                         runner.sha(self.root / 'scripts/test-hol-unified.py'))
        self.assertNotEqual(self.before['scripts/test-hol-unified.py'], runner.sha(wrapper.HERE))

    def test_changed_wrapper_before_copy_rejected(self):
        (self.root / 'scripts/test-hol-unified.py').write_text('mutated before copy')
        with self.assertRaises(runner.RunnerFailure):
            runner.freeze_sources(self.root, self.snapshot, self.before)

    def test_snapshot_wrapper_mutation_detected(self):
        runner.freeze_sources(self.root, self.snapshot, self.before)
        path = self.snapshot / 'scripts/test-hol-unified.py'
        path.chmod(0o644)
        path.write_text('mutated snapshot')
        self.assertEqual(runner.inventory(self.root), self.before)
        self.assertNotEqual(runner.inventory(self.snapshot), self.before)

    def test_unified_plan_has_two_separate_loads(self):
        stages = wrapper.fixture_stages('unified_tests.ml', 'UNIFIED_SETUP_READY')
        self.assertEqual(len(stages), 2)
        self.assertIn('nat_instantiation_tests.ml', stages[0]['command'])
        self.assertIn('unified_tests.ml', stages[1]['command'])
        self.assertEqual(stages[0]['marker'], r'NAT_INSTANTIATION_SETUP_READY\s*')
        self.assertEqual(stages[1]['marker'], r'UNIFIED_SETUP_READY\s*')


if __name__ == '__main__':
    suite = unittest.defaultTestLoader.loadTestsFromModule(sys.modules[__name__])
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    summary = dict(scope=__doc__, tests=result.testsRun, passed=result.wasSuccessful(),
        failures=len(result.failures), errors=len(result.errors), reports=RESULTS,
        sources=runner.inventory())
    (EVIDENCE / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(EVIDENCE, flush=True)
    raise SystemExit(0 if result.wasSuccessful() else 1)
