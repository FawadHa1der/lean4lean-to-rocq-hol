#!/usr/bin/env python3
"""Bounded synthetic runner tests, NOT HOL, Lean, kernel, or Arena verdict tests."""
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('reflection_runner', ROOT / 'scripts/test-hol-reflection.py')
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)
EVIDENCE = Path(tempfile.mkdtemp(prefix='reflection-runner-synthetic-', dir='/private/tmp'))
RESULTS = []
BACKEND = Path(__file__).with_name('synthetic_backend.py')


class ProcessTests(unittest.TestCase):
    def session(self, mode, *, count=1, cap=2.0, limit=runner.MAX_LOG,
                expect_cleanup_failure=False):
        directory = EVIDENCE / (self._testMethodName + '-' + mode)
        directory.mkdir()
        stages = [dict(stage=f'synthetic-{i}', kind='synthetic', command='SYNTHETIC_ONLY;;',
                       marker=rf'COMPOSED_WORK_PASS synthetic-{i} 1') for i in range(count)]
        began = time.monotonic()
        with contextlib.redirect_stdout(io.StringIO()):
            report = runner.run_session([sys.executable, str(BACKEND), mode], ROOT, directory,
                                       stages, cap, log_limit=limit, cleanup_cap=3.0)
        report['synthetic_only'] = True
        (directory / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        RESULTS.append({'test': self._testMethodName, 'path': str(directory / 'report.json')})
        self.assertLess(time.monotonic() - began, 12)
        self.assertTrue(report['parent_reaped'], report)
        if expect_cleanup_failure:
            self.assertFalse(report['group_absent'], report)
            self.assertTrue(report['cleanup_errors'], report)
            # The fixture's descendant exits itself. Never kill an old numeric
            # PID/group to make a negative cleanup test pass.
            deadline = time.monotonic() + 3
            while runner.group_exists(report['pid']) and time.monotonic() < deadline:
                time.sleep(0.02)
        else:
            self.assertTrue(report['group_absent'], report)
            self.assertEqual(report['cleanup_errors'], [])
        self.assertFalse(runner.group_exists(report['pid']))
        return report

    def test_clean_two_stages(self):
        r = self.session('clean', count=2)
        self.assertTrue(r['passed'], r)
        self.assertEqual([s['completion_count'] for s in r['stages']], [1, 1])

    def test_error_in_stage(self):
        r = self.session('in-stage-error')
        self.assertFalse(r['passed'])
        self.assertTrue(r['final_log_errors'])

    def test_error_between_stages(self):
        r = self.session('interstage-error', count=2)
        self.assertFalse(r['passed'])
        self.assertTrue(r['final_log_errors'])

    def test_error_after_last_stage(self):
        r = self.session('final-error')
        self.assertTrue(r['stages'][0]['passed'])
        self.assertEqual(r['exit'], 0)
        self.assertFalse(r['passed'])
        self.assertTrue(r['final_log_errors'])

    def test_duplicate_marker(self):
        r = self.session('duplicate')
        self.assertFalse(r['passed'])
        self.assertTrue(r['final_log_errors'])

    def test_duplicate_completion(self):
        r = self.session('duplicate-done')
        self.assertFalse(r['passed'])
        self.assertTrue(r['final_log_errors'])

    def test_wrong_marker(self):
        self.assertFalse(self.session('wrong-marker')['passed'])

    def test_completion_before_marker(self):
        self.assertFalse(self.session('completion-first')['passed'])

    def test_unfinished_work_not_resumed(self):
        r = self.session('unfinished', count=2, cap=0.2)
        self.assertFalse(r['passed'])
        self.assertEqual(len(r['stages']), 1)
        self.assertEqual(r['stages'][0]['marker_count'], 1)
        self.assertEqual(r['stages'][0]['completion_count'], 0)
        self.assertTrue(r['stages'][0]['timed_out'])

    def test_log_byte_limit(self):
        r = self.session('log-flood', limit=4096)
        self.assertFalse(r['passed'])
        self.assertTrue(any('limit' in e for e in r['stream_errors']))
        path = Path(RESULTS[-1]['path']).with_name('hol.log')
        self.assertLessEqual(path.stat().st_size, 4096)

    def test_child_survives_exited_parent(self):
        r = self.session('surviving-child', expect_cleanup_failure=True)
        self.assertEqual(r['exit'], 0)
        self.assertFalse(r['passed'], r)
        self.assertIn('SYNTHETIC_CHILD ', Path(RESULTS[-1]['path']).with_name('hol.log').read_text())

    def test_nonzero_after_markers(self):
        r = self.session('nonzero')
        self.assertFalse(r['passed'])
        self.assertEqual(r['exit'], 7)

    def test_operational_exception_after_markers(self):
        original = runner.Transcript.poll
        injected = False
        def poll(obj, timeout=0):
            nonlocal injected
            if obj.done[0] and not injected:
                injected = True
                raise OSError('synthetic drain fault after markers')
            return original(obj, timeout)
        with mock.patch.object(runner.Transcript, 'poll', poll):
            r = self.session('clean')
        self.assertTrue(injected)
        self.assertFalse(r['passed'])
        self.assertTrue(r['operational_errors'])


class CleanupTests(unittest.TestCase):
    def process(self, returncode=0):
        process = mock.Mock(pid=123456, returncode=returncode)
        process.poll.return_value = returncode
        process.wait.return_value = returncode
        return process

    def test_reaped_absent_group_is_only_probed(self):
        probes = 0
        def signal_group(pgid, sig):
            nonlocal probes
            self.assertEqual(pgid, 123456)
            self.assertEqual(sig, 0, 'reaped leaders must never be signalled')
            probes += 1
            raise ProcessLookupError('synthetic confirmed absence')
        with mock.patch.object(runner.os, 'killpg', signal_group):
            report = runner.cleanup_group(self.process())
        self.assertTrue(report['parent_reaped'] and report['group_absent'])
        self.assertEqual(report['cleanup_errors'], [])
        self.assertEqual(report['cleanup_observations'], [])
        self.assertEqual(probes, 1)

    def test_persistent_permission_is_not_absence(self):
        with mock.patch.object(runner.os, 'killpg', side_effect=PermissionError('synthetic denial')):
            report = runner.cleanup_group(self.process(), cap=0.01)
        self.assertFalse(report['group_absent'])
        self.assertTrue(report['cleanup_errors'])
        self.assertTrue(any('final group probe' in e for e in report['cleanup_errors']))

    def test_absent_group_does_not_substitute_for_reaping(self):
        process = self.process(returncode=None)
        process.wait.side_effect = subprocess.TimeoutExpired('synthetic child', 0.01)
        with mock.patch.object(runner.os, 'killpg', side_effect=ProcessLookupError()):
            report = runner.cleanup_group(process, cap=0.01)
        self.assertTrue(report['group_absent'])
        self.assertFalse(report['parent_reaped'])
        self.assertTrue(report['cleanup_errors'])

    def test_reaped_parent_does_not_substitute_for_group_absence(self):
        with mock.patch.object(runner.os, 'killpg', return_value=None):
            report = runner.cleanup_group(self.process(), cap=0.001)
        self.assertTrue(report['parent_reaped'])
        self.assertFalse(report['group_absent'])
        self.assertTrue(report['cleanup_errors'])

    def test_final_permission_denial_is_failure(self):
        process = self.process()
        process.wait.side_effect = lambda **_: None
        def signal_group(pgid, sig):
            self.assertEqual(sig, 0)
            raise PermissionError('synthetic final probe denied')
        with mock.patch.object(runner.os, 'killpg', signal_group):
            report = runner.cleanup_group(process)
        self.assertFalse(report['group_absent'])
        self.assertTrue(any('final group probe' in item for item in report['cleanup_errors']))

    def test_reused_group_is_not_signalled(self):
        calls = []
        def signal_group(pgid, sig):
            calls.append((pgid, sig))
            self.assertEqual(sig, 0)
        with mock.patch.object(runner.os, 'killpg', signal_group):
            report = runner.cleanup_group(self.process())
        self.assertEqual(calls, [(123456, 0)])
        self.assertTrue(report['cleanup_errors'])

    def test_exit_after_term_does_not_trigger_kill(self):
        process = self.process(returncode=None)
        count = 0
        def poll():
            nonlocal count
            count += 1
            if count > 1:
                process.returncode = -15
            return process.returncode
        process.poll.side_effect = poll
        signals = []
        def signal_group(pgid, sig):
            signals.append(sig)
            if sig == 0:
                raise ProcessLookupError()
        with mock.patch.object(runner.os, 'killpg', signal_group):
            report = runner.cleanup_group(process)
        self.assertEqual(signals, [runner.signal.SIGTERM, 0])
        self.assertTrue(report['parent_reaped'] and report['group_absent'])

    def test_unreaped_child_can_be_killed_and_bounded_waited(self):
        process = self.process(returncode=None)
        signals = []
        def signal_group(pgid, sig):
            signals.append(sig)
            if sig == 0 and process.returncode is not None:
                raise ProcessLookupError()
        def wait(timeout):
            self.assertGreater(timeout, 0)
            self.assertLessEqual(timeout, 0.02)
            process.returncode = -9
            return -9
        process.wait.side_effect = wait
        with mock.patch.object(runner.os, 'killpg', signal_group):
            report = runner.cleanup_group(process, cap=0.001)
        self.assertIn(runner.signal.SIGTERM, signals)
        self.assertIn(runner.signal.SIGKILL, signals)
        self.assertEqual(report['cleanup_errors'], [])

    def test_failed_ownership_poll_never_signals(self):
        process = self.process(returncode=None)
        process.poll.side_effect = PermissionError('poll denied')
        process.wait.side_effect = subprocess.TimeoutExpired('fake', 0.01)
        signals = []
        def signal_group(pgid, sig):
            signals.append(sig)
            raise ProcessLookupError()
        with mock.patch.object(runner.os, 'killpg', signal_group):
            report = runner.cleanup_group(process, cap=0.001)
        self.assertEqual(signals, [0])
        self.assertTrue(report['cleanup_errors'])

    def test_transient_signal_denial_requires_reaped_child_and_absence(self):
        process = self.process(returncode=None)
        killed = False
        def poll():
            if killed:
                process.returncode = -9
            return process.returncode
        process.poll.side_effect = poll
        def signal_group(pgid, sig):
            nonlocal killed
            if sig == runner.signal.SIGTERM:
                raise PermissionError('transient signal denial')
            if sig == runner.signal.SIGKILL:
                killed = True
            elif sig == 0 and process.returncode is not None:
                raise ProcessLookupError()
        with mock.patch.object(runner.os, 'killpg', signal_group):
            report = runner.cleanup_group(process, cap=0.3)
        self.assertTrue(report['parent_reaped'] and report['group_absent'])
        self.assertEqual(report['cleanup_errors'], [])
        self.assertTrue(any('transient signal denial' in e for e in report['cleanup_observations']))

    def test_own_group_is_never_signalled(self):
        process = self.process()
        process.pid = os.getpgrp()
        with mock.patch.object(runner.os, 'killpg') as signal_group:
            with self.assertRaises(runner.RunnerFailure):
                runner.cleanup_group(process)
            signal_group.assert_not_called()


class FinalizationTests(unittest.TestCase):
    def attempt(self, *, stdin_error=None, cleanup_error=None, transcript_error=None):
        directory = EVIDENCE / self._testMethodName
        directory.mkdir()
        process = mock.Mock(pid=123456, returncode=0)
        process.stdin.closed = False
        process.stdin.close.side_effect = stdin_error
        process.poll.return_value = 0
        transcript = mock.Mock(errors=[], eof=True, counts=[1], done=[1])
        transcript.close.side_effect = transcript_error
        cleanup = dict(parent_reaped=True, group_absent=True, cleanup_errors=[], exit=0)
        stages = [dict(stage='fake', kind='synthetic', command='FAKE', marker='FAKE')]
        with mock.patch.object(runner.subprocess, 'Popen', return_value=process), \
             mock.patch.object(runner.os, 'set_blocking'), \
             mock.patch.object(runner.os, 'write', side_effect=lambda fd, data: len(data)), \
             mock.patch.object(runner, 'Transcript', return_value=transcript), \
             mock.patch.object(runner, 'cleanup_group', return_value=cleanup,
                               side_effect=cleanup_error) as cleanup_call, \
             mock.patch.object(runner, 'final_log_check', return_value=[]), \
             contextlib.redirect_stdout(io.StringIO()):
            report = runner.run_session(['never-launched'], ROOT, directory, stages, 1)
        cleanup_call.assert_called_once_with(process, 5.0)
        transcript.close.assert_called_once_with()
        self.assertIn('log_sha256', report)
        self.assertIn('final_log_errors', report)
        self.assertFalse(report['passed'])
        self.assertTrue(report['stages'][0]['passed'])
        return report

    def test_stdin_close_failure_cannot_skip_owned_cleanup(self):
        report = self.attempt(stdin_error=BrokenPipeError('injected stdin failure'))
        self.assertTrue(report['parent_reaped'] and report['group_absent'])
        self.assertEqual(len(report['operational_errors']), 2)
        self.assertTrue(all('injected stdin failure' in e for e in report['operational_errors']))

    def test_primary_and_cleanup_failure_both_survive_finalization(self):
        report = self.attempt(stdin_error=OSError('primary close failure'),
                              cleanup_error=OSError('secondary cleanup failure'))
        self.assertTrue(any('primary close failure' in e for e in report['operational_errors']))
        self.assertTrue(any('secondary cleanup failure' in e for e in report['cleanup_errors']))
        self.assertFalse(report['group_absent'])

    def test_transcript_close_failure_retains_finished_cleanup(self):
        report = self.attempt(transcript_error=OSError('transcript close failure'))
        self.assertTrue(report['parent_reaped'] and report['group_absent'])
        self.assertTrue(any('transcript close failure' in e for e in report['operational_errors']))


class SourceTests(unittest.TestCase):
    def setUp(self):
        self.directory = EVIDENCE / self._testMethodName
        self.root, self.snapshot = self.directory / 'root', self.directory / 'snapshot'
        files = ['hol/reflection.ml', 'tests/hol_reflection/library_smoke.ml',
                 'tests/hol_reflection/SOURCE_PINS.json', 'scripts/test-hol-reflection.py',
                 'scripts/toolchain-exec.sh', 'scripts/toolchain-env.sh']
        for rel in files:
            p = self.root / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text('synthetic source ' + rel)
        (self.root / 'toolchain').mkdir()
        self.before = runner.inventory(self.root)

    def test_verified_readonly_copy(self):
        t = runner.freeze_sources(self.root, self.snapshot, self.before)
        self.assertEqual(runner.inventory(self.snapshot), self.before)
        self.assertTrue((self.snapshot / 'toolchain').is_symlink())
        self.assertEqual(t['target'], str((self.root / 'toolchain').resolve()))
        self.assertEqual((self.snapshot / 'hol/reflection.ml').stat().st_mode & 0o222, 0)
        self.assertEqual(self.snapshot.stat().st_mode & 0o222, 0)

    def test_changed_source_not_copied(self):
        (self.root / 'hol/reflection.ml').write_text('changed')
        with self.assertRaises(runner.RunnerFailure):
            runner.freeze_sources(self.root, self.snapshot, self.before)

    def test_corrupt_copy_not_accepted(self):
        original = runner.sha
        def digest(path):
            return 'bad' if self.snapshot in path.parents else original(path)
        with mock.patch.object(runner, 'sha', digest), self.assertRaises(runner.RunnerFailure):
            runner.freeze_sources(self.root, self.snapshot, self.before)

    def test_source_symlink_not_accepted(self):
        p = self.root / 'hol/reflection.ml'
        data = p.read_text()
        p.unlink()
        outside = self.directory / 'outside.ml'
        outside.write_text(data)
        p.symlink_to(outside)
        with self.assertRaises(runner.RunnerFailure):
            runner.freeze_sources(self.root, self.snapshot, self.before)


if __name__ == '__main__':
    suite = unittest.defaultTestLoader.loadTestsFromModule(sys.modules[__name__])
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    summary = dict(scope=__doc__, tests=result.testsRun, passed=result.wasSuccessful(),
                   failures=len(result.failures), errors=len(result.errors), process_reports=RESULTS,
                   runner_sha256=runner.sha(ROOT / 'scripts/test-hol-reflection.py'),
                   backend_sha256=runner.sha(BACKEND))
    (EVIDENCE / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(EVIDENCE, flush=True)
    raise SystemExit(0 if result.wasSuccessful() else 1)
