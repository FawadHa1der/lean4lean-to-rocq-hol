"""Fake-only error-route controls for the private synthetic-suite helper."""
import importlib.util
from pathlib import Path
import subprocess
import sys
import unittest
from unittest import mock

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location(
    'hol_runner_provenance_tests', ROOT / 'tests/hol_runner/test_provenance.py')
subject = importlib.util.module_from_spec(spec)
spec.loader.exec_module(subject)


class Pipe:
    def __init__(self, owner, name, error=None, closed=False):
        self.owner, self.name, self.error, self.closed = owner, name, error, closed

    def close(self):
        self.owner.events.append(('close', self.name))
        if self.error:
            raise self.error
        self.closed = True


class Process:
    def __init__(self, reaped=False):
        self.returncode = 0 if reaped else None
        self.events = []
        self.stdout = Pipe(self, 'stdout')
        self.stderr = Pipe(self, 'stderr')
        self.term_error = self.kill_error = self.wait_error = None
        self.communications = []
        self.reap_on_error = False
        self.forbidden = []

    def destructive(self, name, error):
        self.events.append((name,))
        if self.returncode is not None:
            self.forbidden.append(name)
            raise AssertionError('destructive operation after reaping')
        if error:
            raise error

    def terminate(self):
        self.destructive('terminate', self.term_error)

    def kill(self):
        self.destructive('kill', self.kill_error)

    def communicate(self, timeout=None):
        self.events.append(('communicate', timeout))
        if timeout not in (8, 10):
            self.forbidden.append(('communicate', timeout))
            raise AssertionError('unbounded or changed communication cap')
        result = self.communications.pop(0) if self.communications else (b'out', b'err')
        if isinstance(result, BaseException):
            if self.reap_on_error:
                self.returncode = 0
            raise result
        if self.returncode is None:
            self.returncode = 0
        return result

    def wait(self, timeout=None):
        self.events.append(('wait', timeout))
        if timeout != 3:
            self.forbidden.append(('wait', timeout))
            raise AssertionError('unbounded or changed final reap cap')
        if self.wait_error:
            raise self.wait_error
        self.returncode = -9
        return self.returncode


class CleanupTests(unittest.TestCase):
    def process(self, **kwargs):
        process = Process(**kwargs)
        self.addCleanup(lambda: self.assertEqual(process.forbidden, []))
        return process

    def test_reaped_child_never_signalled_or_waited(self):
        p = self.process(reaped=True)
        subject.finish_synthetic_supervisor(p, None)
        self.assertEqual(p.events, [('close', 'stdout'), ('close', 'stderr')])

    def test_closed_or_missing_read_pipes_are_skipped(self):
        p = self.process(reaped=True)
        p.stdout.closed = True
        p.stderr = None
        subject.finish_synthetic_supervisor(p, None)
        self.assertEqual(p.events, [])

    def test_graceful_direct_child_cleanup_does_not_escalate(self):
        p = self.process()
        subject.finish_synthetic_supervisor(p, None)
        self.assertEqual(p.events, [('terminate',), ('communicate', 8),
                                    ('close', 'stdout'), ('close', 'stderr')])

    def test_timeout_escalates_before_exact_bounded_wait_and_remains_failure(self):
        p = self.process()
        timeout = subprocess.TimeoutExpired('fake', 8)
        p.communications = [timeout]
        with self.assertRaises(subject.SyntheticCleanupError) as caught:
            subject.finish_synthetic_supervisor(p, None)
        self.assertEqual(caught.exception.errors, (timeout,))
        self.assertIs(caught.exception.__cause__, timeout)
        self.assertEqual(p.events[:4], [('terminate',), ('communicate', 8), ('kill',), ('wait', 3)])

    def test_communication_error_after_reap_cannot_trigger_kill(self):
        p = self.process()
        error = OSError('pipe error after root reaped')
        p.communications = [error]
        p.reap_on_error = True
        with self.assertRaises(subject.SyntheticCleanupError) as caught:
            subject.finish_synthetic_supervisor(p, None)
        self.assertEqual(caught.exception.errors, (error,))
        self.assertNotIn(('kill',), p.events)
        self.assertNotIn(('wait', 3), p.events)

    def test_terminate_failure_does_not_skip_bounded_communication(self):
        p = self.process()
        p.term_error = PermissionError('TERM')
        with self.assertRaises(subject.SyntheticCleanupError) as caught:
            subject.finish_synthetic_supervisor(p, None)
        self.assertEqual(caught.exception.errors, (p.term_error,))
        self.assertIn(('communicate', 8), p.events)
        self.assertIsNotNone(p.returncode)

    def test_kill_failure_does_not_skip_bounded_reap(self):
        p = self.process()
        timeout = subprocess.TimeoutExpired('fake', 8)
        p.communications = [timeout]
        p.kill_error = PermissionError('KILL')
        with self.assertRaises(subject.SyntheticCleanupError) as caught:
            subject.finish_synthetic_supervisor(p, None)
        self.assertEqual(caught.exception.errors, (timeout, p.kill_error))
        self.assertIn(('wait', 3), p.events)

    def test_primary_and_all_cleanup_faults_are_retained_without_retry(self):
        p = self.process()
        primary = ValueError('original assertion')
        p.term_error = PermissionError('TERM')
        timeout = subprocess.TimeoutExpired('fake', 8)
        p.communications = [timeout]
        p.kill_error = PermissionError('KILL')
        p.wait_error = subprocess.TimeoutExpired('fake', 3)
        p.stdout.error = OSError('stdout')
        p.stderr.error = OSError('stderr')
        with self.assertRaises(subject.SyntheticCleanupError) as caught:
            subject.finish_synthetic_supervisor(p, primary)
        error = caught.exception
        self.assertIs(error.primary, primary)
        self.assertIs(error.__cause__, primary)
        self.assertEqual(error.errors[:4], (p.term_error, timeout, p.kill_error, p.wait_error))
        self.assertIn('not reaped', str(error.errors[4]))
        self.assertEqual(error.errors[5:], (p.stdout.error, p.stderr.error))
        self.assertEqual(p.events.count(('kill',)), 1)
        self.assertEqual(p.events.count(('wait', 3)), 1)

    def test_stdout_close_fault_does_not_skip_stderr_close(self):
        p = self.process(reaped=True)
        p.stdout.error = OSError('stdout')
        with self.assertRaises(subject.SyntheticCleanupError) as caught:
            subject.finish_synthetic_supervisor(p, None)
        self.assertEqual(caught.exception.errors, (p.stdout.error,))
        self.assertTrue(p.stderr.closed)

    def test_keyboard_interrupt_is_preserved_while_reaping(self):
        p = self.process()
        interrupt = KeyboardInterrupt('cleanup interrupted')
        p.communications = [interrupt]
        with self.assertRaises(subject.SyntheticCleanupError) as caught:
            subject.finish_synthetic_supervisor(p, None)
        self.assertEqual(caught.exception.errors, (interrupt,))
        self.assertIsNotNone(p.returncode)

    def test_wrapper_success_preserves_all_four_codes_and_bytes(self):
        for code in range(4):
            with self.subTest(code=code):
                p = self.process(reaped=True)
                p.returncode = code
                p.communications = [(b'output\x00', b'diagnostic\xff')]
                with mock.patch.object(subject.subprocess, 'Popen', return_value=p) as spawn:
                    result = subject.run_synthetic_supervisor(['fake'], {'KEY': 'value'})
                self.assertEqual((result.args, result.returncode, result.stdout, result.stderr),
                                 (['fake'], code, b'output\x00', b'diagnostic\xff'))
                self.assertEqual(spawn.call_args.kwargs,
                                 dict(env={'KEY': 'value'}, stdout=subprocess.PIPE, stderr=subprocess.PIPE))
                self.assertNotIn(('kill',), p.events)

    def test_wrapper_preserves_original_when_cleanup_succeeds(self):
        p = self.process()
        primary = subprocess.TimeoutExpired('fake', 10)
        p.communications = [primary, (b'', b'')]
        with mock.patch.object(subject.subprocess, 'Popen', return_value=p):
            with self.assertRaises(subprocess.TimeoutExpired) as caught:
                subject.run_synthetic_supervisor(['fake'], {})
        self.assertIs(caught.exception, primary)
        self.assertEqual(p.events[:3], [('communicate', 10), ('terminate',), ('communicate', 8)])

    def test_wrapper_retains_original_and_cleanup_timeout(self):
        p = self.process()
        primary = subprocess.TimeoutExpired('fake', 10)
        cleanup = subprocess.TimeoutExpired('fake', 8)
        p.communications = [primary, cleanup]
        with mock.patch.object(subject.subprocess, 'Popen', return_value=p):
            with self.assertRaises(subject.SyntheticCleanupError) as caught:
                subject.run_synthetic_supervisor(['fake'], {})
        self.assertIs(caught.exception.primary, primary)
        self.assertIs(caught.exception.__cause__, primary)
        self.assertEqual(caught.exception.errors, (cleanup,))

    def test_spawn_failure_has_no_cleanup_of_nonexistent_child(self):
        error = OSError('spawn failed')
        with mock.patch.object(subject.subprocess, 'Popen', side_effect=error), \
                mock.patch.object(subject, 'finish_synthetic_supervisor') as finish:
            with self.assertRaises(OSError) as caught:
                subject.run_synthetic_supervisor(['fake'], {})
        self.assertIs(caught.exception, error)
        finish.assert_not_called()


if __name__ == '__main__':
    unittest.main()
