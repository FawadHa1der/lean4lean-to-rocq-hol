"""Deterministic cleanup controls: no real process creation, signals, or probes."""
import contextlib
import io
import json
from pathlib import Path
import signal
import subprocess
import tempfile
import unittest
from unittest import mock

import run


class Child:
    def __init__(self, returncode=None):
        self.pid = 32123
        self.returncode = returncode
        self.stdin = io.BytesIO()
        self.events = []
        self.poll_error = self.kill_error = self.wait_error = None
        self.communication_error = None

    def poll(self):
        self.events.append(('poll', self.returncode))
        if self.poll_error:
            raise self.poll_error
        return self.returncode

    def kill(self):
        self.events.append(('direct_kill', self.returncode))
        if self.kill_error:
            raise self.kill_error

    def wait(self, timeout=None):
        self.events.append(('wait', timeout))
        if self.wait_error:
            raise self.wait_error
        self.returncode = -signal.SIGKILL
        return self.returncode

    def communicate(self, data=None, timeout=None):
        self.events.append(('communicate', timeout))
        if timeout is None:
            raise AssertionError('Unbounded communicate forbidden')
        if self.communication_error:
            raise self.communication_error
        self.returncode = 0
        return b'', None


class OwnedProcessHarness(unittest.TestCase):
    def setUp(self):
        self.child = Child()
        self.signals = []
        self.group_error = None
        self.probe_error = None
        self.pid_present = self.group_present = False
        self.stack = contextlib.ExitStack()
        self.addCleanup(self.stack.close)
        self.stack.enter_context(mock.patch.object(run.os, 'killpg', side_effect=self.killpg))
        self.stack.enter_context(mock.patch.object(run.os, 'kill', side_effect=self.kill))
        self.spawn = self.stack.enter_context(mock.patch.object(run.subprocess, 'Popen',
                        side_effect=AssertionError('No actual process launch')))

    def probe(self, kind):
        if self.probe_error:
            raise self.probe_error
        if getattr(self, kind + '_present'):
            return
        raise ProcessLookupError('absent')

    def killpg(self, pid, sig):
        self.assertEqual(pid, self.child.pid)
        self.signals.append(('group', sig))
        self.child.events.append(('group_signal', sig))
        if sig == 0:
            return self.probe('group')
        self.assertEqual(sig, signal.SIGKILL)
        self.assertIsNone(self.child.returncode, 'Group signal after reap')
        self.assertIn(('poll', None), self.child.events)
        if self.group_error:
            raise self.group_error

    def kill(self, pid, sig):
        self.assertEqual(pid, self.child.pid)
        self.assertEqual(sig, 0, 'Raw direct destructive signal forbidden')
        self.signals.append(('pid', sig))
        return self.probe('pid')

    def cleanup(self, **kwargs):
        return run.cleanup_owned_process(self.child, **kwargs)

    def assert_read_only(self):
        self.assertTrue(all(sig == 0 for _, sig in self.signals))
        self.assertFalse(any(e[0] == 'direct_kill' for e in self.child.events))


class CleanupTests(OwnedProcessHarness):
    def test_completed_success_never_signals(self):
        self.child.returncode = 0
        self.assertTrue(self.cleanup()['verified'])
        self.assert_read_only()

    def test_completed_nonzero_never_signals(self):
        self.child.returncode = 2
        self.assertTrue(self.cleanup()['verified'])
        self.assert_read_only()

    def test_recycled_pid_and_group_are_only_observed(self):
        self.child.returncode = 0
        self.pid_present = self.group_present = True
        result = self.cleanup()
        self.assertFalse(result['verified'])
        self.assertFalse(result['pid_absent'])
        self.assertFalse(result['process_group_absent'])
        self.assert_read_only()

    def test_recycled_pid_alone_fails_closed(self):
        self.child.returncode = 0
        self.pid_present = True
        self.assertFalse(self.cleanup()['verified'])
        self.assert_read_only()

    def test_remnant_group_is_not_signalled_after_root_reap(self):
        self.child.returncode = 0
        self.group_present = True
        self.assertFalse(self.cleanup()['verified'])
        self.assert_read_only()

    def test_unreaped_owned_group_is_killed_then_reaped(self):
        result = self.cleanup()
        self.assertTrue(result['verified'])
        self.assertEqual(self.child.events[:3], [('poll', None),
                         ('group_signal', signal.SIGKILL), ('wait', 10)])
        self.assertEqual(result['actions'], ['owned_unreaped_group_kill'])

    def test_signal_lookup_race_uses_direct_handle(self):
        self.group_error = ProcessLookupError('group gone')
        result = self.cleanup()
        self.assertTrue(result['verified'])
        self.assertIn(('direct_kill', None), self.child.events)

    def test_group_permission_failure_retained_with_direct_fallback(self):
        self.group_error = PermissionError('group permission denied')
        result = self.cleanup()
        self.assertFalse(result['verified'])
        self.assertTrue(result['reaped'])
        self.assertIn('group permission denied', repr(result['errors']))
        self.assertIn(('direct_kill', None), self.child.events)

    def test_direct_kill_error_does_not_skip_reap(self):
        self.child.kill_error = PermissionError('direct permission denied')
        result = self.cleanup(allow_group=False)
        self.assertFalse(result['verified'])
        self.assertTrue(result['reaped'])
        self.assertIn(('wait', 10), self.child.events)

    def test_all_errors_retained(self):
        self.group_error = PermissionError('group denied')
        self.child.kill_error = PermissionError('direct denied')
        self.child.wait_error = OSError('reap denied')
        result = self.cleanup()
        self.assertFalse(result['verified'])
        self.assertFalse(result['reaped'])
        for error in ('group denied', 'direct denied', 'reap denied'):
            self.assertIn(error, repr(result['errors']))

    def test_reap_timeout_is_bounded_and_fails_closed(self):
        self.child.wait_error = subprocess.TimeoutExpired('fake', 10)
        result = self.cleanup()
        self.assertFalse(result['verified'])
        self.assertFalse(result['reaped'])
        self.assertEqual([e for e in self.child.events if e[0] == 'wait'], [('wait', 10)])
        self.assertIn('TimeoutExpired', repr(result['errors']))

    def test_poll_failure_never_authorizes_group_signal(self):
        self.child.poll_error = OSError('poll failed')
        result = self.cleanup()
        self.assertFalse(result['verified'])
        self.assertTrue(all(sig == 0 for _, sig in self.signals))
        self.assertIn(('direct_kill', None), self.child.events)

    def test_probe_permission_is_unknown_not_absence(self):
        self.child.returncode = 0
        self.probe_error = PermissionError('cannot observe')
        result = self.cleanup()
        self.assertFalse(result['verified'])
        self.assertIsNone(result['pid_absent'])
        self.assertIsNone(result['process_group_absent'])
        self.assertEqual(len(result['errors']), 2)
        self.assert_read_only()

    def test_second_cleanup_of_reaped_leader_cannot_signal_recycled_group(self):
        self.assertTrue(self.cleanup()['verified'])
        self.signals.clear()
        self.child.events.clear()
        self.pid_present = self.group_present = True
        self.assertFalse(self.cleanup()['verified'])
        self.assert_read_only()

    def test_outer_live_handle_uses_direct_kill_only(self):
        result = self.cleanup(allow_group=False)
        self.assertTrue(result['verified'])
        self.assertTrue(all(sig == 0 for _, sig in self.signals))
        self.assertIn(('direct_kill', None), self.child.events)

    def test_outer_completed_handle_is_read_only(self):
        self.child.returncode = 0
        self.assertTrue(self.cleanup(allow_group=False)['verified'])
        self.assert_read_only()


class RunJobTests(OwnedProcessHarness):
    def setUp(self):
        super().setUp()
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.snapshot = self.root / 'snapshot'
        self.snapshot.mkdir()
        self.report = self.root / 'report'
        self.report.mkdir()
        self.job = {'source': '', 'markers': ['TEST_PASS 1'], 'limit': 180, 'options': {}}
        self.spawn.side_effect = self.launch
        self.stack.enter_context(contextlib.redirect_stdout(io.StringIO()))

    def launch(self, argv, **kwargs):
        self.assertEqual(argv, ['sh', 'scripts/private-hol.sh'])
        self.assertTrue(kwargs['start_new_session'])
        kwargs['stdout'].write(b'TEST_PASS 1\n')
        kwargs['stdout'].flush()
        return self.child

    def attempt(self, **kwargs):
        return run._run_job(self.snapshot, self.report, 'fake', self.job, **kwargs)

    def test_success_no_signal_after_communicate(self):
        result = self.attempt()
        self.assertTrue(result['passed'])
        self.assert_read_only()
        self.assertEqual([e for e in self.child.events if e[0] == 'communicate'], [('communicate', 180)])

    def test_success_recycled_group_is_failure_without_signal(self):
        self.pid_present = self.group_present = True
        self.assertFalse(self.attempt()['passed'])
        self.assert_read_only()

    def test_timeout_kills_unreaped_owned_group_and_never_passes(self):
        self.child.communication_error = subprocess.TimeoutExpired('fake', 180)
        result = self.attempt()
        self.assertTrue(result['timed_out'])
        self.assertTrue(result['cleanup']['verified'])
        self.assertFalse(result['passed'])
        self.assertIn(('group', signal.SIGKILL), self.signals)
        self.assertEqual([e for e in self.child.events if e[0] == 'communicate'], [('communicate', 180)])

    def test_timeout_reap_failure_preserved(self):
        self.child.communication_error = subprocess.TimeoutExpired('fake', 180)
        self.child.wait_error = OSError('failed wait')
        result = self.attempt()
        self.assertTrue(result['timed_out'])
        self.assertFalse(result['reaped'])
        self.assertFalse(result['passed'])
        self.assertIn('failed wait', repr(result['cleanup']['errors']))

    def test_primary_error_rethrown_and_cleanup_errors_durable(self):
        error = BrokenPipeError('first execution error')
        self.child.communication_error = error
        self.group_error = PermissionError('second cleanup error')
        with self.assertRaises(BrokenPipeError) as raised:
            self.attempt()
        self.assertIs(raised.exception, error)
        record = json.loads((self.report / 'fake.execution-error.json').read_text())
        self.assertIn('first execution error', record['primary_error'])
        self.assertIn('second cleanup error', repr(record['cleanup']['errors']))
        self.assertFalse(record['passed'])
        self.assertIn('second cleanup error', str(error.__notes__))

    def test_publish_false_still_retains_primary_cleanup_record(self):
        self.child.communication_error = OSError('execution error')
        with self.assertRaises(OSError):
            self.attempt(publish=False)
        self.assertTrue((self.report / 'fake.execution-error.json').is_file())

    def test_interrupt_still_cleans_owned_unreaped_root(self):
        error = KeyboardInterrupt('interrupted')
        self.child.communication_error = error
        with self.assertRaises(KeyboardInterrupt) as raised:
            self.attempt()
        self.assertIs(raised.exception, error)
        self.assertIn(('group', signal.SIGKILL), self.signals)
        self.assertIn(('wait', 10), self.child.events)

    def test_post_reap_error_does_not_signal(self):
        self.child.returncode = 0
        self.child.communication_error = OSError('post reap failure')
        with self.assertRaises(OSError):
            self.attempt()
        self.assert_read_only()


if __name__ == '__main__':
    unittest.main()
