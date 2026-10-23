"""Deterministic fake-process tests. No real child, signal, socket, or sleep."""
from contextlib import ExitStack, contextmanager, nullcontext
import importlib.util
from pathlib import Path
import signal
import subprocess
import sys
from types import SimpleNamespace
import unittest
from unittest import mock

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('hol_runner_teardown', ROOT/'scripts/hol-check.py')
subject = importlib.util.module_from_spec(spec)
spec.loader.exec_module(subject)


class InputPipe:
    def __init__(self, events, closed=True):
        self.events = events
        self.closed = closed
        self.blocking = True
        self.fileno_error = None
        self.blocking_error = None
        self.write_error = None
        self.close_errors = []

    def fileno(self):
        self.events.append(('stdin_fileno',))
        if self.fileno_error:
            raise self.fileno_error
        return 654

    def set_blocking(self, fd, blocking):
        self.events.append(('stdin_set_blocking', fd, blocking))
        if fd != 654 or blocking is not False:
            raise AssertionError('only the fake stdin can be made nonblocking')
        if self.blocking_error:
            raise self.blocking_error
        self.blocking = blocking

    def write(self, data):
        self.events.append(('stdin_write', data))
        if self.write_error:
            raise self.write_error
        return len(data)

    def close(self):
        self.events.append(('stdin_close', self.blocking))
        if self.close_errors:
            error = self.close_errors.pop(0)
            if error is not None:
                raise error
        self.closed = True


class World:
    def __init__(self, reaped=False, residual=False):
        self.now = 0.
        self.events = []
        self.forbidden = []
        self.residual = residual
        self.reused_pid = False
        self.group_present = not reaped or residual
        self.disposition = signal.SIG_DFL
        self.pgid = 321
        self.signal_errors = {}
        self.probe_error = None
        self.identity_error = None
        self.wait_error = None
        self.wait_outcomes = []
        self.after_wait = None
        self.after_wait_error = None
        self.sleep_error = None
        self.clock_error = None
        self.after_term = None
        self.after_sleep = None
        self.close_error = None
        self.process = SimpleNamespace(pid=321, returncode=0 if reaped else None,
            wait=self.wait, poll=self.poll, stdout=SimpleNamespace(close=self.close),
            stdin=InputPipe(self.events))

    def kill(self, pid, sig):
        self.events.append(('pid_probe',pid,sig))
        if pid!=321 or sig!=0:
            self.forbidden.append(('naked_pid',pid,sig))
            raise AssertionError('only nondestructive owned-root PID probes are allowed')
        if not self.reused_pid and self.process.returncode is not None:
            raise ProcessLookupError('root PID gone')

    def killpg(self, pid, sig):
        self.events.append(('signal', pid, sig, self.process.returncode))
        if pid != 321:
            self.forbidden.append(('wrong_group', pid))
            raise AssertionError('wrong group')
        if sig:
            if self.process.returncode is not None or self.disposition != signal.SIG_DFL:
                self.forbidden.append(('lost_reservation', pid, sig))
                raise AssertionError('destructive signal after reservation lost')
            if sig in self.signal_errors:
                raise self.signal_errors[sig]
            if not self.group_present:
                raise ProcessLookupError('group gone')
            if sig == signal.SIGTERM and self.after_term:
                self.after_term()
        else:
            if self.probe_error:
                raise self.probe_error
            if not self.group_present:
                raise ProcessLookupError('group gone')

    def getpgid(self, pid):
        self.events.append(('identity', pid))
        if self.identity_error:
            raise self.identity_error
        return self.pgid

    def wait(self, timeout=None):
        self.events.append(('wait', timeout))
        if timeout is None or not 0 < timeout <= 3:
            self.forbidden.append(('unbounded_wait', timeout))
            raise AssertionError('wait must be explicitly bounded')
        outcome = self.wait_outcomes.pop(0) if self.wait_outcomes else (self.wait_error or 0)
        if isinstance(outcome, BaseException):
            if self.after_wait_error:
                self.after_wait_error()
            raise outcome
        self.process.returncode = outcome
        self.group_present = self.residual
        if self.after_wait:
            self.after_wait()
        return outcome

    def poll(self):
        self.forbidden.append(('poll',))
        raise AssertionError('cleanup must use bounded waits, not poll')

    def clock(self):
        if self.clock_error:
            raise self.clock_error
        return self.now

    def sleep(self, seconds):
        self.events.append(('sleep', seconds))
        if self.sleep_error:
            raise self.sleep_error
        self.now += seconds
        if self.after_sleep:
            action,self.after_sleep = self.after_sleep,None
            action()

    def close(self):
        self.events.append(('close',))
        if self.close_error:
            raise self.close_error

    def signals(self):
        return [event for event in self.events if event[0]=='signal' and event[2]]


class TeardownTests(unittest.TestCase):
    @contextmanager
    def world(self, **kw):
        world = World(**kw)
        with ExitStack() as stack:
            for obj, name, replacement in [
                (subject.os,'kill',world.kill), (subject.os,'killpg',world.killpg),
                (subject.os,'getpgid',world.getpgid),
                (subject.os,'set_blocking',world.process.stdin.set_blocking),
                (subject.signal,'getsignal',lambda sig: world.disposition),
                (subject.time,'monotonic',world.clock), (subject.time,'sleep',world.sleep)]:
                stack.enter_context(mock.patch.object(obj,name,side_effect=replacement))
            try:
                yield world
            finally:
                self.assertEqual(world.forbidden, [])

    def test_owned_graceful_stop_signals_reserved_group_then_bounded_reap(self):
        with self.world() as w:
            report=subject.stop_process(w.process,98765)
            self.assertEqual([e[2] for e in w.signals()],[signal.SIGTERM])
            self.assertTrue(all(e[1]==321 and e[3] is None for e in w.signals()))
            wait=w.events.index(('wait',3))
            self.assertTrue(all(i<wait for i,e in enumerate(w.events) if e in w.signals()))
            self.assertEqual([e for e in w.events if e[0]=='wait'],[('wait',3)])
            self.assertEqual(w.now,0.)
            self.assertFalse(any(e[0]=='sleep' for e in w.events))
            self.assertTrue(report['reaped'] and report['process_group_absent'])
            self.assertTrue(report['verified']);self.assertEqual(report['errors'],[])
            self.assertEqual(report['ready_hol_pid'],98765)

    def test_before_ready_uses_same_group_not_unknown_pid(self):
        with self.world() as w:
            self.assertTrue(subject.stop_process(w.process,None)['process_group_absent'])
            self.assertEqual(len(w.signals()),1)

    def test_ready_pid_never_becomes_signal_authority(self):
        for ready in (None,0,1,-999,321,98765,10**30):
            with self.subTest(ready=ready), self.world() as w:
                subject.stop_process(w.process,ready)
                self.assertTrue(all(e[1]==321 for e in w.signals()))

    def test_already_reaped_and_absent_never_signals_or_waits(self):
        with self.world(reaped=True) as w:
            self.assertTrue(subject.stop_process(w.process,999)['process_group_absent'])
            self.assertEqual(w.signals(),[])
            self.assertFalse(any(e[0]=='wait' for e in w.events))

    def test_recycled_or_unknown_group_after_reap_fails_closed(self):
        with self.world(reaped=True,residual=True) as w:
            with self.assertRaises(subject.ProcessCleanupError) as caught:
                subject.stop_process(w.process,999)
            self.assertEqual(w.signals(),[])
            self.assertFalse(caught.exception.report['process_group_absent'])
            self.assertFalse(caught.exception.report['verified'])
            self.assertIn('no post-reap signal',str(caught.exception))

    def test_ready_child_may_be_recycled_but_is_never_touched(self):
        with self.world(reaped=True,residual=True) as w:
            with self.assertRaises(subject.ProcessCleanupError):
                subject.stop_process(w.process,98765)
            self.assertEqual(w.signals(),[])

    def test_recycled_root_pid_in_other_group_is_only_probed_and_faulted(self):
        with self.world(reaped=True) as w:
            w.reused_pid=True
            with self.assertRaises(subject.ProcessCleanupError) as caught:
                subject.stop_process(w.process,999)
            self.assertFalse(caught.exception.report['pid_absent'])
            self.assertTrue(caught.exception.report['process_group_absent'])
            self.assertFalse(caught.exception.report['verified'])
            self.assertEqual(w.signals(),[])

    def test_reservation_lost_during_grace_blocks_kill(self):
        with self.world(residual=True) as w:
            w.wait_outcomes=[subprocess.TimeoutExpired('fake HOL',3)]
            w.after_wait_error=lambda:setattr(w.process,'returncode',0)
            with self.assertRaises(subject.ProcessCleanupError):
                subject.stop_process(w.process,999)
            self.assertEqual([e[2] for e in w.signals()],[signal.SIGTERM])
            self.assertEqual([e for e in w.events if e[0]=='wait'],[('wait',3)])

    def test_exited_unreaped_root_gets_grace_wait_without_kill(self):
        with self.world() as w:
            # Zombie/exited is intentionally not reflected in cached returncode until wait.
            w.after_term=lambda:w.events.append(('root_exited_unreaped',))
            subject.stop_process(w.process,999)
            self.assertEqual(len(w.signals()),1)
            self.assertLess(w.events.index(('root_exited_unreaped',)),w.events.index(('wait',3)))

    def test_no_post_wait_kill_when_descendants_or_reused_group_remain(self):
        with self.world(residual=True) as w:
            with self.assertRaises(subject.ProcessCleanupError):
                subject.stop_process(w.process,999)
            at=w.events.index(('wait',3))
            self.assertFalse(any(e[0]=='signal' and e[2] for e in w.events[at+1:]))

    def test_disappeared_group_still_gets_bounded_root_wait(self):
        with self.world() as w:
            w.group_present=False
            self.assertTrue(subject.stop_process(w.process,None)['reaped'])
            self.assertIn(('wait',3),w.events)

    def test_ignored_sigchld_disables_destructive_signals(self):
        with self.world() as w:
            w.disposition=signal.SIG_IGN
            with self.assertRaises(subject.ProcessCleanupError) as caught:
                subject.stop_process(w.process,999)
            self.assertEqual(w.signals(),[])
            self.assertIn('SIGCHLD',str(caught.exception))

    def test_custom_sigchld_handler_disables_destructive_signals(self):
        with self.world() as w:
            w.disposition=lambda *args:None
            with self.assertRaises(subject.ProcessCleanupError):subject.stop_process(w.process,999)
            self.assertEqual(w.signals(),[])

    def test_unreaped_root_does_not_require_live_pid_lookup(self):
        with self.world() as w:
            w.identity_error=ProcessLookupError('exited but unreaped root')
            self.assertTrue(subject.stop_process(w.process,999)['reaped'])
            self.assertEqual(len(w.signals()),1)
            self.assertFalse(any(e[0]=='identity' for e in w.events))

    def test_ready_pid_membership_is_not_requeried_for_signal_authority(self):
        with self.world() as w:
            w.identity_error=PermissionError('a live membership probe is not ownership')
            self.assertTrue(subject.stop_process(w.process,98765)['reaped'])
            self.assertFalse(any(e[0]=='identity' for e in w.events))

    def test_two_wait_timeouts_have_no_unbounded_fallback_or_third_wait(self):
        with self.world() as w:
            error=subprocess.TimeoutExpired('fake HOL',3);w.wait_error=error
            with self.assertRaises(subject.ProcessCleanupError) as caught:subject.stop_process(w.process,999)
            self.assertIn(error,caught.exception.errors)
            self.assertFalse(caught.exception.report['reaped'])
            self.assertEqual([e for e in w.events if e[0]=='wait'],[('wait',3),('wait',3)])
            self.assertEqual(len(w.signals()),2)

    def test_primary_term_and_kill_errors_are_both_retained(self):
        with self.world() as w:
            term=PermissionError('TERM denied');kill=OSError('KILL denied')
            w.signal_errors={signal.SIGTERM:term,signal.SIGKILL:kill}
            w.wait_outcomes=[subprocess.TimeoutExpired('fake HOL',3),0]
            with self.assertRaises(subject.ProcessCleanupError) as caught:subject.stop_process(w.process,999)
            self.assertIn(term,caught.exception.errors);self.assertIn(kill,caught.exception.errors)
            self.assertIn(('wait',3),w.events)

    def test_unexpected_grace_wait_error_is_fatal_after_successful_owned_cleanup(self):
        for error in (OSError('grace wait failed'),PermissionError(1,'grace wait denied')):
            with self.subTest(error=type(error).__name__), self.world() as w:
                w.wait_outcomes=[error,-9]
                with self.assertRaises(subject.ProcessCleanupError) as caught:subject.stop_process(w.process,999)
                self.assertEqual(caught.exception.errors,(error,))
                self.assertEqual([e for e in w.events if e[0]=='wait'],[('wait',3),('wait',3)])
                self.assertEqual([e[2] for e in w.signals()],[signal.SIGTERM,signal.SIGKILL])
                self.assertTrue(caught.exception.report['reaped'])
                self.assertFalse(caught.exception.report['verified'])

    def test_grace_wait_interrupt_is_fatal_after_successful_owned_cleanup(self):
        with self.world() as w:
            error=KeyboardInterrupt('grace wait interrupted');w.wait_outcomes=[error,-9]
            with self.assertRaises(subject.ProcessCleanupError) as caught:subject.stop_process(w.process,999)
            self.assertEqual(caught.exception.errors,(error,))
            self.assertEqual([e for e in w.events if e[0]=='wait'],[('wait',3),('wait',3)])
            self.assertEqual([e[2] for e in w.signals()],[signal.SIGTERM,signal.SIGKILL])
            self.assertTrue(caught.exception.report['reaped'])
            self.assertFalse(caught.exception.report['verified'])

    def test_grace_timeout_escalates_once_then_bounded_reap_can_succeed(self):
        with self.world() as w:
            timeout=subprocess.TimeoutExpired('fake HOL',3)
            w.wait_outcomes=[timeout,-9]
            report=subject.stop_process(w.process,98765)
            self.assertEqual([e[2] for e in w.signals()],[signal.SIGTERM,signal.SIGKILL])
            waits=[i for i,e in enumerate(w.events) if e[0]=='wait']
            kill=next(i for i,e in enumerate(w.events) if e[0]=='signal' and e[2]==signal.SIGKILL)
            self.assertEqual(len(waits),2)
            self.assertLess(waits[0],kill);self.assertLess(kill,waits[1])
            self.assertTrue(report['verified']);self.assertEqual(report['errors'],[])
            self.assertIn('term_grace_timeout',report['actions'])
            grace=next(e for e in report['events'] if e['operation']=='wait_term_grace')
            self.assertEqual(grace['error']['type'],'TimeoutExpired')
            self.assertIsNone(grace['cached_returncode_after'])

    def test_no_group_probes_before_last_wait_on_success_or_timeout(self):
        for timed_out in (False,True):
            with self.subTest(timed_out=timed_out), self.world() as w:
                if timed_out:w.wait_outcomes=[subprocess.TimeoutExpired('fake HOL',3),0]
                w.clock_error=AssertionError('old grace clock must not run')
                w.sleep_error=AssertionError('old grace sleep must not run')
                subject.stop_process(w.process,None)
                last_wait=max(i for i,e in enumerate(w.events) if e[0]=='wait')
                probes=[i for i,e in enumerate(w.events) if e[0]=='signal' and e[2]==0]
                self.assertTrue(probes)
                self.assertTrue(all(i>last_wait for i in probes))
                self.assertFalse(any(e[0]=='sleep' for e in w.events))

    def test_pid_reused_after_grace_reap_is_only_probed_and_faulted(self):
        with self.world() as w:
            w.after_wait=lambda:setattr(w,'reused_pid',True)
            with self.assertRaises(subject.ProcessCleanupError) as caught:
                subject.stop_process(w.process,98765)
            self.assertFalse(caught.exception.report['pid_absent'])
            self.assertTrue(caught.exception.report['process_group_absent'])
            self.assertEqual([e[2] for e in w.signals()],[signal.SIGTERM])

    def test_group_reused_after_grace_reap_is_only_probed_and_faulted(self):
        with self.world() as w:
            w.after_wait=lambda:setattr(w,'group_present',True)
            with self.assertRaises(subject.ProcessCleanupError) as caught:
                subject.stop_process(w.process,98765)
            self.assertTrue(caught.exception.report['pid_absent'])
            self.assertFalse(caught.exception.report['process_group_absent'])
            self.assertEqual([e[2] for e in w.signals()],[signal.SIGTERM])

    def test_sigchld_changed_on_grace_timeout_blocks_kill(self):
        with self.world() as w:
            w.wait_outcomes=[subprocess.TimeoutExpired('fake HOL',3),0]
            w.after_wait_error=lambda:setattr(w,'disposition',signal.SIG_IGN)
            with self.assertRaises(subject.ProcessCleanupError) as caught:
                subject.stop_process(w.process,None)
            self.assertIn('SIGCHLD',str(caught.exception))
            self.assertEqual([e[2] for e in w.signals()],[signal.SIGTERM])
            self.assertTrue(caught.exception.report['reaped'])

    def test_term_eperm_is_not_suppressed_when_grace_wait_reaps(self):
        with self.world() as w:
            error=PermissionError(1,'TERM denied')
            w.signal_errors[signal.SIGTERM]=error
            with self.assertRaises(subject.ProcessCleanupError) as caught:
                subject.stop_process(w.process,None)
            self.assertEqual(caught.exception.errors,(error,))
            self.assertTrue(caught.exception.report['reaped'])
            self.assertFalse(caught.exception.report['verified'])
            self.assertEqual([e[2] for e in w.signals()],[signal.SIGTERM])

    def test_kill_eperm_is_not_suppressed_when_final_wait_reaps(self):
        with self.world() as w:
            w.wait_outcomes=[subprocess.TimeoutExpired('fake HOL',3),-15]
            error=PermissionError(1,'KILL denied')
            w.signal_errors[signal.SIGKILL]=error
            with self.assertRaises(subject.ProcessCleanupError) as caught:
                subject.stop_process(w.process,None)
            self.assertEqual(caught.exception.errors,(error,))
            self.assertTrue(caught.exception.report['reaped'])
            self.assertFalse(caught.exception.report['verified'])
            self.assertEqual([e[2] for e in w.signals()],[signal.SIGTERM,signal.SIGKILL])

    def test_unexpected_wait_error_after_reap_cannot_trigger_kill(self):
        for error in (OSError('wait error after cached reap'),KeyboardInterrupt('interrupt after cached reap')):
            with self.subTest(error=type(error).__name__), self.world() as w:
                w.wait_error=error
                def reaped():
                    w.process.returncode=0
                    w.group_present=False
                w.after_wait_error=reaped
                with self.assertRaises(subject.ProcessCleanupError) as caught:
                    subject.stop_process(w.process,None)
                self.assertEqual(caught.exception.errors,(error,))
                self.assertEqual([e[2] for e in w.signals()],[signal.SIGTERM])
                self.assertEqual([e for e in w.events if e[0]=='wait'],[('wait',3)])

    def test_ownership_lost_on_unexpected_grace_error_blocks_kill(self):
        for disposition in (signal.SIG_IGN,lambda *args:None):
            with self.subTest(disposition=disposition), self.world() as w:
                error=OSError('grace wait failed')
                w.wait_outcomes=[error,0]
                w.after_wait_error=lambda:setattr(w,'disposition',disposition)
                with self.assertRaises(subject.ProcessCleanupError) as caught:
                    subject.stop_process(w.process,None)
                self.assertIs(caught.exception.errors[0],error)
                self.assertIn('SIGCHLD',str(caught.exception))
                self.assertEqual([e[2] for e in w.signals()],[signal.SIGTERM])
                self.assertTrue(caught.exception.report['reaped'])
                self.assertFalse(caught.exception.report['verified'])

    def test_original_grace_error_and_final_reap_error_are_both_preserved(self):
        with self.world() as w:
            primary=OSError('grace wait failed')
            cleanup=subprocess.TimeoutExpired('fake HOL',3)
            w.wait_outcomes=[primary,cleanup]
            with self.assertRaises(subject.ProcessCleanupError) as caught:
                subject.stop_process(w.process,None)
            self.assertIs(caught.exception.errors[0],primary)
            self.assertIs(caught.exception.errors[1],cleanup)
            self.assertFalse(caught.exception.report['reaped'])
            self.assertEqual([e for e in w.events if e[0]=='wait'],[('wait',3),('wait',3)])
            self.assertEqual([e[2] for e in w.signals()],[signal.SIGTERM,signal.SIGKILL])

    def test_uninspectable_post_reap_group_fails_closed(self):
        with self.world(reaped=True) as w:
            error=PermissionError('probe denied');w.probe_error=error
            with self.assertRaises(subject.ProcessCleanupError) as caught:subject.stop_process(w.process,999)
            self.assertIn(error,caught.exception.errors)
            self.assertIsNone(caught.exception.report['process_group_absent'])
            self.assertEqual(w.signals(),[])

    def test_invalid_root_pid_cannot_target_global_groups(self):
        for pid in (0,1,-1,True,'321'):
            with self.subTest(pid=pid), self.world() as w:
                w.process.pid=pid
                with self.assertRaises(subject.ProcessCleanupError):subject.stop_process(w.process,999)
                self.assertEqual(w.signals(),[])

    def test_finish_preserves_primary_cleanup_and_close_failures(self):
        with self.world(reaped=True,residual=True) as w:
            primary=ValueError('startup failure');close=OSError('close failure');w.close_error=close
            with self.assertRaises(subject.ServeCleanupError) as caught:
                subject.finish_process(w.process,999,primary)
            error=caught.exception
            self.assertIs(error.primary,primary);self.assertIs(error.__cause__,primary)
            self.assertEqual(len(error.cleanup),2)
            self.assertIsInstance(error.cleanup[0],subject.ProcessCleanupError)
            self.assertIs(error.cleanup[1],close)
            self.assertIn('startup failure',str(error));self.assertIn('close failure',str(error))

    def test_finish_success_does_not_replace_primary(self):
        with self.world(reaped=True) as w:
            subject.finish_process(w.process,None,ValueError('original remains with caller'))
            self.assertIn(('close',),w.events)

    def test_finish_close_only_failure_is_visible(self):
        with self.world(reaped=True) as w:
            error=OSError('close');w.close_error=error
            with self.assertRaises(subject.ServeCleanupError) as caught:
                subject.finish_process(w.process,None,None)
            self.assertIsNone(caught.exception.primary)
            self.assertEqual(caught.exception.cleanup,(error,))

    def test_finish_skips_closed_or_absent_stdin_without_touching_a_descriptor(self):
        for missing in (False, True):
            with self.subTest(missing=missing), self.world(reaped=True) as w:
                if missing:
                    w.process.stdin=None
                subject.finish_process(w.process,None,None)
                self.assertFalse(any(e[0].startswith('stdin_') for e in w.events))

    def test_finish_open_stdin_is_nonblocking_and_closed_after_owned_cleanup(self):
        with self.world() as w:
            w.process.stdin.closed=False
            subject.finish_process(w.process,None,None)
            self.assertTrue(w.process.stdin.closed)
            self.assertLess(w.events.index(('wait',3)),w.events.index(('stdin_fileno',)))
            self.assertLess(w.events.index(('stdin_set_blocking',654,False)),
                            w.events.index(('stdin_close',False)))
            self.assertLess(w.events.index(('stdin_close',False)),w.events.index(('close',)))
            self.assertEqual([e for e in w.events if e[0]=='stdin_close'],[('stdin_close',False)])

    def test_finish_never_closes_stdin_if_nonblocking_cannot_be_established(self):
        for field in ('fileno_error','blocking_error'):
            with self.subTest(field=field), self.world(reaped=True) as w:
                w.process.stdin.closed=False
                error=OSError('nonblocking setup failed')
                setattr(w.process.stdin,field,error)
                with self.assertRaises(subject.ServeCleanupError) as caught:
                    subject.finish_process(w.process,None,None)
                self.assertEqual(caught.exception.cleanup,(error,))
                self.assertFalse(w.process.stdin.closed)
                self.assertFalse(any(e[0]=='stdin_close' for e in w.events))
                self.assertIn(('close',),w.events)

    def test_finish_nonblocking_flush_failure_is_retained_without_retry(self):
        with self.world(reaped=True) as w:
            w.process.stdin.closed=False
            error=BlockingIOError('pending buffered bytes cannot flush')
            w.process.stdin.close_errors=[error]
            with self.assertRaises(subject.ServeCleanupError) as caught:
                subject.finish_process(w.process,None,None)
            self.assertEqual(caught.exception.cleanup,(error,))
            self.assertEqual([e for e in w.events if e[0]=='stdin_close'],[('stdin_close',False)])
            self.assertIn(('close',),w.events)

    def test_finish_preserves_primary_process_stdin_and_stdout_errors(self):
        with self.world(reaped=True,residual=True) as w:
            primary=ValueError('startup write failed')
            stdin_error=BlockingIOError('stdin flush failed')
            stdout_error=OSError('stdout close failed')
            w.process.stdin.closed=False
            w.process.stdin.close_errors=[stdin_error]
            w.close_error=stdout_error
            with self.assertRaises(subject.ServeCleanupError) as caught:
                subject.finish_process(w.process,None,primary)
            self.assertIs(caught.exception.primary,primary)
            self.assertIs(caught.exception.__cause__,primary)
            self.assertIsInstance(caught.exception.cleanup[0],subject.ProcessCleanupError)
            self.assertEqual(caught.exception.cleanup[1:],(stdin_error,stdout_error))
            self.assertEqual(w.signals(),[])
            self.assertEqual([e for e in w.events if e[0]=='stdin_close'],[('stdin_close',False)])

    def serve_failure(self, primary, cleanup=None, close=None, at_close=False, stdin_error=None):
        events=[]
        stdin=InputPipe(events,closed=False)
        process=SimpleNamespace(pid=321,returncode=0,
            stdin=stdin,stdout=mock.Mock())
        if at_close:
            stdin.close_errors=[primary,stdin_error]
        else:
            stdin.write_error=primary
            stdin.close_errors=[stdin_error]
        process.stdout.close.side_effect=close
        with ExitStack() as stack:
            stack.enter_context(mock.patch.object(Path,'is_file',return_value=True))
            stack.enter_context(mock.patch.object(subject.subprocess,'run',return_value=SimpleNamespace(stdout='/fake/lib')))
            popen=stack.enter_context(mock.patch.object(subject.subprocess,'Popen',return_value=process))
            stack.enter_context(mock.patch.object(subject.tempfile,'TemporaryDirectory',return_value=nullcontext('/fake/private')))
            stack.enter_context(mock.patch.object(subject.os,'chmod'))
            stack.enter_context(mock.patch.object(subject.os,'set_blocking',side_effect=stdin.set_blocking))
            handlers=stack.enter_context(mock.patch.object(subject.signal,'signal',return_value=signal.SIG_DFL))
            stack.enter_context(mock.patch.object(subject.signal,'getsignal',return_value=signal.SIG_DFL))
            stack.enter_context(mock.patch.object(subject,'project_snapshot',return_value={}))
            stopper=stack.enter_context(mock.patch.object(subject,'stop_process',side_effect=cleanup))
            try:
                subject.serve([])
            finally:
                self.assertTrue(popen.call_args.kwargs['start_new_session'])
                stopper.assert_called_once_with(process,None)
                process.stdout.close.assert_called_once()
                self.assertEqual(handlers.call_count,4)
                expected=[('stdin_close',True),('stdin_close',False)] if at_close else [('stdin_close',False)]
                self.assertEqual([e for e in events if e[0]=='stdin_close'],expected)
                self.assertEqual([e for e in events if e[0]=='stdin_set_blocking'],
                                 [('stdin_set_blocking',654,False)])

    def test_actual_serve_finally_retains_all_three_errors(self):
        primary=ValueError('bootstrap');cleanup=RuntimeError('teardown');close=OSError('pipe close')
        with self.assertRaises(subject.ServeCleanupError) as caught:
            self.serve_failure(primary,cleanup,close)
        self.assertIs(caught.exception.primary,primary)
        self.assertEqual(caught.exception.cleanup,(cleanup,close))

    def test_actual_serve_preserves_original_when_cleanup_succeeds(self):
        primary=RuntimeError('original')
        with self.assertRaises(RuntimeError) as caught:self.serve_failure(primary)
        self.assertIs(caught.exception,primary)

    def test_actual_serve_preserves_keyboard_interrupt_with_cleanup_error(self):
        primary=KeyboardInterrupt();cleanup=RuntimeError('teardown')
        with self.assertRaises(subject.ServeCleanupError) as caught:self.serve_failure(primary,cleanup)
        self.assertIs(caught.exception.primary,primary)
        self.assertIs(caught.exception.__cause__,primary)

    def test_actual_serve_initial_stdin_close_failure_is_preserved_after_cleanup(self):
        primary=OSError('initial bootstrap close failed')
        with self.assertRaises(OSError) as caught:
            self.serve_failure(primary,at_close=True)
        self.assertIs(caught.exception,primary)

    def test_actual_serve_initial_close_and_all_cleanup_failures_remain_distinct(self):
        primary=OSError('initial bootstrap close failed')
        cleanup=RuntimeError('owned teardown failed')
        stdin_error=BlockingIOError('nonblocking stdin flush failed')
        stdout_error=OSError('stdout close failed')
        with self.assertRaises(subject.ServeCleanupError) as caught:
            self.serve_failure(primary,cleanup,stdout_error,at_close=True,stdin_error=stdin_error)
        self.assertIs(caught.exception.primary,primary)
        self.assertEqual(caught.exception.cleanup,(cleanup,stdin_error,stdout_error))

    def test_serve_refuses_unsafe_sigchld_before_creating_a_child(self):
        for disposition in (signal.SIG_IGN,lambda *args:None):
            with self.subTest(disposition=disposition), \
                 mock.patch.object(subject.signal,'getsignal',return_value=disposition), \
                 mock.patch.object(subject.subprocess,'Popen') as spawn:
                with self.assertRaisesRegex(RuntimeError,'requires default SIGCHLD'):
                    subject.serve([])
                spawn.assert_not_called()

if __name__=='__main__':
    unittest.main()
