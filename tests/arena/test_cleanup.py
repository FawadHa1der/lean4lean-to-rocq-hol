"""Pure mock ownership/error controls. No checker, OS probes, signals or threads."""
import argparse
import contextlib
import errno
import importlib.util
import inspect
import io
import json
import os
from pathlib import Path
import signal
import subprocess
import tempfile
import threading
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


runner = load("private_arena_cleanup", ROOT / "scripts/test_arena.py")
reference = load("reviewed_owned_cleanup", ROOT / "tests/arena/cleanup_reference.py")


class Child:
    pid = 123456789

    def __init__(self, waits=(), code=None):
        self.returncode = code
        self.waits = list(waits)
        self.stdout = io.BytesIO(b"prefix\n")
        self.stderr = io.BytesIO(b"detail\n")
        self.stdin = None
        self.events = []
        self.poll_error = self.kill_error = None
        self.poll_completion = None

    def poll(self):
        self.events.append(("poll", self.returncode))
        if self.poll_error:
            raise self.poll_error
        if self.poll_completion is not None:
            self.returncode = self.poll_completion
        return self.returncode

    def wait(self, timeout=None):
        assert timeout is not None and 0 < timeout <= 30, "unbounded wait"
        self.events.append(("wait", timeout))
        value = self.waits.pop(0) if self.waits else self.returncode
        if isinstance(value, BaseException):
            raise value
        self.returncode = value
        return value

    def kill(self):
        self.events.append(("direct_kill", self.returncode))
        assert self.returncode is None, "destructive signal after reap"
        if self.kill_error:
            raise self.kill_error


class Reader:
    active = False

    def __init__(self, target, args, daemon):
        assert daemon
        self.target, self.args = target, args
        self.ident = None
        self.joins = []

    def start(self):
        self.ident = 1
        if not self.active:
            self.target(*self.args)

    def join(self, timeout=None):
        assert timeout is not None and 0 <= timeout <= 30, "unbounded join"
        self.joins.append(timeout)

    def is_alive(self):
        return self.active and self.ident is not None


class Harness(unittest.TestCase):
    def setUp(self):
        self.stack = contextlib.ExitStack()
        self.addCleanup(self.stack.close)
        self.child = Child(waits=[0])
        self.signals = []
        self.group_error = self.probe_error = None
        self.pid_present = self.group_present = False
        self.group_exit_after_poll = False
        self.spawn = self.stack.enter_context(mock.patch.object(subprocess, "Popen", side_effect=self.launch))
        self.stack.enter_context(mock.patch.object(subprocess, "run", side_effect=AssertionError("subprocess.run forbidden")))
        self.stack.enter_context(mock.patch.object(os, "killpg", side_effect=self.killpg))
        self.stack.enter_context(mock.patch.object(os, "kill", side_effect=self.kill))
        self.stack.enter_context(mock.patch.object(threading, "Thread", side_effect=Reader))
        self.getsignal = self.stack.enter_context(mock.patch.object(signal, "getsignal", return_value=signal.SIG_DFL))
        self.setsignal = self.stack.enter_context(mock.patch.object(signal, "signal", side_effect=AssertionError("handler mutation forbidden")))
        self.tmp = self.stack.enter_context(tempfile.TemporaryDirectory())
        self.root = Path(self.tmp).resolve()
        self.evidence = Path(os.environ.get("ARENA_CLEANUP_EVIDENCE_DIR", str(self.root / "evidence")))
        self.evidence.mkdir(parents=True, exist_ok=True)
        self.path = self.root / "input.ndjson"
        self.path.write_bytes(b'{"mock":true}\n')
        self.case = {"id": "fake", "expected": "accept", "availability": "available",
                     "path": self.path.name, "size": self.path.stat().st_size,
                     "sha256": runner.digest(self.path), "timeout_seconds": 3}
        self.args = argparse.Namespace(checker="fake-checker", select=[], skip=[], timeout=None,
                                       default_timeout=30, input_mode="file", max_log_bytes=256)

    def launch(self, command, **kwargs):
        self.getsignal.assert_called_with(signal.SIGCHLD)
        self.assertTrue(kwargs["start_new_session"])
        self.assertEqual(kwargs["env"]["IN"], str(self.path))
        return self.child

    def absence(self, present):
        if self.probe_error:
            raise self.probe_error
        if not present:
            raise ProcessLookupError(errno.ESRCH, "mock absence")

    def killpg(self, pid, sig):
        self.assertEqual(pid, self.child.pid)
        self.signals.append(("group", sig))
        self.child.events.append(("group_signal", sig))
        if sig == 0:
            return self.absence(self.group_present)
        self.assertEqual(sig, signal.SIGKILL)
        self.assertIsNone(self.child.returncode)
        self.assertEqual(self.child.events[-2], ("poll", None))
        if self.group_exit_after_poll:
            self.child.events.append(("exited_unreaped", None))
        if self.group_error:
            raise self.group_error

    def kill(self, pid, sig):
        self.assertEqual((pid, sig), (self.child.pid, 0))
        self.signals.append(("pid", sig))
        return self.absence(self.pid_present)

    def cleanup(self):
        try:
            return runner.stop_group(self.child)
        except runner.ProcessCleanupError as exc:
            return exc.receipt

    def run_case(self):
        return runner.run_case(self.case, self.root, self.args)

    def assert_read_only(self):
        self.assertTrue(all(sig == 0 for _, sig in self.signals))
        self.assertFalse(any(event[0] == "direct_kill" for event in self.child.events))


class CleanupTests(Harness):
    def test_reaped_success_reject_decline_fault_all_read_only(self):
        for code in (0, 1, 2, 3, -9):
            with self.subTest(code=code):
                self.child = Child(code=code)
                receipt = self.cleanup()
                self.assertTrue(receipt["verified"])
                self.assertEqual(self.child.events, [("poll", code), ("group_signal", 0)])
                self.assert_read_only()

    def test_reused_pid_group_and_surviving_group_fail_closed(self):
        for pid, group in ((True, True), (True, False), (False, True)):
            with self.subTest(pid=pid, group=group):
                self.child = Child(code=0)
                self.pid_present, self.group_present = pid, group
                receipt = self.cleanup()
                self.assertFalse(receipt["verified"])
                self.assertEqual(receipt["pid_absent"], not pid)
                self.assertEqual(receipt["process_group_absent"], not group)
                self.assertEqual(receipt["errors"][0]["operation"], "verify_cleanup")
                self.assert_read_only()

    def test_running_leader_signalled_before_bounded_reap(self):
        self.child = Child(waits=[-9])
        receipt = self.cleanup()
        self.assertTrue(receipt["verified"])
        self.assertEqual(self.child.events[:3], [("poll", None), ("group_signal", signal.SIGKILL), ("wait", 10)])

    def test_poll_reaps_just_exited_leader_never_signals_group(self):
        self.child.poll_completion = 0
        self.assertTrue(self.cleanup()["verified"])
        self.assert_read_only()

    def test_exit_between_poll_and_signal_remains_unreaped(self):
        self.group_exit_after_poll = True
        self.assertTrue(self.cleanup()["verified"])
        self.assertIn(("exited_unreaped", None), self.child.events)

    def test_group_esrch_uses_direct_handle_and_bounded_reap(self):
        self.group_error = ProcessLookupError(errno.ESRCH, "gone")
        receipt = self.cleanup()
        self.assertTrue(receipt["verified"])
        self.assertEqual(receipt["actions"], ["owned_group_already_absent", "direct_handle_kill"])

    def test_signal_permission_error_preserved_despite_successful_reap(self):
        self.group_error = PermissionError(errno.EPERM, "group denied")
        receipt = self.cleanup()
        self.assertFalse(receipt["verified"])
        self.assertTrue(receipt["reaped"])
        self.assertEqual(receipt["errors"][0]["errno"], errno.EPERM)
        self.assertIn("PermissionError", receipt["errors"][0]["traceback"])
        self.assertIn(("direct_kill", None), self.child.events)

    def test_all_secondary_errors_survive(self):
        self.group_error = PermissionError(errno.EPERM, "group denied")
        self.child.kill_error = OSError(errno.EIO, "direct denied")
        self.child.waits = [subprocess.TimeoutExpired("mock-reap", 10)]
        self.probe_error = PermissionError(errno.EACCES, "observation denied")
        receipt = self.cleanup()
        self.assertFalse(receipt["verified"])
        self.assertFalse(receipt["reaped"])
        self.assertEqual([error["operation"] for error in receipt["errors"]],
                         ["kill_process_group", "kill_direct_handle", "reap_process", "pid_absent", "process_group_absent"])

    def test_poll_error_never_authorizes_group_signal(self):
        self.child.poll_error = OSError(errno.EIO, "poll failed")
        receipt = self.cleanup()
        self.assertFalse(receipt["verified"])
        self.assertTrue(all(sig == 0 for _, sig in self.signals))
        self.assertIn(("direct_kill", None), self.child.events)

    def test_reap_timeout_one_bounded_wait_no_retry(self):
        self.child.waits = [subprocess.TimeoutExpired("reap", 10)]
        receipt = self.cleanup()
        self.assertFalse(receipt["verified"])
        self.assertEqual([e for e in self.child.events if e[0] == "wait"], [("wait", 10)])
        self.assertEqual(receipt["errors"][0]["type"], "TimeoutExpired")

    def test_non_reaping_wait_result_is_not_success(self):
        self.child.waits = [None]
        self.assertFalse(self.cleanup()["verified"])

    def test_absence_permission_error_unknown_not_absent(self):
        self.child = Child(code=0)
        self.probe_error = PermissionError(errno.EPERM, "probe denied")
        receipt = self.cleanup()
        self.assertIsNone(receipt["pid_absent"])
        self.assertIsNone(receipt["process_group_absent"])
        self.assertFalse(receipt["verified"])
        self.assert_read_only()

    def test_second_cleanup_after_reap_never_signals_reused_group(self):
        self.assertTrue(self.cleanup()["verified"])
        self.signals.clear()
        self.child.events.clear()
        self.group_present = True
        self.assertFalse(self.cleanup()["verified"])
        self.assert_read_only()

    def test_reviewed_helper_algorithm_controls_match(self):
        for scenario in ("live", "reaped", "reused", "denied", "esrch", "poll-error", "timeout"):
            def prepare():
                self.child = Child(waits=[0], code=0 if scenario in ("reaped", "reused") else None)
                self.pid_present = self.group_present = scenario == "reused"
                self.group_error = (PermissionError(errno.EPERM, "denied") if scenario == "denied" else
                                    ProcessLookupError(errno.ESRCH, "gone") if scenario == "esrch" else None)
                if scenario == "poll-error":
                    self.child.poll_error = OSError(errno.EIO, "poll failed")
                if scenario == "timeout":
                    self.child.waits = [subprocess.TimeoutExpired("reap", 10)]
            with self.subTest(scenario=scenario):
                prepare()
                original = reference.cleanup_owned_process(self.child)
                original_events = list(self.child.events)
                prepare()
                actual = self.cleanup()
                self.assertEqual(self.child.events, original_events)
                for key in ("verified", "reaped", "actions", "pid_absent", "process_group_absent"):
                    self.assertEqual(actual[key], original[key], key)


class ProcessTests(Harness):
    def test_symlink_manifest_root_uses_canonical_input(self):
        alias = self.root / "alias"
        alias.symlink_to(self.root, target_is_directory=True)
        result = runner.run_case(self.case, alias, self.args)
        self.assertEqual(result["status"], "correct_accept")
        self.spawn.assert_called_once()
        self.assertEqual(self.spawn.call_args.kwargs["env"]["IN"], str(self.path))
        self.assert_read_only()

    def test_success_decline_fault_mapping_and_logs_unchanged(self):
        for expected in ("accept", "reject", "either"):
            for code in (0, 1, 2, 3, 17, -9):
                with self.subTest(expected=expected, code=code):
                    self.child = Child(waits=[code])
                    self.case["expected"] = expected
                    result = self.run_case()
                    self.assertEqual(result["status"], runner.classify(code, expected))
                    self.assertEqual(result["exit_code"], code)
                    self.assertEqual(result["stdout"], "prefix\n")
                    self.assertEqual(result["stderr"], "detail\n")
                    self.assertTrue(result["cleanup_verified"])
                    if code == 2:
                        self.assertEqual(result["decline_kind"], "checker_declared")
                    self.assert_read_only()

    def test_timeout_not_decline_bounded_cleanup(self):
        self.child = Child(waits=[subprocess.TimeoutExpired("case", 3), -9])
        result = self.run_case()
        self.assertEqual(result["status"], "timeout")
        self.assertTrue(result["cleanup_verified"])
        self.assertEqual(result["wait_timeout"]["type"], "TimeoutExpired")
        self.assertEqual([e for e in self.child.events if e[0] == "wait"], [("wait", 3), ("wait", 10)])

    def test_primary_wait_and_all_cleanup_errors_retained_in_order(self):
        primary = OSError(errno.EIO, "primary wait")
        self.child = Child(waits=[primary, subprocess.TimeoutExpired("cleanup wait", 10)])
        self.group_error = PermissionError(errno.EPERM, "group denied")
        self.child.kill_error = PermissionError(errno.EACCES, "direct denied")
        self.probe_error = OSError(errno.EIO, "probe failed")
        result = self.run_case()
        (self.evidence / "error-order.json").write_text(json.dumps(result, indent=2) + "\n")
        self.assertEqual(result["status"], "execution_error")
        self.assertIn("primary wait", result["reason"])
        self.assertFalse(result["cleanup_verified"])
        self.assertEqual([error["operation"] for error in result["execution_errors"]],
                         ["wait_process", "kill_process_group", "kill_direct_handle", "reap_process", "pid_absent", "process_group_absent"])
        self.assertEqual([error["operation"] for error in result["cleanup"]["errors"]],
                         ["kill_process_group", "kill_direct_handle", "reap_process", "pid_absent", "process_group_absent"])
        self.assertEqual(result["stdout"], "prefix\n")

    def test_same_exception_in_two_actions_not_coalesced(self):
        shared = PermissionError(errno.EPERM, "same failure object in independent actions")
        self.child = Child(waits=[shared, -9])
        self.group_error = shared
        result = self.run_case()
        self.assertEqual(result["status"], "execution_error")
        self.assertEqual([e["operation"] for e in result["execution_errors"]], ["wait_process", "kill_process_group"])
        self.assertTrue(all(e["errno"] == errno.EPERM for e in result["execution_errors"]))
        self.assertIn(str(shared), result["reason"])
        (self.evidence / "same-instance.json").write_text(json.dumps(result, indent=2) + "\n")

    def test_wait_error_propagation_does_not_duplicate_action(self):
        self.child = Child(waits=[OSError(errno.EIO, "wait failed"), -9])
        result = self.run_case()
        self.assertEqual([e["operation"] for e in result["execution_errors"]], ["wait_process"])
        self.assertTrue(result["cleanup_verified"])

    def test_unobserved_setup_fallback_recorded_once(self):
        with mock.patch.object(threading, "Thread", side_effect=OSError(errno.EIO, "setup failed")):
            result = self.run_case()
        self.assertEqual([e["operation"] for e in result["execution_errors"]], ["process_setup_or_wait"])

    def test_observed_stop_wrapper_propagation_does_not_duplicate(self):
        failure = PermissionError(errno.EPERM, "wrapped action")
        def wrapper(proc, observe):
            def fail():
                raise failure
            return observe("wrapped_cleanup_action", fail)
        with mock.patch.object(runner, "stop_group", side_effect=wrapper):
            result = self.run_case()
        self.assertEqual([e["operation"] for e in result["execution_errors"]], ["wrapped_cleanup_action"])
        self.assertEqual(result["status"], "execution_error")
        self.assertFalse(result["cleanup_verified"])

    def test_shared_reader_error_objects_retained_and_collection_locked(self):
        class CheckedLock:
            held = False
            entries = 0
            def __enter__(self):
                assert not self.held
                self.held = True
                self.entries += 1
            def __exit__(self, *args):
                self.held = False
        lock = CheckedLock()
        shared = OSError(errno.EIO, "both readers failed")
        self.child.stdout = mock.Mock()
        self.child.stderr = mock.Mock()
        self.child.stdout.read.side_effect = shared
        self.child.stderr.read.side_effect = shared
        real_stop, real_evidence = runner.stop_group, runner.error_evidence
        def evidence(operation, exc):
            self.assertTrue(lock.held, "shared error serialization must hold the lock")
            return real_evidence(operation, exc)
        def cleanup(proc, observe):
            record = inspect.getclosurevars(observe).nonlocals["record_error"]
            refs = inspect.getclosurevars(record).nonlocals["observed_errors"]
            self.assertIs(refs[id(shared)], shared, "must retain actual exception to prevent id reuse")
            self.assertFalse(lock.held, "no lock may be held during cleanup")
            return real_stop(proc, observe)
        with mock.patch.object(threading, "Lock", return_value=lock), \
             mock.patch.object(runner, "error_evidence", side_effect=evidence), \
             mock.patch.object(runner, "stop_group", side_effect=cleanup):
            result = self.run_case()
        self.assertEqual([e["operation"] for e in result["execution_errors"]], ["read_stdout", "read_stderr"])
        self.assertFalse(lock.held)
        self.assertGreaterEqual(lock.entries, 5)  # Two observations, two propagations, snapshot.
        self.assertFalse(result["capture_complete"])

    def test_sigchld_default_checked_immediately_before_spawn(self):
        events = []
        self.getsignal.side_effect = lambda sig: events.append("default_checked") or signal.SIG_DFL
        def launch(*args, **kwargs):
            self.assertEqual(events, ["default_checked"])
            events.append("spawn")
            return self.launch(*args, **kwargs)
        self.spawn.side_effect = launch
        result = self.run_case()
        self.assertEqual(events, ["default_checked", "spawn"])
        self.assertTrue(result["sigchld_default_verified"])
        self.assertEqual(result["status"], "correct_accept")
        self.setsignal.assert_not_called()

    def test_sigchld_ignore_custom_unknown_refused_without_reset_or_spawn(self):
        outcomes = []
        for label, handler in (("ignored", signal.SIG_IGN), ("custom", lambda *_: None),
                               ("unknown", None), ("unrecognized", object())):
            with self.subTest(handler=label):
                self.getsignal.return_value = handler
                result = self.run_case()
                outcomes.append({"handler": label, "result": result})
                self.assertEqual(result["status"], "execution_error")
                self.assertFalse(result["sigchld_default_verified"])
                self.assertIsNone(result["process_id"])
                self.assertIsNone(result["exit_code"])
                self.assertEqual([e["operation"] for e in result["execution_errors"]], ["verify_sigchld_default"])
                self.assertEqual(result["execution_errors"][0]["errno"], errno.EINVAL)
                self.assertTrue(result["cleanup_verified"])
        self.spawn.assert_not_called()
        self.setsignal.assert_not_called()
        self.assertEqual(self.signals, [])
        (self.evidence / "sigchld-refusals.json").write_text(json.dumps(outcomes, indent=2) + "\n")

    def test_sigchld_query_failure_is_operational_no_spawn(self):
        self.getsignal.side_effect = PermissionError(errno.EPERM, "handler query failed")
        result = self.run_case()
        self.assertEqual(result["status"], "execution_error")
        self.assertEqual([e["operation"] for e in result["execution_errors"]], ["verify_sigchld_default"])
        self.assertEqual(result["execution_errors"][0]["errno"], errno.EPERM)
        self.assertFalse(result["sigchld_default_verified"])
        self.spawn.assert_not_called()
        self.setsignal.assert_not_called()

    def test_refused_sigchld_closes_open_input_preserving_both_errors(self):
        self.getsignal.return_value = signal.SIG_IGN
        path = mock.Mock()
        path.open.return_value.close.side_effect = OSError(errno.EIO, "input close failed")
        with self.assertRaises(runner.ProcessExecutionError) as caught:
            runner.run_process(["fake"], path, 3, "file", 256)
        result = caught.exception.evidence
        self.assertEqual([e["operation"] for e in result["execution_errors"]], ["verify_sigchld_default", "close_input"])
        self.assertIn("SIGCHLD", str(caught.exception))
        self.spawn.assert_not_called()
        path.open.return_value.close.assert_called_once()

    def test_refused_sigchld_accounts_all_mock_cases_without_launch(self):
        cases = [{**self.case, "id": f"handler/{i}"} for i in range(3)]
        cases[2]["availability"] = "missing_generated"
        manifest, report = self.root / "manifest.json", self.root / "report.json"
        manifest.write_text(json.dumps({"manifest_version": 1, "cases": cases}))
        self.getsignal.return_value = signal.SIG_IGN
        with contextlib.redirect_stdout(io.StringIO()):
            code = runner.main(["--manifest", str(manifest), "--checker", "fake-checker", "--report", str(report)])
        data = json.loads(report.read_text())
        self.assertEqual(code, 1)
        self.assertEqual([r["id"] for r in data["results"]], [c["id"] for c in cases])
        self.assertEqual(data["summary"]["statuses"], {"execution_error": 2, "missing_generated": 1})
        self.spawn.assert_not_called()
        self.setsignal.assert_not_called()

    def test_timeout_with_reap_timeout_is_execution_error(self):
        self.child = Child(waits=[subprocess.TimeoutExpired("case", 3), subprocess.TimeoutExpired("reap", 10)])
        result = self.run_case()
        self.assertEqual(result["status"], "execution_error")
        self.assertTrue(result["timed_out"])
        self.assertIsNotNone(result["wait_timeout"])
        self.assertFalse(result["cleanup_verified"])

    def test_reaped_reject_then_reused_group_never_signalled(self):
        self.child = Child(waits=[1])
        self.case["expected"] = "reject"
        self.group_present = True
        result = self.run_case()
        self.assertEqual(result["status"], "execution_error")
        self.assertEqual(result["exit_code"], 1)
        self.assertEqual(result["verdict"], "reject")
        self.assertFalse(result["cleanup_verified"])
        self.assert_read_only()

    def test_wrapper_error_not_silently_accepted(self):
        with mock.patch.object(runner, "stop_group", side_effect=PermissionError(errno.EPERM, "wrapper denied")):
            result = self.run_case()
        self.assertEqual(result["status"], "execution_error")
        self.assertFalse(result["cleanup_verified"])
        self.assertEqual(result["execution_errors"][0]["operation"], "stop_group")

    def test_missing_cleanup_receipt_not_silently_accepted(self):
        with mock.patch.object(runner, "stop_group", return_value=None):
            result = self.run_case()
        self.assertEqual(result["status"], "execution_error")
        self.assertTrue(result["group_stop_returned"])
        self.assertFalse(result["cleanup_verified"])
        self.assertIn("no verified receipt", result["reason"])

    def test_non_os_primary_error_survives_cleanup_error(self):
        self.child = Child(waits=[RuntimeError("primary wait failure"), -9])
        self.group_error = PermissionError(errno.EPERM, "cleanup denied")
        result = self.run_case()
        self.assertEqual(result["status"], "execution_error")
        self.assertIn("primary wait failure", result["reason"])
        self.assertEqual(result["execution_errors"][0]["type"], "RuntimeError")
        self.assertTrue(any(e["errno"] == errno.EPERM for e in result["execution_errors"]))

    def test_interrupt_preserves_object_and_secondary_evidence(self):
        primary = KeyboardInterrupt("primary interrupt")
        self.child = Child(waits=[primary, -9])
        self.group_error = PermissionError(errno.EPERM, "secondary denied")
        with self.assertRaises(KeyboardInterrupt) as caught:
            self.run_case()
        self.assertIs(caught.exception, primary)
        evidence = primary.arena_evidence
        self.assertEqual(evidence["exit_code"], -9)
        self.assertEqual(evidence["execution_errors"][0]["type"], "KeyboardInterrupt")
        self.assertTrue(any(e["errno"] == errno.EPERM for e in evidence["execution_errors"]))
        json.dumps(evidence)

    def test_cleanup_interrupt_not_converted_to_logical_verdict(self):
        interrupt = KeyboardInterrupt("cleanup interrupt")
        self.child.poll_error = interrupt
        with self.assertRaises(KeyboardInterrupt) as caught:
            self.run_case()
        self.assertIs(caught.exception, interrupt)
        self.assertFalse(interrupt.arena_evidence["cleanup_verified"])
        self.assert_read_only()

    def test_post_reap_primary_error_cannot_signal(self):
        self.child = Child(waits=[OSError(errno.EIO, "post reap wait")], code=0)
        result = self.run_case()
        self.assertEqual(result["status"], "execution_error")
        self.assertEqual(result["exit_code"], 0)
        self.assertTrue(result["cleanup_verified"])
        self.assert_read_only()

    def test_unstarted_pipes_closed_after_thread_setup_failure(self):
        with mock.patch.object(threading, "Thread", side_effect=RuntimeError("thread construction failed")):
            result = self.run_case()
        self.assertEqual(result["status"], "execution_error")
        self.assertEqual(result["execution_errors"][0]["operation"], "process_setup_or_wait")
        self.assertTrue(self.child.stdout.closed)
        self.assertTrue(self.child.stderr.closed)
        self.assertFalse(result["capture_complete"])

    def test_active_readers_not_silently_left_as_timeout_only(self):
        class ActiveReader(Reader):
            active = True
        with mock.patch.object(threading, "Thread", side_effect=ActiveReader):
            result = self.run_case()
        self.assertEqual(result["status"], "execution_error")
        self.assertTrue(result["timed_out"])
        self.assertFalse(result["cleanup_verified"])
        self.assertFalse(result["capture_complete"])
        self.assertEqual(result["execution_errors"][0]["operation"], "finish_log_readers")
        self.assert_read_only()

    def test_missing_executable_no_claimed_execution(self):
        self.spawn.side_effect = FileNotFoundError(errno.ENOENT, "mock missing")
        result = self.run_case()
        self.assertEqual(result["status"], "execution_error")
        self.assertIsNone(result["process_id"])
        self.assertTrue(result["cleanup_verified"])
        self.assertFalse(result["group_stop_returned"])

    def test_read_close_and_input_close_errors_all_retained(self):
        self.child.stdout = mock.Mock()
        self.child.stdout.read.side_effect = [b"kept", OSError(errno.EIO, "read failed")]
        self.child.stdout.close.side_effect = OSError(errno.EIO, "stream close failed")
        path = mock.Mock()
        path.open.return_value.close.side_effect = OSError(errno.EIO, "input close failed")
        with mock.patch.object(self, "launch", return_value=self.child):
            self.spawn.side_effect = None
            self.spawn.return_value = self.child
            with self.assertRaises(runner.ProcessExecutionError) as caught:
                runner.run_process(["fake"], path, 3, "file", 256)
        result = caught.exception.evidence
        self.assertEqual(result["stdout"], "kept")
        self.assertEqual([e["operation"] for e in result["execution_errors"]], ["read_stdout", "close_stdout", "close_input"])

    def test_logs_remain_bounded(self):
        self.child.stdout = io.BytesIO(b"x" * 1000)
        self.args.max_log_bytes = 17
        result = self.run_case()
        self.assertEqual(len(result["stdout"]), 17)
        self.assertEqual(result["stdout_bytes"], 1000)
        self.assertTrue(result["stdout_truncated"])

    def test_case_caps_and_explicit_override_unchanged(self):
        for override, cap in ((None, 3), (2, 2)):
            self.child = Child(waits=[0])
            self.args.timeout = override
            self.assertEqual(self.run_case()["timeout_seconds"], cap)
            self.assertIn(("wait", cap), self.child.events)

    def test_post_execution_integrity_failure_still_not_verdict(self):
        with mock.patch.object(runner, "digest", side_effect=[self.case["sha256"], "0" * 64]):
            result = self.run_case()
        self.assertEqual(result["status"], "input_error")
        self.assertEqual(result["exit_code"], 0)

    def test_all_221_records_accounted_after_unverified_cleanup(self):
        cases = [{**self.case, "id": f"mock/{index}"} for index in range(221)]
        for index in range(217, 221):
            cases[index]["availability"] = "missing_download" if index % 2 else "missing_generated"
        manifest, report = self.root / "manifest.json", self.root / "report.json"
        manifest.write_text(json.dumps({"manifest_version": 1, "cases": cases}))
        self.group_present = True
        with contextlib.redirect_stdout(io.StringIO()):
            code = runner.main(["--manifest", str(manifest), "--checker", "fake-checker", "--report", str(report)])
        data = json.loads(report.read_text())
        self.assertEqual(code, 1)
        self.assertEqual(self.spawn.call_count, 1)
        self.assertEqual([r["id"] for r in data["results"]], [c["id"] for c in cases])
        self.assertEqual(data["summary"]["statuses"], {"execution_error": 1, "skipped": 216,
                                                     "missing_download": 2, "missing_generated": 2})
        self.assertFalse(data["summary"]["complete"])
        self.assertTrue(all(r["exit_code"] is None for r in data["results"][1:]))
        self.assertIn("cleanup unverified", data["results"][1]["reason"])
        self.assert_read_only()

    def test_verified_timeout_does_not_skip_following_cases(self):
        cases = [{**self.case, "id": f"mock/{i}"} for i in range(2)]
        manifest, report = self.root / "manifest.json", self.root / "report.json"
        manifest.write_text(json.dumps({"manifest_version": 1, "cases": cases}))
        children = [Child(waits=[subprocess.TimeoutExpired("case", 3), -9]), Child(waits=[2])]
        def launch(*args, **kwargs):
            self.child = children.pop(0)
            return self.launch(*args, **kwargs)
        self.spawn.side_effect = launch
        with contextlib.redirect_stdout(io.StringIO()):
            code = runner.main(["--manifest", str(manifest), "--checker", "fake-checker", "--report", str(report)])
        data = json.loads(report.read_text())
        self.assertEqual(code, 1)
        self.assertEqual([r["status"] for r in data["results"]], ["timeout", "declined"])
        self.assertEqual(self.spawn.call_count, 2)


if __name__ == "__main__":
    # Unexpected calls outside a test fixture cannot reach the OS either.
    with mock.patch.object(subprocess, "Popen", side_effect=AssertionError("unmocked launch")), \
         mock.patch.object(subprocess, "run", side_effect=AssertionError("unmocked subprocess.run")), \
         mock.patch.object(os, "kill", side_effect=AssertionError("unmocked signal/probe")), \
         mock.patch.object(os, "killpg", side_effect=AssertionError("unmocked group signal/probe")), \
         mock.patch.object(signal, "getsignal", side_effect=AssertionError("unmocked disposition read")), \
         mock.patch.object(signal, "signal", side_effect=AssertionError("handler mutation forbidden")), \
         mock.patch.object(threading, "Thread", side_effect=AssertionError("unmocked thread")):
        unittest.main(verbosity=2, failfast=True)
