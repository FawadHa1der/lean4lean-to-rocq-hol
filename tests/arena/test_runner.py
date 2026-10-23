"""Contract, integrity, and adversarial process tests for the independent runner."""

import argparse
import errno
import hashlib
import io
import json
import os
from pathlib import Path
import shlex
import signal
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest import mock

SCRIPTS = Path(__file__).resolve().parents[2] / "scripts"
sys.path.insert(0, str(SCRIPTS))
import test_arena as runner
import fetch_arena as fetch


class RunnerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.path = self.root / "input with spaces.ndjson"
        self.path.write_bytes(b'{"input":"no expected verdict"}\n')
        self.case = {"id": "case", "expected": "accept", "availability": "available",
                     "path": self.path.name, "sha256": runner.digest(self.path), "size": self.path.stat().st_size}

    def args(self, code="pass", **kwargs):
        args = argparse.Namespace(checker=shlex.join([sys.executable, "-c", code]), select=[], skip=[],
                                  timeout=None, default_timeout=2, input_mode="file", max_log_bytes=256)
        vars(args).update(kwargs)
        return args

    def run_case(self, code="pass", **kwargs):
        return runner.run_case(self.case, self.root, self.args(code, **kwargs))

    def run_cli(self, *arguments):
        # subprocess.run(timeout=...) can still wait unboundedly in cleanup.
        result = runner.run_process([sys.executable, str(SCRIPTS / "test_arena.py"), *arguments],
                                    self.path, 10, "env", 65536)
        self.assertFalse(result["timed_out"], result)
        self.assertTrue(result["cleanup_verified"], result)
        self.assertTrue(result["capture_complete"], result)
        return result

    def test_all_exit_codes_and_expected_combinations(self):
        for expected in ("accept", "reject", "either"):
            self.case["expected"] = expected
            for code in (0, 1, 2, 3, 17):
                with self.subTest(expected=expected, code=code):
                    result = self.run_case(f"raise SystemExit({code})")
                    self.assertEqual(result["exit_code"], code)
                    self.assertEqual(result["status"], runner.classify(code, expected))
        self.assertEqual(runner.classify(0, "reject"), "wrong_accept")
        self.assertEqual(runner.classify(1, "accept"), "wrong_reject")
        self.assertEqual(runner.classify(2, "reject"), "declined")
        self.assertEqual(runner.classify(3, "reject"), "fault")
        self.assertEqual(runner.classify(-9, "reject"), "fault")

    def test_filename_and_environment(self):
        result = self.run_case("import os,sys,pathlib; assert len(sys.argv)==2; assert sys.argv[1]==os.environ['IN']; assert pathlib.Path(sys.argv[1]).read_bytes()")
        self.assertEqual(result["status"], "correct_accept")

    def test_environment_only(self):
        result = self.run_case("import os,sys,pathlib; assert len(sys.argv)==1; assert pathlib.Path(os.environ['IN']).exists()", input_mode="env")
        self.assertEqual(result["status"], "correct_accept")

    def test_stdin(self):
        result = self.run_case("import os,sys,pathlib; assert len(sys.argv)==1; assert sys.stdin.buffer.read()==pathlib.Path(os.environ['IN']).read_bytes()", input_mode="stdin")
        self.assertEqual(result["status"], "correct_accept")

    def test_placeholder_is_not_shell_expansion(self):
        command = runner.make_command("checker --input '$IN' ';' touch", self.path, "file")
        self.assertEqual(command, ["checker", "--input", str(self.path), ";", "touch"])
        self.assertEqual(runner.make_command("checker '${IN}'", self.path, "env"), ["checker", str(self.path)])

    def test_timeout_is_not_decline(self):
        result = self.run_case("import time; time.sleep(60)", timeout=0.08)
        self.assertEqual(result["status"], "timeout")
        self.assertNotEqual(result["exit_code"], 2)
        self.assertLess(result["elapsed_seconds"], 2)

    def test_case_timeout_and_override(self):
        self.case["timeout_seconds"] = 0.05
        self.assertEqual(self.run_case("import time; time.sleep(0.2)")["status"], "timeout")
        self.assertEqual(self.run_case("import time; time.sleep(0.2)", timeout=2)["status"], "correct_accept")

    @unittest.skipUnless(os.name == "posix", "process-group handling is POSIX-specific")
    def test_surviving_group_after_parent_reap_is_readonly_failure(self):
        proc = self.fake_process(code=0)
        def surviving_group(pid, sig):
            self.assertEqual((pid, sig), (proc.pid, 0), "post-reap destructive signal")
        self.fake_group_signal.side_effect = surviving_group
        with mock.patch.object(runner.subprocess, "Popen", return_value=proc):
            result = self.run_case()
        self.assertEqual(result["status"], "execution_error")
        self.assertEqual(result["exit_code"], 0)
        self.assertFalse(result["cleanup_verified"])
        self.assertFalse(result["cleanup"]["process_group_absent"])
        self.fake_group_signal.assert_called_once_with(proc.pid, 0)
        proc.kill.assert_not_called()

    @unittest.skipUnless(os.name == "posix", "POSIX signals")
    def test_signal_is_fault(self):
        result = self.run_case("import os,signal; os.kill(os.getpid(),signal.SIGTERM)")
        self.assertEqual(result["status"], "fault")
        self.assertEqual(result["exit_code"], -15)

    def test_logs_are_bounded_and_binary_safe(self):
        result = self.run_case("import os; os.write(1,b'\\xff'*100000); os.write(2,b'e'*200000)")
        self.assertEqual(result["status"], "correct_accept")
        self.assertEqual(result["stdout_bytes"], 100000)
        self.assertEqual(result["stderr_bytes"], 200000)
        self.assertTrue(result["stdout_truncated"])
        self.assertEqual(len(result["stderr"]), 256)

    def test_missing_executable_is_execution_error(self):
        args = self.args()
        args.checker = str(self.root / "nonexistent")
        result = runner.run_case(self.case, self.root, args)
        self.assertEqual(result["status"], "execution_error")
        self.assertEqual(result["execution_errors"][0]["operation"], "spawn_process")
        self.assertIsNone(result["process_id"])
        self.assertFalse(result["group_stop_returned"])

    @unittest.skipUnless(os.name == "posix", "process-group handling is POSIX-specific")
    def test_cleanup_permission_error_preserves_reject_and_logs_but_is_not_pass(self):
        with mock.patch.object(runner.os, "killpg", side_effect=PermissionError(errno.EPERM, "injected")) as group_probe:
            result = self.run_case("import sys; print('observed'); print('diagnostic',file=sys.stderr); raise SystemExit(1)")
        self.assertEqual(result["status"], "execution_error")
        self.assertEqual(result["exit_code"], 1)
        self.assertEqual(result["verdict"], "reject")
        self.assertEqual(result["stdout"], "observed\n")
        self.assertEqual(result["stderr"], "diagnostic\n")
        self.assertTrue(result["capture_complete"])
        self.assertFalse(result["group_stop_returned"])
        error = result["execution_errors"][0]
        self.assertEqual(error["operation"], "process_group_absent")
        group_probe.assert_called_once_with(result["process_id"], 0)
        self.assertEqual(error["errno"], errno.EPERM)
        self.assertIn("PermissionError", error["traceback"])
        self.assertEqual(runner.summary([result])["failures"], 1)
        self.assertFalse(runner.summary([result])["complete"])

    def fake_process(self, *, waits=(), code=None):
        proc = mock.Mock(pid=123456789, returncode=code,
                         stdout=io.BytesIO(b"prefix"), stderr=io.BytesIO(b"detail"))
        outcomes = list(waits)
        def wait(timeout=None):
            self.assertIsNotNone(timeout, "unbounded wait")
            self.assertGreater(timeout, 0)
            result = outcomes.pop(0) if outcomes else (proc.returncode if proc.returncode is not None else 0)
            if isinstance(result, BaseException):
                raise result
            proc.returncode = result
            return result
        proc.wait.side_effect = wait
        proc.poll.side_effect = lambda: proc.returncode
        proc.kill.side_effect = lambda: self.assertIsNone(proc.returncode, "post-reap direct kill")
        def pid_absent(pid, sig):
            self.assertEqual((pid, sig), (proc.pid, 0))
            raise ProcessLookupError(errno.ESRCH, "fake absent PID")
        def group_signal(pid, sig):
            self.assertEqual(pid, proc.pid)
            if sig == 0:
                raise ProcessLookupError(errno.ESRCH, "fake absent group")
            self.assertEqual(sig, signal.SIGKILL)
            self.assertIsNone(proc.returncode, "post-reap group kill")
        self.enterContext(mock.patch.object(runner.os, "kill", side_effect=pid_absent))
        self.fake_group_signal = self.enterContext(mock.patch.object(runner.os, "killpg", side_effect=group_signal))
        self.enterContext(mock.patch.object(runner.signal, "getsignal", return_value=signal.SIG_DFL))
        self.enterContext(mock.patch.object(runner.signal, "signal", side_effect=AssertionError("handler mutation")))
        class Reader:
            def __init__(self, target, args, daemon):
                self.target, self.args, self.ident = target, args, None
            def start(self):
                self.ident = 1
                self.target(*self.args)
            def join(self, timeout=None):
                if timeout is None:
                    raise AssertionError("unbounded join")
            def is_alive(self):
                return False
        import threading
        self.enterContext(mock.patch.object(threading, "Thread", side_effect=Reader))
        return proc

    def deny_fake_group_kill(self, pid, sig):
        if sig == 0:
            raise ProcessLookupError(errno.ESRCH, "fake absent group")
        self.assertEqual(sig, signal.SIGKILL)
        raise PermissionError(errno.EPERM, "injected cleanup")

    def test_wait_and_cleanup_errors_both_survive(self):
        proc = self.fake_process(waits=[OSError(errno.EIO, "injected wait"), -9])
        self.fake_group_signal.side_effect = self.deny_fake_group_kill
        with mock.patch.object(runner.subprocess, "Popen", return_value=proc):
            result = self.run_case()
        self.assertEqual(result["status"], "execution_error")
        self.assertEqual([x["operation"] for x in result["execution_errors"]],
                         ["wait_process", "kill_process_group"])
        self.assertIn("injected wait", result["reason"])
        self.assertEqual(result["stdout"], "prefix")
        self.assertEqual(result["exit_code"], -9)
        self.assertFalse(result["group_stop_returned"])

    def test_timeout_cleanup_fault_is_not_timeout_only(self):
        proc = self.fake_process(waits=[subprocess.TimeoutExpired("fake", 1), -9])
        self.fake_group_signal.side_effect = self.deny_fake_group_kill
        with mock.patch.object(runner.subprocess, "Popen", return_value=proc):
            result = self.run_case()
        self.assertEqual(result["status"], "execution_error")
        self.assertTrue(result["timed_out"])
        self.assertFalse(result["group_stop_returned"])

    def test_reaping_fault_is_identified(self):
        proc = self.fake_process(waits=[subprocess.TimeoutExpired("fake", 1), OSError(errno.ECHILD, "injected reap")])
        with mock.patch.object(runner.subprocess, "Popen", return_value=proc):
            result = self.run_case()
        self.assertEqual(result["status"], "execution_error")
        self.assertIsNone(result["exit_code"])
        self.assertTrue(result["timed_out"])
        self.assertFalse(result["cleanup"]["reaped"])
        self.assertEqual(proc.wait.call_args_list, [mock.call(timeout=2), mock.call(timeout=runner.CLEANUP_REAP_SECONDS)])
        self.assertEqual(result["execution_errors"][0]["operation"], "reap_process")

    def test_reader_fault_cannot_be_silently_accepted(self):
        proc = self.fake_process()
        proc.returncode = 0
        proc.stdout = mock.Mock()
        proc.stdout.read.side_effect = [b"retained", OSError(errno.EIO, "injected read")]
        with mock.patch.object(runner.subprocess, "Popen", return_value=proc):
            result = self.run_case()
        self.assertEqual(result["status"], "execution_error")
        self.assertEqual(result["exit_code"], 0)
        self.assertEqual(result["stdout"], "retained")
        self.assertFalse(result["capture_complete"])
        self.assertTrue(result["group_stop_returned"])
        self.assertEqual(result["execution_errors"][0]["operation"], "read_stdout")

    def test_open_failure_has_no_claimed_checker_execution(self):
        path = mock.Mock()
        path.open.side_effect = PermissionError(errno.EACCES, "injected open")
        with self.assertRaises(runner.ProcessExecutionError) as caught:
            runner.run_process(["unused"], path, 1, "stdin", 256)
        evidence = caught.exception.evidence
        self.assertIsNone(evidence["exit_code"])
        self.assertIsNone(evidence["process_id"])
        self.assertEqual(evidence["execution_errors"][0]["operation"], "open_input")

    def test_interrupt_not_converted_to_checker_verdict(self):
        interrupt = KeyboardInterrupt()
        proc = self.fake_process(waits=[interrupt, -9])
        with mock.patch.object(runner.subprocess, "Popen", return_value=proc), \
             self.assertRaises(KeyboardInterrupt) as caught:
            self.run_case()
        self.assertEqual(proc.wait.call_count, 2)
        self.assertIs(caught.exception, interrupt)
        self.assertTrue(interrupt.arena_evidence["cleanup_verified"])

    def test_input_close_fault_preserves_successful_process_evidence(self):
        proc = self.fake_process()
        proc.returncode = 0
        path = mock.Mock()
        path.open.return_value.close.side_effect = OSError(errno.EIO, "injected close")
        with mock.patch.object(runner.subprocess, "Popen", return_value=proc), \
             self.assertRaises(runner.ProcessExecutionError) as caught:
            runner.run_process(["unused"], path, 1, "file", 256)
        evidence = caught.exception.evidence
        self.assertEqual(evidence["exit_code"], 0)
        self.assertTrue(evidence["group_stop_returned"])
        self.assertEqual(evidence["execution_errors"][0]["operation"], "close_input")

    def test_cleanup_wrapper_error_outside_observer_is_never_a_verdict(self):
        proc = self.fake_process()
        proc.returncode = 1
        self.case["expected"] = "reject"
        with mock.patch.object(runner.subprocess, "Popen", return_value=proc), \
             mock.patch.object(runner, "stop_group", side_effect=PermissionError(errno.EPERM, "wrapper fault")):
            result = self.run_case()
        self.assertEqual(result["status"], "execution_error")
        self.assertEqual(result["exit_code"], 1)
        self.assertFalse(result["group_stop_returned"])
        self.assertEqual(result["execution_errors"][0]["operation"], "stop_group")
        self.assertIn("wrapper fault", result["execution_errors"][0]["traceback"])

    def test_setup_error_outside_observer_is_retained(self):
        proc = self.fake_process()
        proc.returncode = 0
        import threading
        with mock.patch.object(runner.subprocess, "Popen", return_value=proc), \
             mock.patch.object(threading, "Thread", side_effect=OSError(errno.EIO, "thread construction")):
            result = self.run_case()
        self.assertEqual(result["status"], "execution_error")
        self.assertEqual(result["execution_errors"][0]["operation"], "process_setup_or_wait")
        self.assertTrue(result["group_stop_returned"])
        self.assertFalse(result["capture_complete"])
        self.assertTrue(proc.stdout.closed)
        self.assertTrue(proc.stderr.closed)

    def test_integrity_io_faults_preserve_stage_and_prior_exit(self):
        digest = runner.digest
        for post in (False, True):
            with self.subTest(post=post):
                calls = [digest(self.path), OSError(errno.EIO, "post hash")] if post else [OSError(errno.EACCES, "pre hash")]
                with mock.patch.object(runner, "digest", side_effect=calls):
                    result = self.run_case()
                self.assertEqual(result["status"], "execution_error")
                self.assertEqual(result["exit_code"], 0 if post else None)
                error = result["execution_errors"][0]
                self.assertEqual(error["operation"], "verify_input_after_execution" if post else "verify_input_before_execution")
                self.assertIn("hash", error["traceback"])

    def test_tampered_input_never_runs(self):
        self.path.write_bytes(b"changed")
        result = self.run_case("raise SystemExit(2)")
        self.assertEqual(result["status"], "input_error")
        self.assertIsNone(result["exit_code"])

    def test_input_mutation_invalidates_accept(self):
        result = self.run_case("import pathlib,sys; pathlib.Path(sys.argv[1]).write_text('changed')")
        self.assertEqual(result["exit_code"], 0)
        self.assertEqual(result["status"], "input_error")

    def test_input_deletion_invalidates_accept(self):
        result = self.run_case("import pathlib,sys; pathlib.Path(sys.argv[1]).unlink()")
        self.assertEqual(result["status"], "input_error")

    def test_command_fingerprint_tracks_explicit_script(self):
        script = self.root / "checker with spaces.py"
        script.write_text("pass\n")
        command = shlex.join([sys.executable, str(script), "$IN"])
        before = runner.checker_fingerprint(command)
        self.assertEqual([item["argument_index"] for item in before], [0, 1])
        self.assertEqual(before[1]["sha256"], runner.digest(script))
        script.write_text("raise SystemExit(2)\n")
        self.assertNotEqual(before, runner.checker_fingerprint(command))

    def test_mutating_checker_invalidates_run(self):
        manifest = self.manifest()
        script = self.root / "self-changing.py"
        script.write_text("from pathlib import Path\nPath(__file__).write_text('pass\\n')\n")
        report = self.root / "report.json"
        command = shlex.join([sys.executable, str(script)])
        p = self.run_cli("--manifest", str(manifest), "--checker", command, "--report", str(report))
        self.assertEqual(p["exit_code"], 1, p["stderr"])
        data = json.loads(report.read_text())
        self.assertEqual(data["results"][0]["status"], "correct_accept")
        self.assertFalse(data["integrity_verified"])
        self.assertFalse(data["summary"]["complete"])
        self.assertEqual(data["summary"]["integrity_failures"], 1)

    def test_absent_available_input_is_not_missing_download(self):
        self.path.unlink()
        self.assertEqual(self.run_case()["status"], "input_error")

    def test_declared_missing_distinct_from_skip(self):
        for status in ("missing_download", "missing_generated"):
            self.case["availability"] = status
            result = self.run_case()
            self.assertEqual(result["status"], status)
            self.assertIsNone(result["exit_code"])
        self.assertEqual(self.run_case(skip=[("case", "operator selected skip")])["status"], "skipped")

    def test_unselected_and_explicit_skips_remain_visible(self):
        result = self.run_case(select=["something-else"])
        self.assertEqual(result["status"], "skipped")
        self.case["skip_reason"] = "known unsupported feature; not a verdict"
        self.assertEqual(self.run_case()["reason"], self.case["skip_reason"])

    def test_either_is_not_completeness(self):
        self.case["expected"] = "either"
        result = self.run_case()
        self.assertEqual(result["status"], "acceptable_either")
        self.assertNotEqual(result["status"], "correct_accept")

    def test_summary_exposes_every_gap_and_failure(self):
        statuses = sorted(runner.FAILURES | runner.GAPS | {"correct_accept", "correct_reject", "acceptable_either"})
        s = runner.summary([{"status": status, "expected": "either", "exit_code": None} for status in statuses])
        self.assertEqual(s["total"], len(statuses))
        self.assertEqual(s["failures"], len(runner.FAILURES))
        self.assertEqual(s["gaps"], len(runner.GAPS))
        self.assertFalse(s["complete"])

    def manifest(self, cases=None, **kwargs):
        path = self.root / "manifest.json"
        data = {"manifest_version": 1, "cases": [self.case] if cases is None else cases, **kwargs}
        path.write_text(json.dumps(data))
        return path

    def test_manifest_validation(self):
        self.assertEqual(runner.load_manifest(self.manifest())["cases"][0]["id"], "case")
        for changes in ({"expected": "maybe"}, {"sha256": "0"}, {"size": True}, {"path": "../outside"},
                        {"timeout_seconds": 0}, {"timeout_seconds": float("inf")}, {"availability": "silently_skip"}):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                runner.load_manifest(self.manifest([{**self.case, **changes}]))
        with self.assertRaises(ValueError):
            runner.load_manifest(self.manifest([self.case, self.case]))
        with self.assertRaises(ValueError):
            runner.load_manifest(self.manifest([]))

    def test_symlink_escape(self):
        (self.root / "link").symlink_to(self.root.parent, target_is_directory=True)
        with self.assertRaises(ValueError):
            runner.relative_path(self.root, "link/escape")

    def test_cli_report_and_aggregate_exit_codes(self):
        manifest = self.manifest()
        report = self.root / "report.json"
        for code, aggregate in [(0, 0), (1, 1), (2, 2), (3, 1)]:
            command = shlex.join([sys.executable, "-c", f"raise SystemExit({code})"])
            p = self.run_cli("--manifest", str(manifest), "--checker", command, "--report", str(report))
            self.assertEqual(p["exit_code"], aggregate, p["stderr"])
            data = json.loads(report.read_text())
            self.assertEqual(data["results"][0]["exit_code"], code)
            self.assertIsNotNone(data["finished_at"])
            self.assertTrue(data["integrity_verified"])
            self.assertEqual(data["checker_artifacts_before"], data["checker_artifacts_after"])

    def test_no_expected_verdict_in_invocation(self):
        command = "import os,sys; assert not any('expected' in k.lower() for k in os.environ); assert len(sys.argv)==2"
        for expected in ("accept", "reject", "either"):
            self.case["expected"] = expected
            self.assertEqual(self.run_case(command)["exit_code"], 0)


class ArchiveTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.payload = b'{"meta":{}}\n'
        self.metadata = {"case": {"size": len(self.payload), "sha256": hashlib.sha256(self.payload).hexdigest(), "outcome": "accept"}}

    def archive(self, names, kind=tarfile.REGTYPE):
        path = self.root / "input.tar.gz"
        with tarfile.open(path, "w:gz") as tar:
            for name in names:
                member = tarfile.TarInfo(name)
                member.type = kind
                member.size = len(self.payload) if kind == tarfile.REGTYPE else 0
                if kind == tarfile.SYMTYPE:
                    member.linkname = "../../outside"
                tar.addfile(member, io.BytesIO(self.payload) if member.size else None)
        return path

    def test_import_verified_file(self):
        imported = fetch.extract_archive(self.archive(["good/case.ndjson"]), self.root, self.metadata)
        self.assertEqual(imported["case"]["origin"], "published_tarball")
        self.assertEqual((self.root / "corpus/case.ndjson").read_bytes(), self.payload)

    def test_archive_paths_and_links_rejected(self):
        for name in ("../escape.ndjson", "/good/case.ndjson", "good/../case.ndjson", "good\\case.ndjson", "other/case.ndjson"):
            with self.subTest(name=name), self.assertRaises(ValueError):
                fetch.extract_archive(self.archive([name]), self.root, self.metadata)
        for kind in (tarfile.SYMTYPE, tarfile.LNKTYPE, tarfile.DIRTYPE):
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                fetch.extract_archive(self.archive(["good/case.ndjson"], kind), self.root, self.metadata)

    def test_duplicate_unknown_and_wrong_bucket_rejected(self):
        for names in (["good/case.ndjson", "good/case.ndjson"], ["good/unknown.ndjson"], ["bad/case.ndjson"]):
            with self.subTest(names=names), self.assertRaises(ValueError):
                fetch.extract_archive(self.archive(names), self.root, self.metadata)

    def test_copy_failure_does_not_overwrite_or_leave_temporary_files(self):
        target = self.root / "target"
        target.write_bytes(b"preserve")
        for payload in (b"too small", b"X" * 100):
            with self.assertRaises(ValueError):
                fetch.verified_copy(io.BytesIO(payload), target, self.metadata["case"])
            self.assertEqual(target.read_bytes(), b"preserve")
            self.assertEqual(list(self.root.iterdir()), [target])


if __name__ == "__main__":
    unittest.main()
