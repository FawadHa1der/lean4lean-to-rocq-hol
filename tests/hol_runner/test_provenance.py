# Copyright (c) 2026 Fawad Haider. All rights reserved.
"""Dependency/publication tests; fake HOL emits transport readiness, not verdicts."""

import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import selectors
import signal
import stat
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('hol_runner', ROOT / 'scripts/hol-check.py')
RUNNER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RUNNER)

FAKE_HOL = r'''
import os
from pathlib import Path
import signal
import socket
import sys
import time

bootstrap = sys.stdin.buffer.read()
assert b'Topdirs.dir_load Format.std_formatter' in bootstrap
assert b'load_path := [Sys.getcwd()]' in bootstrap
assert os.environ['HOL_RUNNER_ROOT'] == os.getcwd()
assert 'HOL_ML_PATH' not in os.environ
change = os.environ.get('TEST_CHANGE')
if change:
    target = Path(change)
    target.write_bytes(target.read_bytes() + b'\n')
if os.environ.get('TEST_NEW_DEPENDENCY'):
    Path('hol/new.ml').write_text('let dependency = ();;\n')
    with Path('hol/environment.ml').open('a') as stream:
        stream.write('needs "hol/new.ml";;\n')
if os.environ.get('TEST_OCCUPY'):
    Path(os.environ['TEST_OCCUPY']).write_bytes(b'existing report')
if os.environ.get('TEST_ERROR'):
    print('Error: synthetic startup failure', flush=True)
    sys.exit(0)
with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as server:
    server.bind(os.environ['HOL_RUNNER_SOCKET'])
    os.chmod(os.environ['HOL_RUNNER_SOCKET'], 0o600)
    server.listen(1)
    print(os.environ['HOL_RUNNER_READY'] + ':' + str(os.getpid()), flush=True)
    while True:
        time.sleep(0.1)
'''


class SyntheticCleanupError(RuntimeError):
    def __init__(self, primary, errors):
        self.primary = primary
        self.errors = tuple(errors)
        super().__init__('synthetic supervisor cleanup failed; primary=' + repr(primary)
                         + '; cleanup=' + '; '.join(repr(error) for error in errors))


def finish_synthetic_supervisor(process, primary):
    """Single owner of this direct child; never signal a recorded READY PID."""
    errors = []
    if process.returncode is None:
        try:
            process.terminate()
        except BaseException as error:
            errors.append(error)
        try:
            process.communicate(timeout=8)
        except BaseException as error:
            errors.append(error)
        if process.returncode is None:
            try:
                process.kill()
            except BaseException as error:
                errors.append(error)
            try:
                # Wait only for the child, not EOF from inherited descendant pipes.
                process.wait(timeout=3)
            except BaseException as error:
                errors.append(error)
    if process.returncode is None:
        errors.append(RuntimeError('synthetic supervisor was not reaped within cleanup bounds'))
    for stream in (process.stdout, process.stderr):
        try:
            if stream is not None and not stream.closed:
                stream.close()
        except BaseException as error:
            errors.append(error)
    if errors:
        raise SyntheticCleanupError(primary, errors) from (primary if primary is not None else errors[0])


def run_synthetic_supervisor(argv, environment):
    # Avoid subprocess.run's implicit unbounded post-timeout wait on POSIX.
    process = subprocess.Popen(argv, env=environment,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    primary = None
    try:
        stdout, stderr = process.communicate(timeout=10)
        return subprocess.CompletedProcess(argv, process.returncode, stdout, stderr)
    except BaseException as error:
        primary = error
        raise
    finally:
        finish_synthetic_supervisor(process, primary)


class ProvenanceTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='hol-provenance-test-', dir='/private/tmp')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        for relative in RUNNER.SOURCE_ROOTS:
            self.put(relative, b'let source = ();;\n')
        self.put('hol/environment.ml', b'needs "hol/core.ml";;\n')
        self.put('hol/core.ml', b'needs "hol/leaf.ml";;\n')
        self.put('hol/leaf.ml', b'let leaf = ();;\n')
        for relative in RUNNER.BOOT_FILES:
            self.put(relative, b'fixture input\n')

    def put(self, relative, data):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        return path

    def snapshot(self):
        return RUNNER.project_snapshot(self.root)

    def arguments(self, output=None):
        return SimpleNamespace(case_timeout=5, provenance_output=output)

    def publish(self, before=None, output=None):
        directory = self.root / 'private-run'
        directory.mkdir(mode=0o700, exist_ok=True)
        return RUNNER.publish_provenance(
            self.root, self.snapshot() if before is None else before,
            str(directory), str(directory / 's'), 12345,
            self.arguments(output), '2026-09-29T00:00:00+00:00')

    def test_transitive_closure_and_hashes(self):
        snapshot = self.snapshot()
        entries = {entry['path']: entry for entry in snapshot['inputs']}
        self.assertEqual(set(entries), set(RUNNER.BOOT_FILES) | set(RUNNER.SOURCE_ROOTS)
                         | {'hol/core.ml', 'hol/leaf.ml'})
        for path, entry in entries.items():
            self.assertEqual(entry['sha256'], hashlib.sha256((self.root / path).read_bytes()).hexdigest())
        self.assertEqual(snapshot['literal_needs']['hol/core.ml'], ['hol/leaf.ml'])
        self.assertEqual(snapshot['bootstrap']['sha256'], hashlib.sha256(RUNNER.BOOTSTRAP).hexdigest())
        RUNNER.require_stable_startup(snapshot, self.snapshot())

    def test_proof_sources_loaded_before_disabling_hol_lexer(self):
        boundary = RUNNER.BOOTSTRAP.index(b'unset_jrh_lexer;;')
        for source in ('hol/environment.ml', 'hol/primitive_validation.ml', 'hol/text_validation.ml'):
            self.assertIn(source, RUNNER.SOURCE_ROOTS)
            self.assertLess(RUNNER.BOOTSTRAP.index(('needs "' + source + '"').encode()),
                            boundary)
        self.assertGreater(RUNNER.BOOTSTRAP.index(b'needs "frontend/hol_check.ml"'), boundary)

    def test_scanner_ignores_comments_literals_and_hol_terms(self):
        source = br'''(* needs "hol/absent.ml" (* nested *) "*)" *)
let message = "needs \"hol/absent.ml\"";;
let term = `needs "hol/absent.ml"`;;
let text = {tag|needs "hol/absent.ml"|tag};;
let c = '"';;
needs (* between tokens *) "hol/leaf.ml";;
needs "hol/leaf.ml";;
'''
        self.assertEqual(RUNNER.literal_needs(source), ['hol/leaf.ml'])

    def test_scanner_refuses_unsupported_or_escaping_loads(self):
        for source in (b'needs path;;', b'let loader = needs;;', b'needs ("hol/core.ml");;',
                       b'needs "../outside.ml";;', b'needs "/private/tmp/a.ml";;',
                       b'needs "hol/../core.ml";;', b'needs "hol/\\x61.ml";;',
                       b'X.needs "hol/core.ml";;', b'loadt "hol/core.ml";;',
                       b'#use "hol/core.ml";;', b'#load "untracked.cmo";;',
                       b'Topdirs.dir_load fmt path;;', b'load_path := [];;',
                       b'Dynlink.loadfile path;;', b'(* incomplete', b'`incomplete'):
            with self.subTest(source=source), self.assertRaises(ValueError):
                RUNNER.literal_needs(source)

    def test_cycle_is_bounded_missing_input_is_fault(self):
        self.put('hol/leaf.ml', b'needs "hol/environment.ml";;\n')
        self.assertEqual(set(self.snapshot()['literal_needs']),
                         set(RUNNER.SOURCE_ROOTS) | {'hol/core.ml', 'hol/leaf.ml'})
        (self.root / 'hol/leaf.ml').unlink()
        with self.assertRaises(OSError):
            self.snapshot()

    def test_project_symlinks_and_nonregular_inputs_refused(self):
        leaf = self.root / 'hol/leaf.ml'
        leaf.unlink()
        leaf.symlink_to(self.root / 'hol/core.ml')
        with self.assertRaises(OSError):
            self.snapshot()
        leaf.unlink()
        os.mkfifo(leaf)
        with self.assertRaises(ValueError):
            self.snapshot()
        leaf.unlink()
        moved = self.root / 'moved-hol'
        (self.root / 'hol').rename(moved)
        (self.root / 'hol').symlink_to(moved, target_is_directory=True)
        with self.assertRaises(ValueError):
            self.snapshot()

    def test_input_size_and_count_bounds(self):
        with mock.patch.object(RUNNER, 'MAX_INPUT_BYTES', 1), self.assertRaises(ValueError):
            self.snapshot()
        with mock.patch.object(RUNNER, 'MAX_INPUT_TOTAL', 1), self.assertRaises(ValueError):
            self.snapshot()
        with mock.patch.object(RUNNER, 'MAX_INPUT_FILES', 1), self.assertRaises(ValueError):
            self.snapshot()
        with mock.patch.object(RUNNER, 'MAX_SOURCE_BYTES', 1), self.assertRaises(ValueError):
            RUNNER.literal_needs(b'needs "hol/core.ml";;')

    def test_changed_source_bytecode_interfaces_and_graph_refused(self):
        for relative in ('hol/leaf.ml', 'build/frontend/wire.cmo', 'build/frontend/replay.cmo',
                         'build/frontend/hol_input.cmo', 'build/frontend/hol_input.cmi',
                         'scripts/toolchain-env.sh'):
            before = self.snapshot()
            self.put(relative, (self.root / relative).read_bytes() + b'changed')
            with self.subTest(relative=relative), self.assertRaisesRegex(ValueError, 'before READY'):
                RUNNER.require_stable_startup(before, self.snapshot())
        before = self.snapshot()
        self.put('hol/leaf.ml', b'needs "hol/new.ml";;\n')
        self.put('hol/new.ml', b'let new_input = ();;\n')
        with self.assertRaises(ValueError):
            self.publish(before)
        self.assertFalse((self.root / 'private-run/provenance.json').exists())

    def test_same_bytes_replaced_input_refused(self):
        before = self.snapshot()
        replacement = self.put('hol/replacement.ml', (self.root / 'hol/leaf.ml').read_bytes())
        replacement.replace(self.root / 'hol/leaf.ml')
        with self.assertRaises(ValueError):
            RUNNER.require_stable_startup(before, self.snapshot())

    def test_input_mutation_during_read_is_detected(self):
        original = os.fstat
        calls = 0

        def mutate_on_second_stat(fd):
            nonlocal calls
            calls += 1
            if calls == 2:
                self.put('hol/leaf.ml', b'changed while reading')
            return original(fd)

        with mock.patch.object(RUNNER.os, 'fstat', side_effect=mutate_on_second_stat):
            with self.assertRaisesRegex(ValueError, 'changed while hashing'):
                RUNNER.read_project_input(self.root, 'hol/leaf.ml', 'test-source')

    def test_manifest_scope_integrity_and_private_modes(self):
        output = self.root / 'persisted.json'
        result = self.publish(output=str(output))
        data = Path(result['provenance_path']).read_bytes()
        self.assertEqual(output.read_bytes(), data)
        self.assertEqual(result['provenance_sha256'], hashlib.sha256(data).hexdigest())
        for path in (output, Path(result['provenance_path'])):
            self.assertEqual(stat.S_IMODE(path.stat().st_mode), 0o600)
            RUNNER.verify_private_output(path, result['provenance_sha256'])
        manifest = json.loads(data)
        self.assertEqual(manifest['scope'], 'project-inputs-only')
        self.assertEqual(manifest['snapshot_sha256'], RUNNER.sha256(RUNNER.json_bytes(manifest['snapshot'])))
        self.assertEqual(manifest['startup']['before_snapshot_sha256'], manifest['snapshot_sha256'])
        self.assertEqual(manifest['startup']['ready_snapshot_sha256'], manifest['snapshot_sha256'])
        self.assertIn('dynamic libraries', ' '.join(manifest['limitations']))
        self.assertLess(len(data), RUNNER.MAX_PROVENANCE)
        output.write_bytes(data + b' ')
        with self.assertRaisesRegex(ValueError, 'integrity mismatch'):
            RUNNER.verify_private_output(output, result['provenance_sha256'])

    def test_no_overwrite_existing_file_symlink_or_public_run_directory(self):
        path = self.put('existing.json', b'keep')
        with self.assertRaises(ValueError):
            RUNNER.atomic_private_output(path, b'new')
        self.assertEqual(path.read_bytes(), b'keep')
        dangling = self.root / 'dangling.json'
        dangling.symlink_to(self.root / 'absent.json')
        with self.assertRaises(ValueError):
            RUNNER.atomic_private_output(dangling, b'new')
        (self.root / 'private-run').mkdir(mode=0o755)
        (self.root / 'private-run').chmod(0o755)
        with self.assertRaisesRegex(ValueError, '0700'):
            self.publish()

    def test_publication_is_complete_atomic_and_race_does_not_overwrite(self):
        destination = self.root / 'report.json'
        original_link = os.link
        payload = b'{"complete":true}\n'

        def check_complete(src, dst, **kwargs):
            self.assertFalse(destination.exists())
            self.assertEqual((destination.parent / src).read_bytes(), payload)
            self.assertEqual(stat.S_IMODE((destination.parent / src).stat().st_mode), 0o600)
            return original_link(src, dst, **kwargs)

        with mock.patch.object(RUNNER.os, 'link', side_effect=check_complete):
            RUNNER.atomic_private_output(destination, payload)
        self.assertEqual(destination.read_bytes(), payload)
        destination.unlink()

        def occupy(src, dst, **kwargs):
            destination.write_bytes(b'race winner')
            return original_link(src, dst, **kwargs)

        with mock.patch.object(RUNNER.os, 'link', side_effect=occupy), self.assertRaises(FileExistsError):
            RUNNER.atomic_private_output(destination, payload)
        self.assertEqual(destination.read_bytes(), b'race winner')
        self.assertEqual(list(self.root.glob('.hol-provenance-*')), [])

    def test_report_bounds_permissions_links_and_failed_write_cleanup(self):
        path = self.root / 'report.json'
        with mock.patch.object(RUNNER, 'MAX_PROVENANCE', 1), self.assertRaises(ValueError):
            RUNNER.atomic_private_output(path, b'too big')
        self.assertFalse(path.exists())
        with mock.patch.object(RUNNER.os, 'fsync', side_effect=OSError('disk fault')):
            with self.assertRaises(OSError):
                RUNNER.atomic_private_output(path, b'abc')
        self.assertFalse(path.exists())
        self.assertEqual(list(self.root.glob('.hol-provenance-*')), [])
        RUNNER.atomic_private_output(path, b'abc')
        path.chmod(0o644)
        with self.assertRaises(ValueError):
            RUNNER.verify_private_output(path, RUNNER.sha256(b'abc'))
        path.chmod(0o600)
        alias = self.root / 'alias.json'
        os.link(path, alias)
        with self.assertRaises(ValueError):
            RUNNER.verify_private_output(path, RUNNER.sha256(b'abc'))
        alias.unlink()
        alias.symlink_to(path)
        with self.assertRaises(OSError):
            RUNNER.verify_private_output(alias, RUNNER.sha256(b'abc'))
        linkdir = self.root / 'linkdir'
        linkdir.symlink_to(self.root, target_is_directory=True)
        with self.assertRaises(OSError):
            RUNNER.atomic_private_output(linkdir / 'new.json', b'new')

    def fake_environment(self, **extra):
        runner = self.put('scripts/hol-check.py', (ROOT / 'scripts/hol-check.py').read_bytes())
        for package in ('zarith', 'yojson'):
            self.put(f'libs/{package}/{package}.cma', b'fake external library')
        query = '#!' + sys.executable + '\nimport sys\nfrom pathlib import Path\nprint(Path(__file__).resolve().parents[1] / "libs" / sys.argv[-1])\n'
        self.put('bin/ocamlfind', query.encode()).chmod(0o700)
        self.put('bin/hol.sh', ('#!' + sys.executable + '\n' + FAKE_HOL).encode()).chmod(0o700)
        environment = {**os.environ, 'PATH': str(self.root / 'bin') + os.pathsep + os.environ['PATH'],
                       'PYTHONDONTWRITEBYTECODE': '1', 'HOL_ML_PATH': '/must/be/cleared', **extra}
        return runner, environment

    def test_existing_output_fails_before_dependency_queries(self):
        output = self.put('report.json', b'preserve')
        with mock.patch.object(RUNNER.subprocess, 'run') as query:
            with self.assertRaisesRegex(ValueError, 'already exists'):
                RUNNER.serve(['--provenance-output', str(output)])
            query.assert_not_called()
        self.assertEqual(output.read_bytes(), b'preserve')

    def test_client_arguments_and_all_four_codes_stay_unchanged(self):
        filename = str(self.root / 'quotes"; exit 0;;\ncase.ndjson')
        for code in range(4):
            frame = {'version': 1, 'code': code, 'message': 'synthetic transport test',
                     'kind': 'fault' if code == 3 else 'result'}
            connection = mock.MagicMock()
            connection.__enter__.return_value = connection
            connection.recv.return_value = json.dumps(frame).encode() + b'\n'
            with mock.patch.object(RUNNER, 'private_socket'), \
                    mock.patch.object(RUNNER.socket, 'socket', return_value=connection), \
                    mock.patch.object(RUNNER.sys, 'stderr', io.StringIO()):
                actual = RUNNER.client(['--socket', '/private/tmp/unused/s', '--timeout', '1', filename])
            self.assertEqual(actual, code)
            request = json.loads(connection.sendall.call_args.args[0])
            self.assertEqual(request, {'version': 1, 'path': filename, 'timeout_seconds': 1.0})

    def test_supervisor_mismatch_refuses_readiness_and_preserves_existing_output(self):
        scenarios = [dict(TEST_CHANGE=path) for path in
                     ('hol/leaf.ml', 'hol/text_validation.ml', 'build/frontend/wire.cmo', 'build/frontend/replay.cmo',
                      'build/frontend/hol_input.cmo', 'build/frontend/hol_input.cmi')]
        scenarios += [dict(TEST_NEW_DEPENDENCY='1'), dict(TEST_ERROR='1'),
                      dict(TEST_OCCUPY=str(self.root / 'occupied.json'))]
        for number, scenario in enumerate(scenarios):
            runner, environment = self.fake_environment(**scenario)
            output = self.root / ('occupied.json' if 'TEST_OCCUPY' in scenario else f'failed-{number}.json')
            result = run_synthetic_supervisor(
                [sys.executable, str(runner), '--serve', '--startup-timeout', '5',
                 '--provenance-output', str(output)], environment)
            with self.subTest(scenario=scenario):
                self.assertEqual(result.returncode, 3, result.stderr)
                self.assertEqual(result.stdout, b'')
                if 'TEST_OCCUPY' in scenario:
                    self.assertEqual(output.read_bytes(), b'existing report')
                    self.assertIn(b'already exists', result.stderr)
                else:
                    self.assertFalse(output.exists())
                    self.assertIn(b'Error: synthetic startup failure' if 'TEST_ERROR' in scenario
                                  else b'startup provenance changed before READY', result.stderr)

    def test_supervisor_ready_provenance_and_graceful_cleanup(self):
        runner, environment = self.fake_environment()
        output = self.root / 'ready.json'
        process = subprocess.Popen([sys.executable, str(runner), '--serve', '--case-timeout', '5',
                                    '--startup-timeout', '5', '--provenance-output', str(output)],
                                   env=environment, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        primary = None
        try:
            with selectors.DefaultSelector() as selector:
                selector.register(process.stdout, selectors.EVENT_READ)
                self.assertTrue(selector.select(8), 'supervisor did not become ready')
                line = process.stdout.readline()
            if not line:
                unused_stdout, stderr = process.communicate(timeout=8)
                self.fail('supervisor failed before readiness: ' + stderr.decode(errors='replace'))
            record = json.loads(line)
            self.assertEqual(record['supervisor_pid'], process.pid)
            self.assertEqual(record['case_timeout_seconds'], 5)
            RUNNER.private_socket(record['socket'])
            RUNNER.verify_private_output(record['provenance_path'], record['provenance_sha256'])
            self.assertEqual(Path(record['provenance_path']).read_bytes(), output.read_bytes())
            manifest = json.loads(output.read_bytes())
            hol_pid = manifest['startup']['hol_pid']
            process.send_signal(signal.SIGTERM)
            stdout, stderr = process.communicate(timeout=8)
            self.assertEqual(process.returncode, 0, stderr)
            self.assertEqual(stdout, b'')
            self.assertFalse(Path(record['socket']).parent.exists())
            self.assertTrue(output.exists())
            with self.assertRaises(ProcessLookupError):
                os.kill(hol_pid, 0)
        except BaseException as error:
            primary = error
            raise
        finally:
            finish_synthetic_supervisor(process, primary)


if __name__ == '__main__':
    unittest.main()
