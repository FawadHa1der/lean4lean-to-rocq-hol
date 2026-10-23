"""Offline adapter controls. Shell helpers are not native HOL evidence."""
import builtins
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
import unittest
from unittest import mock

import early_observers
import early_variants as early
import run

SUITE = Path(__file__).resolve().parent
PROJECT = SUITE.parents[1]
SPEC = early.spec(SUITE)


def copy_file(source, target):
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, target)


def populate(snapshot, shell='printf "EARLY_PASS typed 27\\n"\n'):
    snapshot.mkdir(parents=True, exist_ok=True)
    copy_file(PROJECT / 'hol/core.ml', snapshot / 'hol/core.ml')
    for name in ('early-pins.json', 'early_variants.py', 'early_observers.py', 'run.py'):
        copy_file(SUITE / name, snapshot / 'tests/hol_composition' / name)
    for relative in SPEC['drivers']:
        copy_file(SUITE / 'drivers' / relative, snapshot / relative)
    for entry in SPEC['historical_cores'].values():
        copy_file(SUITE / 'data' / entry['path'], snapshot / entry['path'])
    (snapshot / 'scripts').mkdir(exist_ok=True)
    (snapshot / 'scripts/private-hol.sh').write_text(shell)


def acquisition_fixture(source_root, destination):
    """Copy named acquisition inputs only; never inherit a real toolchain/tree."""
    if destination.exists() or destination.is_symlink():
        raise ValueError('Acquisition fixture destination must be new')
    suite = Path('tests/hol_composition')
    data = early.spec(source_root / suite)
    manifest = json.loads((source_root / suite / 'fixture-pins.json').read_text())
    fixture_pins = {'data/' + entry['path']: entry['sha256']
                    for entry in data['historical_cores'].values()}
    fixture_pins['data/arena/corpus/perf/irrelevance-before-evaluation.ndjson'] = \
        '8cc3996fb088522e56c3670b0bd3b2397ee7b5a81c7fdc634c69a5f052e02e7f'
    entries = []
    for relative, pin in fixture_pins.items():
        matches = [entry for entry in manifest['entries'] if entry['path'] == relative]
        if len(matches) != 1 or matches[0]['sha256'] != pin:
            raise ValueError('Acquisition fixture pin mismatch: ' + relative)
        entries.append(matches[0])
    files = {Path('hol/core.ml'), Path('scripts/toolchain-env.sh'), Path('scripts/toolchain-exec.sh')}
    files.update(Path('frontend') / (name + '.ml') for name in ('wire', 'replay', 'hol_input'))
    files.update(Path('build/frontend') / (name + '.' + ext)
                 for name in ('wire', 'replay', 'hol_input') for ext in ('cmo', 'cmi'))
    files.update(suite / name for name in ('run.py', 'early_variants.py', 'early_observers.py',
                 'early-pins.json', 'native.sh', 'reference_environment_rules.ml',
                 'reference_indexed_environment_rules.ml'))
    files.update(suite / 'drivers' / name for name in data['drivers'])
    files.update(suite / name for name in fixture_pins)
    destination.mkdir(parents=True)
    copied = {}
    for relative in sorted(files):
        source = source_root / relative
        if any((source_root / part).is_symlink() for part in (relative, *relative.parents)):
            raise ValueError('Symlinked required acquisition input: ' + str(relative))
        if not source.is_file():
            raise ValueError('Missing required acquisition input: ' + str(relative))
        before = run.digest(source)
        copy_file(source, destination / relative)
        if run.digest(source) != before or run.digest(destination / relative) != before:
            raise ValueError('Acquisition input changed: ' + str(relative))
        copied[str(relative)] = before
    for entry in entries:
        path = destination / suite / entry['path']
        if run.digest(path) != entry['sha256'] or path.stat().st_size != entry['bytes']:
            raise ValueError('Acquisition fixture content changed: ' + entry['path'])
    (destination / suite / 'fixture-pins.json').write_text(
        json.dumps(dict(manifest, entries=entries), indent=2) + '\n')
    (destination / 'toolchain').mkdir()
    return copied


@contextlib.contextmanager
def forbid_unrelated_access(source_root, forbidden):
    """Tripwires, not a replacement copier: permitted operations stay real."""
    trace = {'blocked': [], 'copies': []}
    source_prefix = os.path.abspath(source_root)
    forbidden_prefixes = [os.path.abspath(path) for path in forbidden]

    def inside(path, prefix):
        return path == prefix or path.startswith(prefix + os.sep)

    def check(operation, path, scan=False):
        if isinstance(path, (str, bytes, os.PathLike)):
            normalized = os.path.abspath(os.fsdecode(path))
            if any(inside(normalized, prefix) for prefix in forbidden_prefixes) or (
                    scan and inside(normalized, source_prefix)):
                trace['blocked'].append((operation, normalized))
                raise AssertionError('Forbidden unrelated access: ' + operation + ': ' + normalized)

    def guarded(operation, original, scan=False):
        def invoke(path, *args, **kwargs):
            check(operation, path, scan)
            return original(path, *args, **kwargs)
        return invoke

    original_copy = shutil.copyfile
    def copy_one(source, target, *args, **kwargs):
        check('copyfile', source)
        trace['copies'].append(str(source))
        return original_copy(source, target, *args, **kwargs)

    def no_copytree(*args, **kwargs):
        trace['blocked'].append(('copytree', str(args[0])))
        raise AssertionError('Whole-tree copying forbidden in acquisition fixture')

    with contextlib.ExitStack() as stack:
        for owner, name in ((builtins, 'open'), (io, 'open'), (os, 'open'),
                            (os, 'stat'), (os, 'lstat'), (os, 'scandir')):
            stack.enter_context(mock.patch.object(owner, name,
                side_effect=guarded(name, getattr(owner, name), name == 'scandir')))
        stack.enter_context(mock.patch.object(shutil, 'copyfile', side_effect=copy_one))
        stack.enter_context(mock.patch.object(shutil, 'copytree', side_effect=no_copytree))
        yield trace


class RegistrationTests(unittest.TestCase):
    def test_original_124_jobs_exactly_preserved(self):
        expected = json.loads((SUITE / 'reference_early_jobs.json').read_text())
        actual = run.jobs()
        self.assertEqual({tag: actual[tag] for tag in expected}, expected)
        self.assertEqual(len(expected), 124)
        self.assertEqual(len(actual), 138)

    def test_exact_fourteen_registrations_and_caps(self):
        additional = early.jobs()
        self.assertEqual(len(additional), 14)
        for tag, job in additional.items():
            self.assertEqual({k: v for k, v in job.items() if k != 'early_variant'}, SPEC['groups'][tag]['job'])
            self.assertEqual(job['early_variant'], tag)
            self.assertEqual(job['limit'], 180)
            self.assertEqual(job['options'], {})

    def test_registration_collision_refused(self):
        with mock.patch.object(early, 'jobs', return_value={'bool-general': {}}):
            with self.assertRaises(ValueError):
                run.jobs()

    def test_historical_controls_not_candidate_passes(self):
        controls = [e for e in SPEC['groups'].values() if e['historical_core_control']]
        candidate = [e for e in SPEC['groups'].values() if not e['historical_core_control']]
        self.assertEqual((len(controls), sum(e['assertions'] for e in controls)), (4, 61))
        self.assertEqual((len(candidate), sum(e['assertions'] for e in candidate)), (10, 158))

    def test_exact_tested_input_bytes_all_fourteen(self):
        import hashlib
        for entry in SPEC['groups'].values():
            source = entry['job']['source'] + 'exit 0;;\n'
            self.assertEqual(hashlib.sha256(source.encode()).hexdigest(), entry['input_sha256'])

    def test_seven_unchanged_drivers(self):
        self.assertEqual(len(SPEC['drivers']), 7)
        for name, pin in SPEC['drivers'].items():
            self.assertEqual(run.digest(SUITE / 'drivers' / name), pin)

    def test_historical_and_full_selected_fixture_pins(self):
        pins = run.verify_fixtures(SUITE)
        for entry in SPEC['historical_cores'].values():
            self.assertEqual(pins['data/' + entry['path']], entry['sha256'])
        selected = 'data/arena/corpus/perf/irrelevance-before-evaluation.ndjson'
        self.assertEqual(pins[selected], '8cc3996fb088522e56c3670b0bd3b2397ee7b5a81c7fdc634c69a5f052e02e7f')
        self.assertEqual((SUITE / selected).stat().st_size, 17877)
        self.assertEqual(len((SUITE / selected).read_bytes().splitlines()), 388)

    def test_observer_functions_preserve_pinned_transforms(self):
        self.assertEqual(run.digest(SUITE / 'early_observers.py'), early.OBSERVER_SHA256)
        core = (run.ROOT / 'hol/core.ml').read_text()
        for transform in (early_observers.observed, early_observers.schedule_observed):
            anchor = '  type budget = { mutable remaining : int }'
            for broken in (core.replace(anchor, '', 1), core.replace(anchor, anchor + '\n' + anchor, 1)):
                with self.assertRaises(ValueError):
                    transform(broken)

    def test_exact_early_markers_not_source_echo_or_error(self):
        for entry in SPEC['groups'].values():
            marker = entry['job']['markers'][0]
            expected = [marker]
            self.assertTrue(run.inspect_log('# ' + marker + '\n', expected)[2])
            for bad in ('', marker + '\n' + marker + '\n', 'print_endline "' + marker + '";;\n',
                        marker + '\nException: Failure "bad"\n', marker + '0\n'):
                self.assertFalse(run.inspect_log(bad, expected)[2])


class SnapshotFixture(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.snapshot = self.root / 'snapshot'
        populate(self.snapshot)
        self.report = self.root / 'report'
        self.report.mkdir()
        self.frozen = early.tree_pins(self.snapshot)

    def tearDown(self):
        self.temp.cleanup()

    def prepare(self, tag='early-typed'):
        return early.prepare(self.snapshot, self.report, tag, run.jobs()[tag], self.frozen)

    def refusal(self, tag='early-typed', job=None, frozen=True):
        with mock.patch.object(run.subprocess, 'Popen') as launch:
            result = run.run_job(self.snapshot, self.report, tag, job or run.jobs()[tag],
                                 self.frozen if frozen else None)
            launch.assert_not_called()
        self.assertFalse(result['passed'])
        self.assertFalse(result['launched'])
        self.assertIsNone(result['reaped'])
        self.assertEqual(json.loads((self.report / (tag + '.json')).read_text()), result)
        return result


class SnapshotTests(SnapshotFixture):
    def test_all_fourteen_derived_pins_and_production_isolation(self):
        for tag, entry in SPEC['groups'].items():
            context = self.prepare(tag)
            self.assertEqual(run.digest(context['derived'] / 'hol/core.ml'), entry['private_tested_loaded_core_sha256'])
            self.assertEqual(context['provenance']['category'],
                             'historical_core_control' if entry['historical_core_control'] else 'candidate_test')
            self.assertNotEqual((context['derived'] / 'hol/core.ml').stat().st_ino,
                                (self.snapshot / 'hol/core.ml').stat().st_ino)
            early.check_ready(context)
            self.assertTrue(early.postflight(context)['passed'])
        self.assertEqual(early.tree_pins(self.snapshot), self.frozen)
        self.assertEqual(len(list((self.report / 'early-snapshots').iterdir())), 14)

    def test_no_live_origin_reads_after_freeze(self):
        original = early.spec
        def local_only(suite=None):
            self.assertEqual(suite, self.snapshot / 'tests/hol_composition')
            return original(suite)
        job = run.jobs()['early-typed']
        with mock.patch.object(early, 'spec', side_effect=local_only):
            context = early.prepare(self.snapshot, self.report, 'early-typed', job, self.frozen)
        self.assertTrue(early.postflight(context)['passed'])

    def test_missing_acquisition_pins_refused(self):
        self.refusal(frozen=False)

    def test_drift_since_acquisition_refused(self):
        (self.snapshot / 'extra.ml').write_text('changed')
        self.refusal()

    def test_unreviewed_production_core_refused_even_if_frozen(self):
        (self.snapshot / 'hol/core.ml').write_text('changed')
        self.frozen = early.tree_pins(self.snapshot)
        self.refusal()

    def test_unreviewed_historical_core_refused(self):
        path = self.snapshot / SPEC['historical_cores']['baseline']['path']
        path.write_text('changed')
        self.frozen = early.tree_pins(self.snapshot)
        self.refusal('early-observer-baseline')

    def test_missing_driver_refused(self):
        (self.snapshot / 'tests/common.ml').unlink()
        self.frozen = early.tree_pins(self.snapshot)
        self.refusal()

    def test_modified_driver_refused(self):
        (self.snapshot / 'tests/common.ml').write_text('changed')
        self.frozen = early.tree_pins(self.snapshot)
        self.refusal()

    def test_registry_pin_refused(self):
        (self.snapshot / 'tests/hol_composition/early-pins.json').write_text('{}')
        self.frozen = early.tree_pins(self.snapshot)
        self.refusal()

    def test_adapter_pin_refused(self):
        (self.snapshot / 'tests/hol_composition/early_variants.py').write_text('changed')
        self.frozen = early.tree_pins(self.snapshot)
        self.refusal()

    def test_observer_pin_refused(self):
        (self.snapshot / 'tests/hol_composition/early_observers.py').write_text('changed')
        self.frozen = early.tree_pins(self.snapshot)
        self.refusal('early-observer-candidate')

    def test_altered_source_marker_options_and_cap_refused(self):
        for field, value in [('source', 'exit 0;;\n'), ('markers', ['fake']),
                             ('options', {'TRUST': 'yes'}), ('limit', 181),
                             ('early_variant', 'early-observer-baseline')]:
            job = dict(run.jobs()['early-typed'], **{field: value})
            self.refusal(job=job)

    def test_unknown_group_refused(self):
        self.refusal('early-unknown', run.jobs()['early-typed'])

    def test_instrumentation_anchor_exception_never_launches(self):
        with mock.patch.object(early_observers, 'observed', side_effect=ValueError('anchor count')):
            result = self.refusal('early-observer-candidate')
        self.assertIn('anchor count', result['error'])

    def test_wrong_observer_output_never_launches(self):
        with mock.patch.object(early_observers, 'observed', side_effect=lambda source: source):
            result = self.refusal('early-observer-candidate')
        self.assertIn('Observer output', result['error'])

    def test_mutation_during_copy_never_launches(self):
        original = shutil.copytree
        def mutate(src, dst, *args, **kwargs):
            result = original(src, dst, *args, **kwargs)
            if Path(src) == self.snapshot:
                (src / 'hol/core.ml').write_text('changed during copy')
            return result
        with mock.patch.object(early.shutil, 'copytree', side_effect=mutate):
            self.refusal()

    def test_mutation_between_prepare_and_launch_never_launches(self):
        original = early.prepare
        def mutate(*args):
            context = original(*args)
            (context['derived'] / 'hol/core.ml').write_text('changed')
            return context
        with mock.patch.object(early, 'prepare', side_effect=mutate):
            result = self.refusal()
        self.assertEqual(result['stage'], 'prelaunch')

    def test_shared_mutation_before_launch_refused(self):
        original = early.prepare
        def mutate(*args):
            context = original(*args)
            (self.snapshot / 'hol/core.ml').write_text('changed')
            return context
        with mock.patch.object(early, 'prepare', side_effect=mutate):
            self.refusal()

    def test_provenance_mutation_before_launch_refused(self):
        original = early.prepare
        def mutate(*args):
            context = original(*args)
            context['provenance_path'].write_text('changed')
            return context
        with mock.patch.object(early, 'prepare', side_effect=mutate):
            self.refusal()

    def test_incorrect_input_pin_before_launch_refused(self):
        original = early.prepare
        def mutate(*args):
            context = original(*args)
            context['entry']['input_sha256'] = '0' * 64
            return context
        with mock.patch.object(early, 'prepare', side_effect=mutate):
            result = self.refusal()
        self.assertIn('Early input differs', result['error'])

    def test_partial_copy_failure_is_retained_without_launch(self):
        def fail_copy(src, dst, **kwargs):
            dst.mkdir(parents=True)
            (dst / 'partial').write_text('retained')
            raise OSError('simulated copy failure')
        with mock.patch.object(early.shutil, 'copytree', side_effect=fail_copy):
            result = self.refusal()
        self.assertIn('simulated copy failure', result['error'])
        self.assertEqual((self.report / 'early-snapshots/early-typed/partial').read_text(), 'retained')

    def test_derived_target_collision_refused_without_replacement(self):
        target = self.report / 'early-snapshots/early-typed'
        target.mkdir(parents=True)
        (target / 'keep').write_text('preserve')
        self.refusal()
        self.assertEqual((target / 'keep').read_text(), 'preserve')

    def test_source_symlink_refused(self):
        (self.snapshot / 'escape').symlink_to(self.root)
        self.refusal()

    def test_absolute_toolchain_link_preserved_and_change_detected(self):
        runtime = self.root / 'runtime'
        runtime.mkdir()
        (self.snapshot / 'toolchain').symlink_to(runtime)
        self.frozen = early.tree_pins(self.snapshot)
        context = self.prepare()
        self.assertEqual((context['derived'] / 'toolchain').resolve(), runtime.resolve())
        (context['derived'] / 'toolchain').unlink()
        (context['derived'] / 'toolchain').symlink_to(self.root)
        self.assertFalse(early.postflight(context)['passed'])

    def test_relative_toolchain_link_refused(self):
        (self.snapshot / 'toolchain').symlink_to('../')
        self.refusal()

    def test_no_production_hooks(self):
        core = (self.snapshot / 'hol/core.ml').read_text()
        self.assertNotIn('test_early_observer', core)
        self.assertNotIn('test_schedule_', core)


class ProcessTests(SnapshotFixture):
    def attempt(self, shell=None, env=None):
        if shell is not None:
            (self.snapshot / 'scripts/private-hol.sh').write_text(shell)
            self.frozen = early.tree_pins(self.snapshot)
        with mock.patch.dict(os.environ, env or {}):
            result = run.run_job(self.snapshot, self.report, 'early-typed',
                                 run.jobs()['early-typed'], self.frozen)
        self.assertEqual(json.loads((self.report / 'early-typed.json').read_text()), result)
        return result

    def test_success_reaps_and_keeps_exact_pins_and_inputs(self):
        result = self.attempt()
        self.assertTrue(result['passed'])
        self.assertTrue(result['reaped'])
        self.assertTrue(result['process_group_absent'])
        self.assertTrue(result['early_postflight']['passed'])
        self.assertEqual(result['limit_seconds'], 180)
        self.assertEqual(result['input_sha256'], SPEC['groups']['early-typed']['input_sha256'])
        self.assertEqual(result['early']['category'], 'candidate_test')

    def test_nonzero_after_marker_is_failure(self):
        result = self.attempt('printf "EARLY_PASS typed 27\\n"\nexit 7\n')
        self.assertFalse(result['passed'])
        self.assertEqual(result['returncode'], 7)
        self.assertTrue(result['reaped'] and result['process_group_absent'])

    def test_missing_marker_is_failure(self):
        self.assertFalse(self.attempt('exit 0\n')['passed'])

    def test_hol_style_error_after_marker_is_failure(self):
        result = self.attempt('printf "EARLY_PASS typed 27\\nException: simulated\\n"\n')
        self.assertFalse(result['passed'])

    def test_derived_mutation_is_failure(self):
        result = self.attempt('printf "EARLY_PASS typed 27\\n"\nprintf changed > hol/core.ml\n')
        self.assertFalse(result['passed'])
        self.assertFalse(result['early_postflight']['derived_unchanged'])
        self.assertTrue(result['early_postflight']['shared_unchanged'])
        self.assertEqual(result['early_postflight']['derived_after_pins']['files']['hol/core.ml'],
                         run.digest(self.report / 'early-snapshots/early-typed/hol/core.ml'))

    def test_shared_mutation_is_failure(self):
        result = self.attempt('printf "EARLY_PASS typed 27\\n"\nprintf changed > "$SHARED/hol/core.ml"\n',
                              {'SHARED': str(self.snapshot)})
        self.assertFalse(result['passed'])
        self.assertFalse(result['early_postflight']['shared_unchanged'])

    def test_provenance_mutation_is_failure(self):
        result = self.attempt('printf "EARLY_PASS typed 27\\n"\nprintf changed > "$REPORT/early-typed.provenance.json"\n',
                              {'REPORT': str(self.report)})
        self.assertFalse(result['passed'])
        self.assertFalse(result['early_postflight']['provenance_unchanged'])

    def test_prepared_input_deletion_keeps_cleanup_evidence(self):
        result = self.attempt('printf "EARLY_PASS typed 27\\n"\nrm "$REPORT/early-typed.prepared-input.ml"\n',
                              {'REPORT': str(self.report)})
        self.assertFalse(result['passed'])
        self.assertTrue(result['reaped'] and result['process_group_absent'])
        self.assertIsInstance(result['pid'], int)

    def test_popen_failure_is_not_success_or_cleanup_claim(self):
        with mock.patch.object(run.subprocess, 'Popen', side_effect=OSError('simulated launch failure')):
            result = self.attempt()
        self.assertFalse(result['passed'])
        self.assertIsNone(result['reaped'])
        self.assertIn('simulated launch failure', result['error'])

    def test_timeout_kills_and_reaps_without_changing_registered_cap(self):
        original = subprocess.Popen
        def short_test_helper(*args, **kwargs):
            process = original(*args, **kwargs)
            communicate = process.communicate
            def bounded(input=None, timeout=None):
                if timeout is not None:
                    self.assertEqual(timeout, 180)
                    timeout = 0.05
                return communicate(input, timeout)
            process.communicate = bounded
            return process
        with mock.patch.object(run.subprocess, 'Popen', side_effect=short_test_helper):
            result = self.attempt('exec sleep 10\n')
        self.assertFalse(result['passed'])
        self.assertTrue(result['timed_out'] and result['reaped'] and result['process_group_absent'])
        self.assertEqual(result['limit_seconds'], 180)

    def test_residual_group_flag_refuses_pass(self):
        original = os.killpg
        def pretend_residual(pid, sig):
            if sig == 0:
                return None
            return original(pid, sig)
        with mock.patch.object(run.os, 'killpg', side_effect=pretend_residual):
            result = self.attempt()
        self.assertFalse(result['passed'])
        self.assertFalse(result['process_group_absent'])

    def test_old_job_stays_on_shared_snapshot(self):
        job = {'source': '', 'markers': ['EARLY_PASS typed 27'], 'limit': 2, 'options': {}}
        with mock.patch.object(early, 'prepare') as prepare:
            result = run.run_job(self.snapshot, self.report, 'old-control', job)
            prepare.assert_not_called()
        self.assertTrue(result['passed'])
        self.assertFalse((self.report / 'early-snapshots').exists())

    def test_main_stops_on_first_preparation_failure_and_records_unexecuted(self):
        selected = ['early-typed', 'early-context', 'early-guards']
        project = self.root / 'project'
        def acquire(destination):
            populate(destination)
            (destination / 'hol/core.ml').write_text('unreviewed source')
            return {}
        with mock.patch.object(run, 'ROOT', project), \
             mock.patch.object(run, 'prepare_snapshot', side_effect=acquire), \
             mock.patch.object(sys, 'argv', ['run.py', *selected]), \
             mock.patch.object(run.subprocess, 'Popen') as launch:
            self.assertEqual(run.main(), 1)
            launch.assert_not_called()
        report = next((project / 'build/reports').iterdir())
        summary = json.loads((report / 'summary.json').read_text())
        self.assertFalse(summary['complete'])
        self.assertEqual(summary['unexecuted'], selected[1:])
        self.assertEqual(summary['results'], [{'tag': selected[0], 'passed': False}])

    def test_main_summary_explicitly_labels_historical_control(self):
        tag = 'early-fuel-baseline'
        project = self.root / 'project'
        def acquire(destination):
            populate(destination, 'printf "EARLY_PASS fuel-baseline 13\\n"\n')
            return {}
        with mock.patch.object(run, 'ROOT', project), \
             mock.patch.object(run, 'prepare_snapshot', side_effect=acquire), \
             mock.patch.object(sys, 'argv', ['run.py', tag]):
            self.assertEqual(run.main(), 0)
        report = next((project / 'build/reports').iterdir())
        summary = json.loads((report / 'summary.json').read_text())
        self.assertEqual(summary['results'], [{'tag': tag, 'passed': True,
            'category': 'historical_core_control', 'expected_assertions': 13}])
        detail = json.loads((report / (tag + '.json')).read_text())
        self.assertNotEqual(detail['early']['production_core_sha256'], detail['early']['loaded_test_core_sha256'])


class AcquisitionTests(unittest.TestCase):
    def test_real_snapshot_wiring_offline(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            project = root / 'project'
            acquisition_fixture(run.ROOT, project)
            module_spec = importlib.util.spec_from_file_location('early_test_copied_run', project / 'tests/hol_composition/run.py')
            module = importlib.util.module_from_spec(module_spec)
            module_spec.loader.exec_module(module)
            snapshot = root / 'snapshot'
            snapshot.mkdir()
            with mock.patch.object(subprocess, 'Popen') as launch:
                origins = module.prepare_snapshot(snapshot)
                launch.assert_not_called()
            for name in ('early_variants.py', 'early_observers.py', 'early-pins.json'):
                relative = 'tests/hol_composition/' + name
                self.assertEqual(run.digest(snapshot / relative), origins[relative])
            for relative, pin in SPEC['drivers'].items():
                self.assertEqual(run.digest(snapshot / relative), pin)
            for entry in SPEC['historical_cores'].values():
                self.assertEqual(run.digest(snapshot / entry['path']), entry['sha256'])
            self.assertEqual(run.digest(snapshot / 'hol/core.ml'), SPEC['production_core_sha256'])
            self.assertEqual(early.tree_pins(snapshot)['symlinks']['toolchain']['resolved'], str((project / 'toolchain').resolve()))


class BoundedAcquisitionTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.source = self.root / 'source'
        acquisition_fixture(PROJECT, self.source)
        self.destination = self.root / 'fixture'

    def tearDown(self):
        self.temp.cleanup()

    def checked_fixture(self, forbidden):
        with forbid_unrelated_access(self.source, forbidden) as trace:
            copied = acquisition_fixture(self.source, self.destination)
        self.assertEqual(trace['blocked'], [])
        self.assertEqual(len(trace['copies']), 29)
        self.assertEqual(len(copied), 29)
        expected = set(copied) | {'tests/hol_composition/fixture-pins.json'}
        self.assertEqual(set(run.inventory(self.destination)), expected)
        self.assertEqual(list((self.destination / 'toolchain').iterdir()), [])
        return copied

    def test_preexisting_source_toolchain_directory_is_not_read_or_copied(self):
        toolchain = self.source / 'toolchain'
        (toolchain / 'runtime-sentinel').write_text('must not read')
        self.checked_fixture([toolchain])
        self.assertEqual((toolchain / 'runtime-sentinel').read_text(), 'must not read')

    def test_original_acquisition_with_existing_toolchain_directory(self):
        toolchain = self.source / 'toolchain'
        (toolchain / 'sentinel').write_text('must not read')
        with forbid_unrelated_access(self.source, [toolchain]) as trace, \
             mock.patch.object(run, 'ROOT', self.source):
            AcquisitionTests('test_real_snapshot_wiring_offline').test_real_snapshot_wiring_offline()
        self.assertEqual(trace['blocked'], [])

    def test_preexisting_source_toolchain_symlink_is_not_followed(self):
        runtime = self.root / 'external-runtime'
        runtime.mkdir()
        (runtime / 'sentinel').write_text('must not read')
        toolchain = self.source / 'toolchain'
        toolchain.rmdir()
        toolchain.symlink_to(runtime, target_is_directory=True)
        self.checked_fixture([toolchain, runtime])
        self.assertTrue(toolchain.is_symlink())

    def test_original_acquisition_with_existing_toolchain_symlink(self):
        runtime = self.root / 'external-runtime'
        runtime.mkdir()
        (runtime / 'sentinel').write_text('must not read')
        toolchain = self.source / 'toolchain'
        toolchain.rmdir()
        toolchain.symlink_to(runtime, target_is_directory=True)
        with forbid_unrelated_access(self.source, [toolchain, runtime]) as trace, \
             mock.patch.object(run, 'ROOT', self.source):
            AcquisitionTests('test_real_snapshot_wiring_offline').test_real_snapshot_wiring_offline()
        self.assertEqual(trace['blocked'], [])

    def test_broken_source_toolchain_symlink_is_ignored(self):
        toolchain = self.source / 'toolchain'
        toolchain.rmdir()
        toolchain.symlink_to(self.root / 'missing-runtime')
        self.checked_fixture([toolchain])
        self.assertTrue(toolchain.is_symlink())

    def test_large_unrelated_corpus_build_runtime_trees_are_not_traversed(self):
        forbidden = [self.source / name for name in
                     ('arena/corpus', 'build/unrelated', 'build/workers', 'runtime', 'unrelated')]
        for tree in forbidden:
            (tree / 'deep').mkdir(parents=True)
            with (tree / 'deep/large-sentinel').open('xb') as stream:
                stream.truncate(8 * 1024 ** 3)
            for number in range(32):
                (tree / ('branch-' + str(number))).mkdir()
        self.checked_fixture(forbidden + [self.source / 'toolchain'])
        for tree in forbidden:
            self.assertEqual((tree / 'deep/large-sentinel').stat().st_size, 8 * 1024 ** 3)

    def test_tripwires_reject_reads_scans_and_copy_attempts(self):
        forbidden = self.source / 'unrelated'
        forbidden.mkdir()
        sentinel = forbidden / 'sentinel'
        sentinel.write_text('do not copy')
        with forbid_unrelated_access(self.source, [forbidden]) as trace:
            for operation in (lambda: sentinel.read_bytes(), lambda: os.scandir(forbidden),
                    lambda: os.scandir(self.source), lambda: sentinel.stat(),
                    lambda: shutil.copyfile(sentinel, self.root / 'bad-copy'),
                    lambda: shutil.copytree(self.source, self.root / 'bad-tree')):
                with self.assertRaises(AssertionError):
                    operation()
        self.assertEqual(len(trace['blocked']), 6)
        self.assertFalse((self.root / 'bad-copy').exists())
        self.assertFalse((self.root / 'bad-tree').exists())

    def test_preexisting_destination_toolchain_directory_is_not_overwritten(self):
        toolchain = self.destination / 'toolchain'
        toolchain.mkdir(parents=True)
        (toolchain / 'keep').write_text('preserve')
        with self.assertRaises(ValueError):
            acquisition_fixture(self.source, self.destination)
        self.assertEqual((toolchain / 'keep').read_text(), 'preserve')

    def test_preexisting_destination_toolchain_symlink_is_not_followed(self):
        runtime = self.root / 'external-runtime'
        runtime.mkdir()
        (runtime / 'keep').write_text('preserve')
        self.destination.mkdir()
        (self.destination / 'toolchain').symlink_to(runtime, target_is_directory=True)
        with self.assertRaises(ValueError):
            acquisition_fixture(self.source, self.destination)
        self.assertEqual((runtime / 'keep').read_text(), 'preserve')

    def test_missing_explicit_frontend_artifact_is_refused(self):
        (self.source / 'build/frontend/wire.cmo').unlink()
        with self.assertRaisesRegex(ValueError, 'Missing required acquisition input'):
            acquisition_fixture(self.source, self.destination)

    def test_required_symlink_input_is_refused_without_reading_target(self):
        forbidden = self.root / 'unrelated-runtime'
        forbidden.mkdir()
        (forbidden / 'wire.cmo').write_text('do not read')
        required = self.source / 'build/frontend/wire.cmo'
        required.unlink()
        required.symlink_to(forbidden / 'wire.cmo')
        with forbid_unrelated_access(self.source, [forbidden]) as trace:
            with self.assertRaisesRegex(ValueError, 'Symlinked required acquisition input'):
                acquisition_fixture(self.source, self.destination)
        self.assertEqual(trace['blocked'], [])

    def test_unselected_manifest_entry_cannot_trigger_unrelated_copy(self):
        forbidden = self.source / 'tests/hol_composition/data/unrelated'
        forbidden.mkdir()
        (forbidden / 'sentinel').write_text('do not copy')
        path = self.source / 'tests/hol_composition/fixture-pins.json'
        manifest = json.loads(path.read_text())
        manifest['entries'].append({'path': 'data/unrelated/sentinel', 'sha256': '0' * 64,
                                    'bytes': 8 * 1024 ** 3})
        path.write_text(json.dumps(manifest))
        self.checked_fixture([forbidden])
        copied_manifest = json.loads((self.destination / 'tests/hol_composition/fixture-pins.json').read_text())
        self.assertEqual(len(copied_manifest['entries']), 3)

    def test_selected_fixture_pin_mismatch_is_refused(self):
        path = self.source / 'tests/hol_composition/fixture-pins.json'
        manifest = json.loads(path.read_text())
        manifest['entries'][0]['sha256'] = '0' * 64
        path.write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, 'Acquisition fixture pin mismatch'):
            acquisition_fixture(self.source, self.destination)


if __name__ == '__main__':
    unittest.main()
