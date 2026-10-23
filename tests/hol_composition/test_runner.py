"""Runner regression tests, not logical checker or Arena case counts."""
import json
from pathlib import Path
import tempfile
import unittest

import run


class LogTests(unittest.TestCase):
    def outcome(self, text):
        return run.inspect_log(text, [run.marker('EXAMPLE')])[2]

    def test_exact_marker(self):
        self.assertTrue(self.outcome('# HOL_EXAMPLE_TESTS_PASSED 5\n'))

    def test_missing_marker(self):
        self.assertFalse(self.outcome('Exit 0\n'))

    def test_echo_is_not_execution(self):
        self.assertFalse(self.outcome('print_endline "HOL_EXAMPLE_TESTS_PASSED 5";;\n'))

    def test_duplicate_marker(self):
        self.assertFalse(self.outcome('HOL_EXAMPLE_TESTS_PASSED 5\n' * 2))

    def test_error_after_marker(self):
        self.assertFalse(self.outcome('HOL_EXAMPLE_TESTS_PASSED 5\nException: Failure "bad"\n'))

    def test_loader_error(self):
        self.assertFalse(self.outcome('Cannot find file x\nHOL_EXAMPLE_TESTS_PASSED 5\n'))

    def test_exact_private_marker(self):
        pattern = r'PRIVATE_HISTORY_INVENTORY_DONE [^\r\n]+'
        self.assertTrue(run.inspect_log('# PRIVATE_HISTORY_INVENTORY_DONE checked\n', [pattern])[2])

    def test_public_groups(self):
        jobs = {name: job for name, job in run.jobs().items() if not name.startswith('early-')}
        self.assertEqual(len(jobs), 124)
        self.assertIn('bool-general', jobs)
        for operation in ('beq', 'ble'):
            for phase in ('empty', 'nat-context', 'dependent', 'beta', 'let', 'named',
                          'guards', 'missing', 'impostor-zz', 'impostor-zs',
                          'impostor-sz', 'impostor-ss', 'finite'):
                self.assertIn('bool-' + operation + '-' + phase, jobs)
        for group in ('differential', 'guards', 'benchmark'):
            self.assertIn('closed-computation-' + group, jobs)
        self.assertIn('indexed-boundary', jobs)
        self.assertIn('indexed-history-joint', jobs)
        self.assertIn('raw-function-file-119', jobs)
        self.assertIn('hadd-boundary', jobs)
        self.assertIn('hadd-mixed', jobs)
        self.assertIn('mul-general', jobs)
        self.assertIn('mul-cases', jobs)
        for group in ('pow-general', 'pow-empty', 'pow-contexts', 'pow-wrappers'):
            self.assertIn(group, jobs)
        self.assertIn('add-context-general', jobs)
        self.assertIn('add-context', jobs)
        self.assertIn('derived-add', jobs)
        self.assertIn('derived-add-wrappers', jobs)
        self.assertIn('add-evaluation-general', jobs)
        self.assertIn('add-evaluation', jobs)
        self.assertIn('nat-recurrence-general', jobs)
        self.assertIn('nat-recurrence', jobs)
        self.assertEqual(jobs['preserved-full']['limit'], 900)
        self.assertTrue(all(j['limit'] == 180 for name, j in jobs.items() if name != 'preserved-full'))

    def test_registered_driver_sources_exist(self):
        for name, job in run.jobs().items():
            if 'source_file' in job:
                self.assertTrue((run.SUITE / 'drivers' / job['source_file']).is_file(), name)


class ProcessTests(unittest.TestCase):
    def attempt(self, shell, limit=2):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            snapshot = root / 'snapshot'
            (snapshot / 'scripts').mkdir(parents=True)
            (snapshot / 'scripts/private-hol.sh').write_text(shell)
            report = root / 'report'
            report.mkdir()
            result = run.run_job(snapshot, report, 'helper', {
                'source': '', 'markers': [run.marker('EXAMPLE')], 'limit': limit, 'options': {}})
            self.assertTrue(result['reaped'])
            self.assertTrue(result['process_group_absent'])
            self.assertTrue((report / 'helper.input.ml').is_file())
            self.assertEqual(json.loads((report / 'helper.json').read_text()), result)
            return result

    def test_successful_process(self):
        self.assertTrue(self.attempt('printf "HOL_EXAMPLE_TESTS_PASSED 1\\n"\n')['passed'])

    def test_nonzero_not_pass(self):
        self.assertFalse(self.attempt('printf "HOL_EXAMPLE_TESTS_PASSED 1\\n"\nexit 2\n')['passed'])

    def test_timeout_not_pass(self):
        result = self.attempt('exec sleep 10\n', limit=0.1)
        self.assertTrue(result['timed_out'])
        self.assertFalse(result['passed'])

    def test_source_mutation_not_pass(self):
        result = self.attempt('printf "HOL_EXAMPLE_TESTS_PASSED 1\\n"\nprintf changed > new-source.ml\n')
        self.assertFalse(result['passed'])
        self.assertNotEqual(result['before'], result['after'])


class FixtureTests(unittest.TestCase):
    def test_checked_in_pins(self):
        run.verify_fixtures(Path(__file__).resolve().parent)

    def test_modified_or_extra_fixture_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'data').mkdir()
            fixture = root / 'data/input.ndjson'
            fixture.write_text('{}\n')
            (root / 'fixture-pins.json').write_text(json.dumps({'entries': [{
                'path': 'data/input.ndjson', 'sha256': run.digest(fixture), 'bytes': 3}]}))
            run.verify_fixtures(root)
            fixture.write_text('[]\n')
            with self.assertRaises(ValueError):
                run.verify_fixtures(root)
            fixture.write_text('{}\n')
            (root / 'data/extra.ndjson').write_text('{}\n')
            with self.assertRaises(ValueError):
                run.verify_fixtures(root)


if __name__ == '__main__':
    unittest.main()
