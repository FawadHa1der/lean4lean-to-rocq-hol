"""Exercise alias ownership without launching or changing the real toolchain."""
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[2] / 'scripts/toolchain-env.sh'


def alias(directory):
    digest = hashlib.sha256(str(directory).encode()).hexdigest()[:12]
    return Path('/private/tmp') / f'lean4lean-{os.getuid()}-{digest}'


class AliasTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='toolchain-alias-test-', dir='/private/tmp')
        self.root = Path(self.temp.name)
        self.owned = set()

    def tearDown(self):
        for path in self.owned:
            if path.is_symlink():
                path.unlink()
            elif path.exists():
                shutil.rmtree(path)
        self.temp.cleanup()

    def project(self, name):
        root = self.root / name
        root.mkdir()
        directory = root / 'toolchain'
        owned_alias = alias(directory)
        if os.path.lexists(owned_alias):
            self.fail('Refusing a pre-existing test alias: ' + str(owned_alias))
        self.owned.add(owned_alias)
        return root, directory

    def run_env(self, root):
        return subprocess.run(['sh', '-c',
            'PROJECT_ROOT="$1"; . "$2" || exit $?; '
            'printf "%s\\n%s\\n" "$TOOLCHAIN_DIR" "$TOOLCHAIN_ALIAS"',
            'alias-test', str(root), str(SCRIPT)], capture_output=True, text=True, timeout=10)

    def test_direct_installation_keeps_original_alias(self):
        root, directory = self.project('direct project:colon')
        directory.mkdir()
        result = self.run_env(root)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.splitlines(), [str(directory), str(alias(directory))])
        self.assertEqual(alias(directory).readlink(), directory)

    def test_snapshot_recreates_original_alias(self):
        root, directory = self.project('original project:colon')
        directory.mkdir()
        snapshot, link = self.project('snapshot')
        link.symlink_to(directory)
        result = self.run_env(snapshot)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.splitlines(), [str(directory), str(alias(directory))])
        self.assertEqual(alias(directory).readlink(), directory)
        self.assertFalse(alias(link).exists())

    def test_relative_snapshot_link(self):
        root, directory = self.project('original')
        directory.mkdir()
        snapshot, link = self.project('relative snapshot')
        link.symlink_to(Path('..') / root.name / 'toolchain')
        result = self.run_env(snapshot)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(alias(directory).readlink(), directory)

    def test_existing_original_alias_is_reused(self):
        root, directory = self.project('existing')
        directory.mkdir()
        original = alias(directory)
        original.symlink_to(directory)
        before = original.lstat()
        snapshot, link = self.project('existing snapshot')
        link.symlink_to(directory)
        result = self.run_env(snapshot)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(original.lstat().st_ino, before.st_ino)

    def test_setup_relocation_is_not_canonicalized(self):
        root, directory = self.project('relocation')
        physical = alias(directory)
        physical.mkdir()
        directory.symlink_to(physical)
        result = self.run_env(root)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.splitlines(), [str(directory), str(physical)])
        self.assertEqual(directory.readlink(), physical)
        self.assertFalse(physical.is_symlink())

    def test_wrong_alias_is_refused_without_replacement(self):
        root, directory = self.project('wrong alias')
        directory.mkdir()
        wrong = self.root / 'unrelated'
        wrong.mkdir()
        original = alias(directory)
        original.symlink_to(wrong)
        snapshot, link = self.project('wrong alias snapshot')
        link.symlink_to(directory)
        result = self.run_env(snapshot)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('Refusing mismatched toolchain alias', result.stderr)
        self.assertEqual(original.readlink(), wrong)

    def test_occupied_alias_is_refused_without_modification(self):
        root, directory = self.project('occupied')
        directory.mkdir()
        original = alias(directory)
        original.mkdir()
        before = original.stat().st_ino
        result = self.run_env(root)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('Refusing occupied toolchain alias', result.stderr)
        self.assertEqual(original.stat().st_ino, before)

    def test_dangling_toolchain_link_does_not_create_an_alias(self):
        root, directory = self.project('dangling')
        directory.symlink_to(self.root / 'absent')
        result = self.run_env(root)
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(alias(directory).exists())


if __name__ == '__main__':
    unittest.main(verbosity=2)
