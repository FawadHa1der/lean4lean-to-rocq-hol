#!/usr/bin/env python3
"""Read-only Cedar acquisition policy tests; run after preparation."""

import subprocess
import sys
import tarfile
import unittest
from unittest.mock import patch

import acquire_cedar_arena as cedar


class ArchivePolicyTests(unittest.TestCase):
    def checked(self, name, kind=tarfile.REGTYPE, link=""):
        member = tarfile.TarInfo(name)
        member.type = kind
        member.linkname = link
        return list(cedar.members([member], {"directory": "repo"}))

    def test_files_and_in_tree_symlinks(self):
        self.assertEqual(len(self.checked("repo/a.lean")), 1)
        self.assertEqual(len(self.checked("repo/a/link", tarfile.SYMTYPE, "../target")), 1)

    def test_unsafe_members(self):
        for name in ("/repo/a", "repo/../escape", "other/a", "repo/a\\b"):
            with self.subTest(name=name), self.assertRaises(ValueError):
                self.checked(name)
        for kind in (tarfile.LNKTYPE, tarfile.CHRTYPE, tarfile.BLKTYPE, tarfile.FIFOTYPE):
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                self.checked("repo/a", kind)

    def test_escaping_symlinks(self):
        for target in ("/etc/passwd", "../../escape", "..\\escape"):
            with self.subTest(target=target), self.assertRaises(ValueError):
                self.checked("repo/a/link", tarfile.SYMTYPE, target)


class PreparedSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lock = cedar.load_lock()

    def test_original_sources_and_links(self):
        hashes = cedar.source_hashes(self.lock)
        self.assertIn("cedar/cedar-lean/lakefile.lean", hashes)
        self.assertIn("batteries/lakefile.toml", hashes)
        self.assertEqual(hashes["cedar/lean-toolchain"], {"symlink": "cedar-lean/lean-toolchain"})

    def test_simulated_source_change_fails_without_edits(self):
        with patch.object(cedar, "digest", return_value="0" * 64):
            with self.assertRaisesRegex(ValueError, "source changed"):
                cedar.source_hashes(self.lock)

    def test_invalid_limits_fail_before_build(self):
        for argument, value in (("--memory-mib", "0"), ("--build-timeout", "0"),
                                ("--export-timeout", "nan")):
            with self.subTest(argument=argument):
                result = subprocess.run([sys.executable, "-B", str(cedar.ROOT / "scripts/acquire_cedar_arena.py"),
                                         "--execute-reviewed", argument, value],
                                        capture_output=True, text=True, timeout=10)
                self.assertEqual(result.returncode, 2)


if __name__ == "__main__":
    unittest.main()
