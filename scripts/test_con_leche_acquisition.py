#!/usr/bin/env python3
"""Read-only acquisition policy tests; run after Con-Leche preparation."""

import subprocess
import sys
import unittest
from unittest.mock import patch

import build_con_leche_arena as build
from acquire_con_leche_arena import ROOT, WORK, load_lock


class AcquisitionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lock = load_lock()
        cls.source = WORK / "source" / cls.lock["source"]["directory"]

    def test_original_source_matches_archive(self):
        hashes = build.source_hashes(self.lock, self.source)
        self.assertIn("lakefile.toml", hashes)
        self.assertIn("tests/ConLecheTests.lean", hashes)
        self.assertIn("LICENSE", hashes)

    def test_changed_source_is_rejected_without_editing_it(self):
        with patch.object(build, "digest", return_value="0" * 64):
            with self.assertRaisesRegex(ValueError, "source changed from archive"):
                build.source_hashes(self.lock, self.source)

    def test_memory_counts_only_target_group(self):
        with patch.object(build.subprocess, "check_output", return_value="12 100\n34 500\n12 700\n"):
            self.assertEqual(build.group_rss_kib(12), 800)

    def test_invalid_resource_limits_fail_before_build(self):
        for argument, value in (("--memory-mib", "0"), ("--build-timeout", "0"),
                                ("--export-timeout", "nan")):
            with self.subTest(argument=argument):
                result = subprocess.run([sys.executable, "-B", str(ROOT / "scripts/build_con_leche_arena.py"),
                                         "--execute-reviewed", argument, value],
                                        capture_output=True, timeout=10, text=True)
                self.assertEqual(result.returncode, 2)


if __name__ == "__main__":
    unittest.main()
