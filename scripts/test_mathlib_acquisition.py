#!/usr/bin/env python3
"""Read-only checks for the separate Mathlib acquisition policy."""

import json
import subprocess
import sys
import unittest

from acquire_mathlib_arena import CACHE_PROFILE, CURL_POLICY, package_overrides
from prepare_mathlib_arena import ROOT, load_lock, source_hashes, source_paths


class MathlibPolicy(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lock = load_lock()

    def test_exact_recipe_and_distinct_toolchain(self):
        self.assertEqual(self.lock["module"], "Mathlib")
        self.assertEqual(self.lock["lean_version"], "4.34.1")
        self.assertEqual(self.lock["source"]["revision"], "d13f23b723b8a846827a245b89c10fc7d3f11612")
        self.assertEqual(self.lock["expected"]["size"], 6184415052)
        self.assertNotIn("cslib", self.lock["sources"])

    def test_prepared_sources_and_transitive_pins(self):
        self.assertGreater(len(source_hashes(self.lock)), 10000)

    def test_dependency_archives_match_but_builds_are_isolated(self):
        previous = json.loads((ROOT / self.lock["dependency_pins"]["lock"]).read_text())
        for name in self.lock["dependency_pins"]["names"]:
            self.assertEqual(self.lock["sources"][name], previous["sources"][name])
        self.assertNotEqual(previous["lean_version"], self.lock["lean_version"])
        paths = source_paths(self.lock)
        override = package_overrides(paths)
        self.assertEqual(len(override["packages"]), 8)
        for p in override["packages"]:
            self.assertEqual((paths["mathlib"] / p["dir"]).resolve(), paths[p["name"]].resolve())
            self.assertIn("arena/large/mathlib/sources", str(paths[p["name"]]))
            self.assertNotIn(":", p["dir"])

    def test_network_and_download_bounds(self):
        self.assertIn('(remote tcp "*:443")', CACHE_PROFILE)
        self.assertIn('/private/var/run/mDNSResponder', CACHE_PROFILE)
        self.assertNotIn('(allow network*)', CACHE_PROFILE)
        self.assertIn('parallel-max = 2', CURL_POLICY)
        self.assertIn('max-time = 60', CURL_POLICY)

    def test_invalid_resource_limits_fail_without_execution(self):
        for flag, value in [("--memory-mib", "0"), ("--memory-mib", "8193"),
                            ("--max-missing-modules", "17"), ("--max-missing-modules", "-1")]:
            result = subprocess.run([sys.executable, "-B", str(ROOT / "scripts/acquire_mathlib_arena.py"), flag, value],
                                    capture_output=True, text=True, timeout=15)
            self.assertEqual(result.returncode, 2)


if __name__ == "__main__":
    unittest.main()
