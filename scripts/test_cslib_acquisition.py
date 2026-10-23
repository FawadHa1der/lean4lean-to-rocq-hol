#!/usr/bin/env python3
"""Read-only policy tests for the CSLib acquisition worker."""

import json
import subprocess
import sys
import unittest

from acquire_cslib_arena import ROOT, load_lock, source_hashes, source_paths
from build_cslib_arena import CACHE_PROFILE, CURL_POLICY, package_overrides


class AcquisitionPolicy(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lock = load_lock()

    def test_published_recipe_is_unchanged(self):
        self.assertEqual(self.lock["module"], "Cslib")
        self.assertEqual(self.lock["lean_version"], "4.34.0")
        self.assertEqual(self.lock["expected"]["size"], 2422584798)
        self.assertEqual(self.lock["pre_build"], "lake exe cache get")

    def test_all_source_files_and_transitive_pins_match(self):
        self.assertGreater(len(source_hashes(self.lock)), 10000)

    def test_override_only_changes_locations(self):
        paths = source_paths(self.lock)
        project = paths["cslib"]
        overrides = package_overrides(self.lock, paths, project)
        self.assertEqual(overrides["schemaVersion"], "1.2.0")
        self.assertEqual(len(overrides["packages"]), 9)
        for p in overrides["packages"]:
            self.assertEqual((project / p["dir"]).resolve(), paths[p["name"]].resolve())
            self.assertNotIn(":", p["dir"])

    def test_network_and_parallel_bounds(self):
        self.assertIn('(remote tcp "*:443")', CACHE_PROFILE)
        self.assertNotIn('(allow network*)', CACHE_PROFILE)
        self.assertIn('parallel-max = 2', CURL_POLICY)
        self.assertIn('max-time = 60', CURL_POLICY)
        self.assertIn('proto = "=https"', CURL_POLICY)

    def test_invalid_memory_fails_without_build(self):
        for value in ("0", "8193", "-1"):
            result = subprocess.run([sys.executable, "-B", str(ROOT / "scripts/build_cslib_arena.py"),
                                     "--memory-mib", value], capture_output=True, text=True, timeout=15)
            self.assertEqual(result.returncode, 2)
            self.assertIn("at most 8192", result.stderr)

    def test_supplemental_cedar_never_claims_coverage(self):
        supplemental = json.loads((ROOT / "arena/large/cedar/supplemental.json").read_text())
        self.assertEqual(supplemental["classification"], "SUPPLEMENTAL")
        self.assertFalse(supplemental["official_arena"])
        self.assertFalse(supplemental["port_checker_verified"])
        self.assertEqual(supplemental["lines"] - supplemental["published_target"]["lines"], 3)


if __name__ == "__main__":
    unittest.main()
