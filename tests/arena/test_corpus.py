"""Verify the actual pinned corpus, generated cases, and structural audit."""

from collections import Counter
from itertools import zip_longest
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
import test_arena as runner
import test_arena_adversarial as adversarial
import test_arena_schema as schema


class CorpusTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.path = ROOT / "arena/manifest.json"
        if not cls.path.exists():
            raise unittest.SkipTest("pinned manifest absent; run scripts/fetch_arena.py")
        cls.manifest = runner.load_manifest(cls.path)

    def test_complete_published_inventory(self):
        cases = self.manifest["cases"]
        self.assertEqual(len(cases), 220)
        self.assertEqual(Counter(case["expected"] for case in cases), {"accept": 131, "reject": 71, "either": 18})
        self.assertEqual(len({case["definition"] for case in cases}), 80)
        self.assertEqual(sum(case["source_kind"] == "generated_multiple" for case in cases), 141)

    def test_every_available_input_hash_and_size(self):
        for case in self.manifest["cases"]:
            if case["availability"] != "available":
                continue
            with self.subTest(case=case["id"]):
                path = self.path.parent / case["path"]
                self.assertEqual(path.stat().st_size, case["size"])
                self.assertEqual(runner.digest(path), case["sha256"])

    def test_large_and_either_omissions_are_not_skips(self):
        missing = [case for case in self.manifest["cases"] if case["availability"] != "available"]
        self.assertLessEqual(len(missing), 24)
        for case in missing:
            self.assertEqual(case["availability"], "missing_download")
            self.assertTrue(case["size"] > 10 * 1024 * 1024 or case["expected"] == "either")
            self.assertNotIn("skip_reason", case)
            self.assertIn("missing_reason", case)

    def test_full_structural_scan(self):
        report = schema.audit(self.path)
        self.assertEqual(report["errors"], [])
        available = sum(case["availability"] == "available" for case in self.manifest["cases"])
        self.assertEqual(report["scanned_cases"], available)
        self.assertEqual(report["format_versions"], {"3.1.0": available})
        self.assertEqual(report["observation_counts"].get("blank_lines", 0), 0)
        self.assertEqual(report["observation_counts"].get("missing_all", 0), 0)
        self.assertEqual(report["observation_counts"].get("missing_isReflexive", 0), 0)
        self.assertNotIn("in", report["explicit_index_zero"])
        self.assertNotIn("il", report["explicit_index_zero"])

    def test_generated_metamorphic_inputs_preserve_json_values(self):
        with tempfile.TemporaryDirectory() as tmp:
            destination = Path(tmp)
            result = adversarial.generate(self.path, destination)
            available = {case["id"]: case for case in self.manifest["cases"] if case["availability"] == "available"}
            self.assertEqual(len(result["cases"]), len(available) + 7)
            runner.load_manifest(destination / "manifest.json")
            for case in result["cases"]:
                generated = destination / case["path"]
                self.assertEqual(runner.digest(generated), case["sha256"])
                if case["id"].startswith("metamorphic/"):
                    source = available[case["parent"]["id"]]
                    self.assertEqual(case["expected"], source["expected"])
                    with (self.path.parent / source["path"]).open("rb") as old_stream, generated.open("rb") as new_stream:
                        old = (json.loads(line) for line in old_stream if line.strip())
                        new = (json.loads(line) for line in new_stream if line.strip())
                        for index, (before, after) in enumerate(zip_longest(old, new, fillvalue=object()), 1):
                            self.assertEqual(before, after, f"{case['id']} record {index}")

    def test_semantic_mutations_are_separate_from_published_cases(self):
        source = ROOT / "arena/corpus/tutorial/001_basicDef.ndjson"
        records = [json.loads(line) for line in source.read_bytes().splitlines()]
        cases = list(adversarial.semantic_cases(records))
        self.assertEqual(len(cases), 7)
        self.assertEqual(Counter(expected for _, expected, _, _ in cases), {"accept": 1, "reject": 6})
        for _, _, case, _ in cases:
            self.assertEqual(case[0], records[0])
            self.assertEqual(case[1]["str"]["str"], "ArenaAdversarial")


if __name__ == "__main__":
    unittest.main()
