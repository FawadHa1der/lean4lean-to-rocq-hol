"""Authentic unsafe declarations and adversarial boundary checks, without Lean verdict delegation."""
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
FIXTURE = Path(__file__).with_name("unsafe-inductives.ndjson")
CHECKER = ROOT / "build/rocq-check"
DECL_TAGS = {"def", "axiom", "opaque", "thm", "quot", "inductive"}


class SafetyExports(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = [json.loads(line) for line in FIXTURE.read_text().splitlines()]
        cls.binary_hash = hashlib.sha256(CHECKER.read_bytes()).hexdigest()
        baseline = subprocess.run([str(CHECKER), str(FIXTURE)], capture_output=True, text=True, timeout=10)
        if baseline.returncode != 0:
            raise AssertionError(f"valid baseline must accept before mutations: {baseline.stderr}")
        cls.name_ids = {r["str"]["str"]: r["in"] for r in cls.rows if "str" in r and r["str"]["pre"] == 0}

    def check_rows(self, rows, expected):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "input.ndjson"
            path.write_text("".join(json.dumps(row, separators=(",", ":")) + "\n" for row in rows))
            result = subprocess.run([str(CHECKER), str(path)], capture_output=True, text=True, timeout=10)
        self.assertEqual(hashlib.sha256(CHECKER.read_bytes()).hexdigest(), self.binary_hash)
        self.assertEqual(result.returncode, expected, result.stderr)

    def changed(self):
        return copy.deepcopy(self.rows)

    def definition(self, rows, name):
        return next(r["def"] for r in rows if "def" in r and r["def"]["name"] == self.name_ids[name])

    def negative(self, rows):
        return next(r["inductive"] for r in rows if "inductive" in r and
                    r["inductive"]["types"][0]["name"] == self.name_ids["UNeg"])

    def test_original(self):
        self.check_rows(self.rows, 0)

    def test_safe_definition_cannot_use_unsafe_type(self):
        rows = self.changed()
        self.definition(rows, "uId")["safety"] = "safe"
        self.check_rows(rows, 1)

    def test_partial_definition_cannot_use_unsafe_type(self):
        rows = self.changed()
        self.definition(rows, "uId")["safety"] = "partial"
        self.check_rows(rows, 1)

    def test_mixed_inductive_safety(self):
        rows = self.changed()
        self.negative(rows)["ctors"][0]["isUnsafe"] = False
        self.check_rows(rows, 1)

    def test_negative_occurrence_not_allowed_when_safe(self):
        rows = self.changed()
        group = self.negative(rows)
        for key in ("types", "ctors", "recs"):
            for member in group[key]:
                member["isUnsafe"] = False
        self.check_rows(rows, 1)

    def test_unsafe_recursor_k_still_checked(self):
        rows = self.changed()
        self.negative(rows)["recs"][0]["k"] = True
        self.check_rows(rows, 1)

    def test_unsafe_constructor_fields_still_checked(self):
        rows = self.changed()
        self.negative(rows)["ctors"][0]["numFields"] = 0
        self.check_rows(rows, 1)

    def test_unsafe_recursor_rules_still_checked(self):
        rows = self.changed()
        self.negative(rows)["recs"][0]["rules"] = []
        self.check_rows(rows, 1)

    def test_mutual_safety_mismatch(self):
        rows = self.changed()
        self.definition(rows, "uA")["safety"] = "partial"
        self.check_rows(rows, 1)

    def test_reordered_declarations(self):
        nodes = [r for r in self.rows if not DECL_TAGS.intersection(r)]
        declarations = [r for r in self.rows if DECL_TAGS.intersection(r)]
        self.check_rows(nodes + declarations[::-1], 0)

    def test_interleaved_mutual_declarations(self):
        nodes = [r for r in self.rows if not DECL_TAGS.intersection(r)]
        declarations = [r for r in self.rows if DECL_TAGS.intersection(r)]
        mutual = [r for r in declarations if "def" in r and len(r["def"]["all"]) == 2]
        other = [r for r in declarations if r not in mutual]
        self.assertEqual(len(mutual), 2)
        self.check_rows(nodes + [mutual[0]] + other + [mutual[1]], 0)

    def test_actual_missing_mutual_member(self):
        rows = [r for r in self.rows if not("def" in r and r["def"]["name"] == self.name_ids["uB"])]
        self.check_rows(rows, 1)


if __name__ == "__main__":
    unittest.main()
