"""Canonical generation preserves bytes and integrity without whole-file lists."""
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import tracemalloc
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
import test_arena as runner
import test_arena_adversarial as generator


CONTROL = [
    {"meta": {"format": {"version": "3.1.0"}}},
    {"in": 1, "str": {"pre": 0, "str": "basicDef"}},
    {"il": 1, "succ": 0}, {"ie": 0, "sort": 1}, {"ie": 1, "sort": 0},
    {"def": {"all": [1], "hints": "opaque", "levelParams": [], "name": 1,
             "safety": "safe", "type": 0, "value": 1}},
]


class StreamingTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.destination = self.root / "generated"
        self.manifest = self.root / "manifest.json"
        self.control = self.root / "control.ndjson"
        self.control.write_bytes(generator.encode(CONTROL))

    def case(self, name, path, expected="accept"):
        return {"id": name, "path": path.name, "expected": expected,
                "availability": "available", "sha256": runner.digest(path),
                "size": path.stat().st_size, "timeout_seconds": 13}

    def manifest_for(self, cases):
        self.manifest.write_text(json.dumps({"manifest_version": 1, "cases": cases + [
            self.case("tutorial/001_basicDef", self.control)]}))

    def test_canonical_bytes_order_unicode_and_semantic_cases_unchanged(self):
        records = [{"z": 2, "a": [1, "caf\u00e9"]}, {"x": False}, {"n": None}]
        source = self.root / "spaced.ndjson"
        source.write_text("\n" + "\r\n\n".join(json.dumps(x, ensure_ascii=False) for x in records))
        self.manifest_for([self.case("synthetic", source, "either")])
        result = generator.generate(self.manifest, self.destination)
        self.assertEqual(len(result["cases"]), 9)
        first = result["cases"][0]
        expected = generator.encode(records)
        self.assertEqual((self.destination / first["path"]).read_bytes(), expected)
        self.assertEqual(first["sha256"], hashlib.sha256(expected).hexdigest())
        self.assertEqual(first["size"], len(expected))
        self.assertEqual(first["expected"], "either")
        self.assertEqual(first["timeout_seconds"], 13)
        self.assertEqual(first["path"], "inputs/" + first["sha256"] + ".ndjson")
        old_semantic = list(generator.semantic_cases(CONTROL))
        for item, (name, outcome, data, _) in zip(result["cases"][2:], old_semantic):
            self.assertEqual(item["id"], "adversarial/" + name)
            self.assertEqual(item["expected"], outcome)
            self.assertEqual((self.destination / item["path"]).read_bytes(), generator.encode(data))
        runner.load_manifest(self.destination / "manifest.json")

    def test_large_noncontrol_is_streamed_with_bounded_peak(self):
        source = self.root / "large.ndjson"
        line = (json.dumps({"text": "x" * 2048, "index": 0}) + "\n").encode()
        with source.open("wb") as stream:
            for _ in range(6000):
                stream.write(line)
        self.manifest_for([self.case("large", source)])
        tracemalloc.start()
        try:
            with mock.patch.object(Path, "read_bytes", side_effect=AssertionError("whole-file read")):
                result = generator.generate(self.manifest, self.destination)
            _, peak = tracemalloc.get_traced_memory()
        finally:
            tracemalloc.stop()
        self.assertLess(peak, 4 * 1024 * 1024)
        self.assertGreater(result["cases"][0]["size"], 12_000_000)
        with (self.destination / result["cases"][0]["path"]).open("rb") as stream:
            self.assertEqual(sum(1 for _ in stream), 6000)

    def test_invalid_source_never_publishes_partial_file_or_manifest(self):
        for kind in ("checksum", "size", "json"):
            with self.subTest(kind=kind):
                source = self.root / "bad.ndjson"
                source.write_bytes(b'{"a":1}\n' if kind != "json" else b'{"a":1}\nnot-json\n')
                case = self.case("bad", source)
                if kind == "checksum":
                    case["sha256"] = "0" * 64
                if kind == "size":
                    case["size"] += 1
                self.manifest_for([case])
                self.destination.mkdir(exist_ok=True)
                report = self.destination / "manifest.json"
                report.write_text('{"previous":"retained"}')
                with self.assertRaises(ValueError):
                    generator.generate(self.manifest, self.destination)
                self.assertEqual(report.read_text(), '{"previous":"retained"}')
                self.assertEqual(list((self.destination / "inputs").iterdir()), [])

    def test_manifest_drift_is_not_bound_to_new_checksum(self):
        self.manifest_for([])
        original = generator.semantic_cases

        def drift(baseline):
            for case in original(baseline):
                yield case
            self.manifest.write_text(self.manifest.read_text() + "\n")

        with mock.patch.object(generator, "semantic_cases", drift), self.assertRaisesRegex(ValueError, "manifest changed"):
            generator.generate(self.manifest, self.destination)
        self.assertFalse((self.destination / "manifest.json").exists())
        self.assertEqual(list((self.destination / "inputs").glob(".canonical-*")), [])

    def corpus_comparator(self):
        import test_corpus
        source = self.root / "comparison.ndjson"
        source.write_bytes(b'{"one":1}\n{"two":2}\n')
        self.manifest_for([self.case("comparison", source)])
        test = test_corpus.CorpusTests("test_generated_metamorphic_inputs_preserve_json_values")
        test.path = self.manifest
        test.manifest = runner.load_manifest(self.manifest)
        return test

    def test_streaming_corpus_comparator_accepts_equal_records(self):
        self.corpus_comparator().test_generated_metamorphic_inputs_preserve_json_values()

    def test_streaming_corpus_comparator_detects_extra_and_missing_records(self):
        original = generator.generate
        for extra in (False, True):
            def changed(manifest, destination):
                result = original(manifest, destination)
                case = result["cases"][0]
                path = destination / case["path"]
                payload = path.read_bytes()
                path.write_bytes(payload + b'{"extra":3}\n' if extra else payload.splitlines(keepends=True)[0])
                case["sha256"] = runner.digest(path)
                case["size"] = path.stat().st_size
                return result

            test = self.corpus_comparator()
            with self.subTest(extra=extra), mock.patch.object(generator, "generate", changed), \
                 self.assertRaisesRegex(AssertionError, "metamorphic/comparison record"):
                test.test_generated_metamorphic_inputs_preserve_json_values()


if __name__ == "__main__":
    unittest.main()
