import hashlib
import json
from pathlib import Path
import signal
import tempfile
import unittest
from unittest.mock import Mock, patch

import extract_prefix
import profile_init
import summarize_sample


META = {"meta": {"format": {"version": "3.1.0"}, "lean": {"version": "test", "githash": "test"}}}


def name(index, value):
    return {"in": index, "str": {"pre": 0, "str": value}}


def axiom(index, typ=0):
    return {"axiom": {"name": index, "levelParams": [], "type": typ, "isUnsafe": False}}


def definition(index, all_names, safety="unsafe"):
    return {"def": {"name": index, "levelParams": [], "type": 0, "value": 1,
                    "all": all_names, "safety": safety, "hints": "opaque"}}


def audit(records, events=()):
    return extract_prefix.analyze([json.dumps(record).encode() + b"\n" for record in records], events)


class PrefixTests(unittest.TestCase):
    def setUp(self):
        self.base = [META, name(1, "A"), {"ie": 0, "sort": 0}, axiom(1)]

    def test_closed_positive_and_exact_progress(self):
        result = audit(self.base, [{"stage": "declaration", "line": 4, "checked": 0}])
        self.assertTrue(result["dependency_closed_in_input_order"])
        self.assertTrue(result["observed_full_run_batch_order_matches_prefix"])

    def test_progress_order_must_match(self):
        result = audit(self.base, [{"stage": "declaration", "line": 5, "checked": 0}])
        self.assertFalse(result["observed_full_run_batch_order_matches_prefix"])

    def test_missing_constant_in_opaque_body(self):
        records = self.base + [name(2, "missing"), name(3, "opaque"),
                              {"ie": 1, "const": {"name": 2, "us": []}},
                              {"opaque": {"name": 3, "type": 0, "levelParams": [],
                                          "value": 1, "all": [3], "isUnsafe": False}}]
        result = audit(records)
        self.assertFalse(result["dependency_closed_in_input_order"])
        self.assertEqual(result["missing_constant_names"], ["missing"])

    def test_forward_constant(self):
        records = [META, name(1, "A"), name(2, "B"), {"ie": 0, "sort": 0},
                   {"ie": 1, "const": {"name": 2, "us": []}}, axiom(1, 1), axiom(2)]
        result = audit(records)
        self.assertFalse(result["dependency_closed_in_input_order"])
        self.assertTrue(result["audit_problems"][0]["forward_dependency"])

    def test_self_reference_permitted_by_transport_only(self):
        records = [META, name(1, "A"), {"ie": 1, "const": {"name": 1, "us": []}}, axiom(1, 1)]
        self.assertTrue(audit(records)["dependency_closed_in_input_order"])

    def test_nat_implicit_dependencies(self):
        result = audit(self.base + [name(2, "B"), {"ie": 1, "natVal": "1"}, axiom(2, 1)])
        self.assertEqual(result["missing_constant_names"], ["Nat", "Nat.succ", "Nat.zero"])

    def test_string_implicit_dependencies(self):
        result = audit(self.base + [name(2, "B"), {"ie": 1, "strVal": "s"}, axiom(2, 1)])
        self.assertEqual(len(result["missing_constant_names"]), 7)

    def test_quotient_implicit_eq(self):
        records = self.base + [name(2, "Q"), {"quot": {"name": 2, "type": 0,
                                                     "levelParams": [], "kind": "type"}}]
        self.assertFalse(audit(records)["dependency_closed_in_input_order"])

    def test_projection_owner(self):
        records = self.base + [name(2, "B"), name(3, "MissingOwner"),
                              {"ie": 1, "proj": {"typeName": 3, "idx": 0, "struct": 0}}, axiom(2, 1)]
        self.assertEqual(audit(records)["missing_constant_names"], ["MissingOwner"])

    def test_mutual_forward_reference(self):
        records = [META, name(1, "A"), name(2, "B"), {"ie": 0, "sort": 0},
                   {"ie": 1, "const": {"name": 2, "us": []}},
                   definition(1, [1, 2]), definition(2, [2, 1])]
        result = audit(records, [{"stage": "declaration", "line": 6, "checked": 0}])
        self.assertTrue(result["dependency_closed_in_input_order"])
        self.assertTrue(result["observed_full_run_batch_order_matches_prefix"])
        self.assertEqual(result["batches"], 1)

    def test_incomplete_mutual_group(self):
        records = [META, name(1, "A"), name(2, "B"), {"ie": 0, "sort": 0},
                   {"ie": 1, "const": {"name": 1, "us": []}}, definition(1, [1, 2])]
        self.assertFalse(audit(records)["dependency_closed_in_input_order"])

    def test_recursor_rhs_dependency(self):
        records = self.base + [name(2, "rec"), name(3, "missing"),
                              {"ie": 1, "const": {"name": 3, "us": []}},
                              {"inductive": {"types": [], "ctors": [], "recs": [
                                  {"name": 2, "type": 0, "levelParams": [], "all": [1],
                                   "rules": [{"ctor": 1, "rhs": 1}]}]}}]
        self.assertEqual(audit(records)["missing_constant_names"], ["missing"])

    def test_reject_non_declaration_boundary(self):
        with self.assertRaises(ValueError):
            audit(self.base + [name(2, "B")])


class SampleTests(unittest.TestCase):
    def test_recursive_frames_count_once_inclusive(self):
        sample = """Call graph:
    10 root  (in checker)
      10 A  (in checker)
        6 A  (in checker)
          4 B  (in checker)
        3 B  (in checker)
Total number in stack:
"""
        result = summarize_sample.summarize(sample)
        inclusive = {row["symbol"]: row["samples"] for row in result["inclusive_without_recursive_double_count"]}
        exclusive = {row["symbol"]: row["samples"] for row in result["exclusive"]}
        self.assertEqual(result["stack_samples"], 10)
        self.assertTrue(result["call_graph_complete"])
        self.assertEqual(inclusive["A"], 10)
        self.assertEqual(exclusive, {"B": 7, "A": 3})

    def test_invalid_tree_rejected(self):
        with self.assertRaises(ValueError):
            summarize_sample.summarize("Call graph:\n    1 root\n      2 child\nTotal number in stack:\n")

    def test_truncated_tree_cannot_invent_exclusive_parent_samples(self):
        with self.assertRaisesRegex(ValueError, "incomplete"):
            summarize_sample.summarize("Call graph:\n    10 root\n      3 child\n")

    def test_partial_final_frame_rejected(self):
        with self.assertRaises(ValueError):
            summarize_sample.summarize("Call graph:\n    10 root\n      3 ")

    def test_header_only_rejected(self):
        with self.assertRaisesRegex(ValueError, "incomplete"):
            summarize_sample.summarize("Call graph:\n")

    def test_terminator_without_graph_rejected(self):
        with self.assertRaises(ValueError):
            summarize_sample.summarize("Total number in stack:\n")

    def test_unknown_graph_line_rejected(self):
        with self.assertRaisesRegex(ValueError, "unrecognized"):
            summarize_sample.summarize("Call graph:\n    10 root\ncorrupt\nTotal number in stack:\n")

    def test_complete_native_heading_and_multiple_roots(self):
        result = summarize_sample.summarize(
            "Call graph:\n    7 first\n    3 second\n"
            "Total number in stack (recursive counted multiple, when >=5):\n")
        self.assertEqual(result["stack_samples"], 10)
        self.assertTrue(result["call_graph_complete"])

    def test_duplicate_graph_rejected(self):
        with self.assertRaisesRegex(ValueError, "duplicate"):
            summarize_sample.summarize("Call graph:\n    10 root\nCall graph:\nTotal number in stack:\n")


class DriverTests(unittest.TestCase):
    def test_fingerprint(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "input"
            path.write_bytes(b"content")
            result = profile_init.fingerprint(path)
            self.assertEqual(result["sha256"], hashlib.sha256(b"content").hexdigest())
            self.assertEqual(result["size"], 7)

    def test_running_child_killed_and_reaped(self):
        process = Mock(pid=123)
        process.poll.return_value = None
        with patch("profile_init.os.killpg") as kill:
            profile_init.stop_process(process)
            kill.assert_called_once_with(123, signal.SIGKILL)
        process.wait.assert_called_once_with()

    def test_finished_child_reaped_without_kill(self):
        process = Mock(pid=123)
        process.poll.return_value = 0
        with patch("profile_init.os.killpg") as kill:
            profile_init.stop_process(process)
            kill.assert_not_called()
        process.wait.assert_called_once_with()


if __name__ == "__main__":
    unittest.main()
