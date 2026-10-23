import unittest

from profile_prefixes import classify_exit, sample_correlation


def event(wall, checked=1, line=10, stage="declaration"):
    return {"observed_wall_seconds": wall, "checked": checked, "line": line, "stage": stage}


class PrefixProfileTests(unittest.TestCase):
    def setUp(self):
        self.info = {"started_wall_seconds": 30.0, "ended_wall_seconds": 35.0, "exit_code": 0}

    def test_verdict_requires_actual_exit(self):
        for code, verdict in ((0, "accept"), (1, "reject"), (2, "decline"), (3, "fault"),
                              (-9, "fault"), (None, "fault")):
            with self.subTest(code=code):
                self.assertEqual(classify_exit(code, False), verdict)
                self.assertEqual(classify_exit(code, True), "timeout")

    def test_no_progress_across_complete_sample(self):
        result = sample_correlation(self.info, [event(20), event(36, 2, 11)])
        self.assertTrue(result["single_observed_active_declaration"])
        self.assertEqual(result["progress_before"]["line"], 10)

    def test_crossed_declarations_are_lower_bound_only(self):
        result = sample_correlation(self.info, [event(20), event(31, 2, 11), event(34, 3, 12)])
        self.assertFalse(result["single_observed_active_declaration"])
        self.assertEqual(len(result["progress_events_during"]), 2)
        self.assertEqual(result["progress_before"]["checked"], 1)
        self.assertEqual(result["progress_after"]["checked"], 3)

    def test_parse_sample_has_no_single_declaration(self):
        result = sample_correlation(self.info, [event(1, 0, 0, "parse")])
        self.assertFalse(result["single_observed_active_declaration"])

    def test_incomplete_sample_does_not_claim_exact_correlation(self):
        for extra in ({"exit_code": -9}, {"stopped_by_driver": True}, {"error": "failed"}):
            with self.subTest(extra=extra):
                result = sample_correlation({**self.info, **extra}, [event(20)])
                self.assertFalse(result["single_observed_active_declaration"])

    def test_no_sample(self):
        self.assertIsNone(sample_correlation(None, []))


if __name__ == "__main__":
    unittest.main()
