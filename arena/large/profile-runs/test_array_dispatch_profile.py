import unittest

from profile_array_dispatch import sample_eligible, TARGET_LINE, TARGET_NAME


class TargetSampleTests(unittest.TestCase):
    def event(self, **changes):
        event = {"stage": "declaration", "line": TARGET_LINE, "checked": 1703,
                 "declaration": {"names": [TARGET_NAME]}, "observed_wall_seconds": 40.0}
        event.update(changes)
        return event

    def test_stable_exact_target(self):
        self.assertTrue(sample_eligible([self.event()], 50.0, 99.0))

    def test_no_early_sample(self):
        self.assertFalse(sample_eligible([self.event()], 49.99, 99.0))

    def test_no_blind_elapsed_trigger(self):
        self.assertFalse(sample_eligible([self.event(line=94434)], 100.0, 49.0))

    def test_no_wrong_name(self):
        self.assertFalse(sample_eligible([self.event(declaration={"names": ["wrong"]})], 60.0, 89.0))

    def test_no_wrong_count(self):
        self.assertFalse(sample_eligible([self.event(checked=1702)], 60.0, 89.0))

    def test_no_wrong_stage(self):
        self.assertFalse(sample_eligible([self.event(stage="check")], 60.0, 89.0))

    def test_new_event_resets_quiet_time(self):
        self.assertFalse(sample_eligible([self.event(), self.event(observed_wall_seconds=55.0)], 60.0, 89.0))

    def test_target_must_remain_last(self):
        self.assertFalse(sample_eligible([self.event(), self.event(line=120591)], 60.0, 89.0))

    def test_sample_must_fit_budget(self):
        self.assertFalse(sample_eligible([self.event()], 144.0, 5.0))

    def test_no_events(self):
        self.assertFalse(sample_eligible([], 60.0, 89.0))


if __name__ == "__main__":
    unittest.main()
