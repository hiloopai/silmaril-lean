import contextlib
import importlib.util
import io
import os
import unittest
from datetime import datetime, timedelta, timezone
from pathlib import Path
from unittest.mock import patch


spec = importlib.util.spec_from_file_location(
    "ci_time", Path(__file__).with_name("check-ci-time.py")
)
ci_time = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ci_time)


class TimeBudgetTests(unittest.TestCase):
    def setUp(self):
        self.now = datetime(2026, 1, 2, tzinfo=timezone.utc)

    def check_at(self, seconds):
        run = {"run_started_at": (self.now - timedelta(seconds=seconds)).isoformat()}
        with patch.dict(os.environ, {"GITHUB_STEP_SUMMARY": ""}), contextlib.redirect_stdout(io.StringIO()):
            return ci_time.check(run, self.now)

    def test_four_minutes_passes_but_exceeding_it_fails(self):
        self.assertEqual(self.check_at(240), 0)
        self.assertEqual(self.check_at(240.1), 1)

    def test_rerun_does_not_count_time_since_original_run(self):
        run = {"created_at": "2025-01-01T00:00:00Z",
               "run_started_at": "2026-01-01T23:59:00Z"}
        self.assertEqual(ci_time.elapsed_seconds(run, self.now), 60)

    def test_queue_and_setup_time_within_attempt_are_included(self):
        self.assertEqual(self.check_at(300), 1)

    def test_invalid_timestamps_fail_instead_of_passing(self):
        for started in ["invalid", "2026-01-02T00:00:01Z", "2026-01-01T23:59:00"]:
            with self.subTest(started=started), self.assertRaises(ValueError):
                ci_time.elapsed_seconds({"run_started_at": started}, self.now)


class CompileTimeTests(unittest.TestCase):
    start = datetime(2026, 1, 1, tzinfo=timezone.utc)
    end = datetime(2026, 1, 1, 0, 10, tzinfo=timezone.utc)

    def compiled(self, *lines):
        return ci_time.compile_seconds(lines, self.start, self.end)

    def test_overlapping_builds_count_once_and_replays_not_at_all(self):
        self.assertEqual(self.compiled(
            "2026-01-01T00:01:00.0000000Z ✔ [3/9] Built A.B (30s)",
            "2026-01-01T00:01:10.0000000Z ⚠ [4/9] Built A.C (20s)",
            "2026-01-01T00:01:11.0000000Z ℹ [5/9] Replayed A.D",
            "2026-01-01T00:02:00.0000000Z ✔ [6/9] Built A.E (500ms)",
            "2026-01-01T00:03:10.0000000Z ℹ [7/9] Built A.F (1m 2.5s)",
        ), 40 + 0.5 + 62.5)

    def test_compile_time_is_reported_but_not_counted(self):
        line = "2026-01-01T00:04:00.0000000Z ✔ [1/1] Built Big (3m)"
        run = {"run_started_at": "2026-01-01T00:00:00Z"}
        now = datetime(2026, 1, 1, 0, 6, tzinfo=timezone.utc)
        with patch.dict(os.environ, {"GITHUB_STEP_SUMMARY": ""}), \
                contextlib.redirect_stdout(io.StringIO()) as out:
            self.assertEqual(ci_time.check(run, now, [line]), 0)
        self.assertIn("360.0s elapsed, of which 180.0s compiled", out.getvalue())
        with patch.dict(os.environ, {"GITHUB_STEP_SUMMARY": ""}), \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(ci_time.check(run, now), 1)

    def test_an_unknown_duration_fails_instead_of_counting_nothing(self):
        with self.assertRaises(ValueError):
            self.compiled("2026-01-01T00:01:00.0000000Z ✔ [1/1] Built A (soon)")


if __name__ == "__main__":
    unittest.main()
