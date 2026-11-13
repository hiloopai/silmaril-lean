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


def job(name, started, completed, conclusion="success"):
    return {"name": name, "started_at": started, "completed_at": completed,
            "conclusion": conclusion}


def quiet(call, *args):
    with patch.dict(os.environ, {"GITHUB_STEP_SUMMARY": ""}), \
            contextlib.redirect_stdout(io.StringIO()) as out:
        return call(*args), out.getvalue()


class TimeBudgetTests(unittest.TestCase):
    attempt = {"run_started_at": "2026-01-01T00:00:00Z"}
    now = datetime(2026, 1, 1, 0, 10, tzinfo=timezone.utc)

    def check(self, *jobs):
        return quiet(ci_time.check, self.attempt, list(jobs), self.now)

    def test_four_minutes_of_running_jobs_passes_but_exceeding_it_fails(self):
        self.assertEqual(self.check(job("a", "2026-01-01T00:00:00Z", "2026-01-01T00:04:00Z"))[0], 0)
        self.assertEqual(self.check(job("a", "2026-01-01T00:00:00Z", "2026-01-01T00:04:01Z"))[0], 1)

    def test_waiting_for_a_runner_does_not_count(self):
        # main after #93 (run 43357817902): `lean / check` waited 213 s for a 16-vCPU runner.
        run = {"run_started_at": "2026-11-13T03:16:11Z"}
        jobs = [job("changes", "2026-11-13T03:16:13Z", "2026-11-13T03:16:23Z"),
                job("helpers / helpers", "2026-11-13T03:16:14Z", "2026-11-13T03:16:25Z"),
                job("rust", "2026-11-13T03:16:23Z", "2026-11-13T03:16:23Z", "skipped"),
                job("lean / check", "2026-11-13T03:19:56Z", "2026-11-13T03:25:24Z"),
                job("CI", "2026-11-13T03:25:26Z", "2026-11-13T03:25:28Z"),
                {"name": "CI time budget / budget", "started_at": "2026-11-13T03:25:30Z",
                 "completed_at": None, "conclusion": None}]
        now = datetime(2026, 11, 13, 3, 25, 40, tzinfo=timezone.utc)
        status, out = quiet(ci_time.check, run, jobs, now)
        self.assertIn("352.0s with a job running (215.0s with none", out)
        self.assertEqual(status, 1)

    def test_parallel_jobs_count_once(self):
        self.assertEqual(ci_time.union_seconds(ci_time.running_intervals(self.attempt, [
            job("a", "2026-01-01T00:00:00Z", "2026-01-01T00:02:00Z"),
            job("b", "2026-01-01T00:01:00Z", "2026-01-01T00:03:00Z"),
            job("c", "2026-01-01T00:05:00Z", "2026-01-01T00:06:00Z"),
        ], self.now)), 240)

    def test_a_rerun_leaves_out_jobs_from_earlier_attempts(self):
        retained = job("old", "2025-12-31T23:00:00Z", "2025-12-31T23:30:00Z")
        self.assertEqual(ci_time.running_intervals(self.attempt, [retained], self.now), [])
        with self.assertRaises(ValueError):
            self.check(retained)

    def test_invalid_timestamps_fail_instead_of_passing(self):
        for started in ["invalid", "2026-01-01T00:11:00Z", "2026-01-01T00:01:00"]:
            with self.subTest(started=started), self.assertRaises(ValueError):
                ci_time.running_intervals(self.attempt, [job("a", started, None)], self.now)


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
        jobs = [job("lean", "2026-01-01T00:00:00Z", "2026-01-01T00:06:00Z")]
        now = datetime(2026, 1, 1, 0, 6, tzinfo=timezone.utc)
        status, out = quiet(ci_time.check, run, jobs, now, [line])
        self.assertEqual(status, 0)
        self.assertIn("360.0s with a job running", out)
        self.assertIn("of which 180.0s compiled", out)
        self.assertEqual(quiet(ci_time.check, run, jobs, now)[0], 1)

    def test_an_unknown_duration_fails_instead_of_counting_nothing(self):
        with self.assertRaises(ValueError):
            self.compiled("2026-01-01T00:01:00.0000000Z ✔ [1/1] Built A (soon)")


if __name__ == "__main__":
    unittest.main()
