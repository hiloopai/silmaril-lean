"""Fail-closed coverage and process-lifecycle checks for Cerberus runtime shards."""
import importlib.util
import concurrent.futures as cf
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
import time
import unittest

spec = importlib.util.spec_from_file_location("cerberus_runtime", Path(__file__).resolve().parents[1] / "tools/cerberus-runtime/check.py")
R = importlib.util.module_from_spec(spec)
spec.loader.exec_module(R)


def record(suite="core", seed=0, cases=56):
    return {"schema": "silmaril.cerberus.runtime-shard/1", "suite": suite, "seeds": [seed], "cases": cases}


class RuntimeShards(unittest.TestCase):
    def test_missing_seed_and_duplicate_reports_are_rejected(self):
        with self.assertRaises(ValueError):
            R.validate_output("PASS56\n", "core", 0)
        line = R.PREFIX + json.dumps(record()) + "\n"
        with self.assertRaises(ValueError):
            R.validate_output(line * 2, "core", 0)
        rows = [record(suite, seed, n) for suite, n in R.EXPECTED.items() for seed in range(3)]
        R.validate_coverage(rows)
        with self.assertRaises(ValueError):
            R.validate_coverage(rows[:-1])
        with self.assertRaises(ValueError):
            R.validate_coverage(rows + rows[:1])

    def test_count_and_seed_mismatch_are_rejected(self):
        for value in [record(cases=55), record(seed=1), record(cases=168), record(suite="machine")]:
            with self.assertRaises(ValueError):
                R.validate_output(R.PREFIX + json.dumps(value), "core", 0)

    def test_manifest_commands_and_seed_partitions_remain(self):
        jobs = R.plan("lake", sys.executable)
        self.assertEqual(len(jobs), 36)
        for suite in R.EXPECTED:
            self.assertEqual([job[3] for job in jobs if job[2] == suite], [0, 1, 2])
        manifest = json.loads((R.ROOT / "tests/cerberus/runtime-checks.json").read_text())
        self.assertEqual(len(manifest), 32)
        self.assertEqual({row[1] for row in manifest},
                         {arg for job in jobs for arg in job[1] if arg.endswith((".lean", ".py"))})

    def test_child_failure_is_not_a_pass(self):
        result = R.Runner().run(("negative", [sys.executable, "-c", "raise SystemExit(7)"], None, None))
        self.assertEqual(result["exit"], 7)
        self.assertIn("error", result)

    def test_parallel_commands_have_isolated_temporary_artifacts(self):
        code = "import os,pathlib; p=pathlib.Path(os.environ['TMPDIR'])/'artifact'; p.write_text('ok'); print(p)"
        jobs = [(str(i), [sys.executable, "-c", code], None, None) for i in range(4)]
        with cf.ThreadPoolExecutor(4) as pool:
            rows = list(pool.map(R.Runner().run, jobs))
        self.assertTrue(all("error" not in row for row in rows))
        self.assertEqual(len({row["output"].strip() for row in rows}), 4)
        self.assertTrue(all(not Path(row["output"].strip()).exists() for row in rows))

    def test_timeout_and_cancellation_reap_children(self):
        job = ("blocking", [sys.executable, "-c", "import time;time.sleep(30)"], None, None)
        result = R.Runner(timeout=0.2).run(job)
        self.assertEqual(result["error"], "timeout")
        runner = R.Runner()
        rows = []
        thread = threading.Thread(target=lambda: rows.append(runner.run(job)))
        thread.start()
        time.sleep(0.2)
        runner.cancelled.set()
        thread.join(3)
        self.assertFalse(thread.is_alive())
        self.assertEqual(rows[0]["error"], "cancelled")

    def test_parent_death_kills_the_workload_group(self):
        with tempfile.TemporaryDirectory() as scratch:
            pidfile = Path(scratch) / "pid"
            code = f"import os,time,pathlib;pathlib.Path({str(pidfile)!r}).write_text(str(os.getpid()));time.sleep(30)"
            parent_code = (
                "import subprocess,sys,os,time;"
                f"subprocess.Popen([sys.executable,'-I',{str(R.ROOT / 'tools/cerberus-runtime/check.py')!r},"
                f"'--supervise',str(os.getpid()),sys.executable,'-c',{code!r}],start_new_session=True);time.sleep(30)"
            )
            parent = subprocess.Popen([sys.executable, "-c", parent_code])
            try:
                deadline = time.monotonic() + 5
                while not pidfile.exists() and time.monotonic() < deadline:
                    time.sleep(0.02)
                self.assertTrue(pidfile.exists())
                pid = int(pidfile.read_text())
                parent.kill()
                parent.wait()
                while time.monotonic() < deadline:
                    stat = Path(f"/proc/{pid}/stat")
                    if not stat.exists() or stat.read_text().rpartition(")")[2].split()[0] == "Z":
                        break
                    time.sleep(0.02)
                else:
                    self.fail("workload survived its harness's death")
            finally:
                if parent.poll() is None:
                    parent.kill()
                    parent.wait()


if __name__ == "__main__":
    unittest.main()
