"""Real process-tree failures, cancellation, and allocation of post-build phases."""
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("check_phases", ROOT / "tools/ci-checks/run.py")
P = importlib.util.module_from_spec(spec)
spec.loader.exec_module(P)


class CheckPhases(unittest.TestCase):
    def test_allocation_respects_cpu_budget(self):
        c = P.capacity()
        self.assertLessEqual(c["runtime_slots"], 4)
        self.assertLessEqual(c["release_slots"], 4)
        self.assertGreaterEqual(min(c["runtime_slots"], c["release_slots"]), 1)
        if c["overlap"]:
            self.assertLessEqual(c["runtime_slots"] + c["release_slots"], 8)

    def launch(self, root, fail="", block=False):
        (root / "pending.toml").write_text("original input\n")
        fake = root / "make"
        fake.write_text(f"#!{sys.executable}\n" + '''import os,sys,time,subprocess,json
from pathlib import Path
root=Path(os.environ['PHASE_TEST_ROOT'])
name=next(a for a in sys.argv if a.startswith('check-'))[6:]
if name=='features': (root/'pending.toml').write_text('temporary incremental probe\\n')
child=subprocess.Popen([sys.executable,'-c','import time;time.sleep(30)'])
(root/(name+'.json')).write_text(json.dumps([os.getpid(),child.pid]))
deadline=time.monotonic()+5
while not all((root/(n+'.json')).exists() for n in ['runtime','features']):
 if time.monotonic()>deadline: raise SystemExit(9)
 time.sleep(.01)
if os.environ.get('PHASE_TEST_FAIL')==name: raise SystemExit(7)
if os.environ.get('PHASE_TEST_BLOCK')=='1': time.sleep(30)
''')
        fake.chmod(0o755)
        # Two sleeping fixture phases, even on a one-CPU helper runner. The
        # production allocation function is tested separately above.
        bootstrap = (f"import importlib.util,sys; s=importlib.util.spec_from_file_location('p',{str(ROOT / 'tools/ci-checks/run.py')!r});"
                     "p=importlib.util.module_from_spec(s);s.loader.exec_module(p);"
                     f"p.MUTABLE_INPUTS=[__import__('pathlib').Path({str(root / 'pending.toml')!r})];"
                     "p.capacity=lambda:dict(overlap=True,runtime_slots=1,release_slots=1);sys.exit(p.main())")
        return subprocess.Popen([sys.executable, "-c", bootstrap, "--make", str(fake), "--targets", ""],
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                                env=dict(os.environ, PHASE_TEST_ROOT=str(root), PHASE_TEST_FAIL=fail,
                                         PHASE_TEST_BLOCK="1" if block else "0"))

    def assert_stopped(self, root, restored=True):
        deadline = time.monotonic() + 3
        for name in ["runtime", "features"]:
            for pid in json.loads((root / (name + ".json")).read_text()):
                while True:
                    stat = Path(f"/proc/{pid}/stat")
                    try:
                        state = stat.read_text().rpartition(")")[2].split()[0]
                    except (FileNotFoundError, ProcessLookupError):
                        break
                    if state == "Z":
                        break
                    if time.monotonic() > deadline:
                        self.fail(f"phase descendant {pid} survived")
                    time.sleep(0.02)
        if restored:
            self.assertEqual((root / "pending.toml").read_text(), "original input\n")

    def test_both_phases_complete_and_normal_orphans_are_removed(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            p = self.launch(root)
            output, _ = p.communicate(timeout=8)
            self.assertEqual(p.returncode, 0, output)
            self.assertEqual(output.count("CHECK_PHASE_END "), 2)
            self.assertIn('"failed": false', output)
            self.assert_stopped(root)

    def test_either_failure_cancels_peer_and_cannot_be_masked(self):
        for name in ["runtime", "features"]:
            with self.subTest(phase=name), tempfile.TemporaryDirectory() as d:
                root = Path(d)
                p = self.launch(root, fail=name, block=True)
                output, _ = p.communicate(timeout=8)
                self.assertNotEqual(p.returncode, 0, output)
                self.assertEqual(output.count("CHECK_PHASE_END "), 2)
                self.assertIn('"failed": true', output)
                self.assert_stopped(root)

    def test_signal_and_parent_death_remove_both_phase_trees(self):
        for sig in [signal.SIGTERM, signal.SIGKILL]:
            with self.subTest(signal=sig), tempfile.TemporaryDirectory() as d:
                root = Path(d)
                p = self.launch(root, block=True)
                try:
                    deadline = time.monotonic() + 5
                    while not all((root / (n + ".json")).exists() for n in ["runtime", "features"]):
                        self.assertLess(time.monotonic(), deadline)
                        time.sleep(0.02)
                    p.send_signal(sig)
                    output, _ = p.communicate(timeout=8)
                    self.assertNotEqual(p.returncode, 0, output)
                    self.assert_stopped(root, restored=sig != signal.SIGKILL)
                finally:
                    if p.poll() is None:
                        p.kill()
                        p.communicate()

    def test_timeout_does_not_leave_a_successful_peer_result(self):
        command = [sys.executable, "-c", "import time;time.sleep(30)"]
        rows = P.run_phases([("runtime", command), ("features", command)], timeout=0.2)
        self.assertEqual(len(rows), 2)
        self.assertTrue(all(row["exit"] != 0 and row.get("error") for row in rows))


if __name__ == "__main__":
    unittest.main()
