#!/usr/bin/env python3
"""Check replay scheduling and compare the driver to the pinned stock checker."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time
import unittest

DRIVER = Path(__file__).resolve().parents[1] / "Replay.lean"
REPLAY = DRIVER.with_name("replay.sh")


class ReplaySchedulerTests(unittest.TestCase):
    longest = "CompilesToExamples.Explorer.C2C.Runs"
    modules = [f"Fixture.Module{i}" for i in range(17)] + [longest]

    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        lake = self.root / "lake"
        lake.write_text('''#!/usr/bin/env python3
import os
from pathlib import Path
import time

module = os.environ.get("SILMARIL_REPLAY_MODULE")
if module is None:
    print(os.environ["REPLAY_FIXTURES"])
    raise SystemExit(0)

root = Path(os.environ["REPLAY_TEST_ROOT"])

def record(event):
    with (root / "events").open("ab", buffering=0) as file:
        file.write(f"{event} {module}\\n".encode())

record("start")
if os.environ.get("REPLAY_TEST_GATED"):
    gate = root / ("longest" if module == os.environ["REPLAY_TEST_LONGEST"] else "others")
    deadline = time.monotonic() + 15
    while not gate.exists():
        if time.monotonic() >= deadline:
            raise SystemExit("worker gate timed out")
        time.sleep(0.01)
record("finish")
if module == os.environ.get("REPLAY_TEST_FAIL"):
    raise SystemExit(255)
''')
        lake.chmod(0o755)
        self.env = {**os.environ, "LAKE": str(lake), "REPLAY_FIXTURES": "\n".join(self.modules),
                    "REPLAY_TEST_ROOT": str(self.root), "REPLAY_TEST_LONGEST": self.longest}

    def events(self):
        path = self.root / "events"
        return [tuple(line.split()) for line in path.read_text().splitlines()] if path.exists() else []

    def wait_for_events(self, event, count):
        deadline = time.monotonic() + 10
        while time.monotonic() < deadline:
            if sum(kind == event for kind, _ in self.events()) >= count:
                return
            time.sleep(0.01)
        self.fail(f"Expected {count} {event} events, got {self.events()}")

    def run_replay(self, jobs, **overrides):
        env = {**self.env, "LEAN_REPLAY_JOBS": jobs, **overrides}
        return subprocess.run([REPLAY], env=env, text=True, capture_output=True, timeout=20)

    def test_serial_order_and_coverage(self):
        result = self.run_replay("1")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.events(), [(kind, module)
                                         for module in [self.longest, *self.modules[:-1]]
                                         for kind in ("start", "finish")])

    def test_worker_limit_is_clamped_to_queue_size(self):
        modules = [*self.modules[:7], self.longest]
        xargs = self.root / "xargs"
        xargs.write_text('''#!/usr/bin/env bash
printf '%s\\n' "$@" > "$REPLAY_TEST_ROOT/xargs-args"
exec "$REPLAY_REAL_XARGS" "$@"
''')
        xargs.chmod(0o755)
        env = {"PATH": f"{self.root}:{os.environ.get('PATH', os.defpath)}",
               "REPLAY_REAL_XARGS": shutil.which("xargs")}
        limits = (("4", "4"), ("8", "8"), ("9", "8"), ("2147483648", "8"),
                  ("18446744073709551616", "8"), ("9" * 80, "8"))
        for jobs, expected in limits:
            with self.subTest(jobs=jobs):
                (self.root / "events").unlink(missing_ok=True)
                result = self.run_replay(jobs, REPLAY_FIXTURES="\n".join(modules), **env)
                self.assertEqual(result.returncode, 0, result.stderr)
                args = (self.root / "xargs-args").read_text().splitlines()
                self.assertEqual(args[args.index("-P") + 1], expected)
                self.assertCountEqual(self.events(), [(kind, module) for module in modules
                                                       for kind in ("start", "finish")])

    def test_one_module(self):
        module = self.modules[0]
        result = self.run_replay("4", REPLAY_FIXTURES=module)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.events(), [("start", module), ("finish", module)])

    def test_empty_selection_fails_before_starting_workers(self):
        result = self.run_replay("2147483648", REPLAY_FIXTURES="")
        self.assertEqual(result.returncode, 1)
        self.assertEqual(result.stderr.strip(), "kernel replay selected no modules")
        self.assertFalse(self.events())

    def test_leading_zero_is_invalid(self):
        result = self.run_replay("08")
        self.assertEqual(result.returncode, 1)
        self.assertIn("LEAN_REPLAY_JOBS must be a positive integer", result.stderr)
        self.assertFalse(self.events())

    def test_refills_within_cap_and_joins_all_workers(self):
        env = {**self.env, "LEAN_REPLAY_JOBS": "4", "REPLAY_TEST_GATED": "1"}
        others = self.root / "others"
        longest = self.root / "longest"
        with subprocess.Popen([REPLAY], env=env, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE) as process:
            try:
                self.wait_for_events("start", 4)
                self.assertCountEqual((module for _, module in self.events()),
                                      [self.longest, *self.modules[:3]])
                others.touch()
                self.wait_for_events("finish", 17)
                self.assertIsNone(process.poll())
            finally:
                others.touch()
                longest.touch()
                _, stderr = process.communicate(timeout=20)
        self.assertEqual(process.returncode, 0, stderr)
        active = set()
        finished = []
        for kind, module in self.events():
            if kind == "start":
                self.assertNotIn(module, active)
                active.add(module)
                self.assertLessEqual(len(active), 4)
            else:
                active.remove(module)
                finished.append(module)
        self.assertFalse(active)
        self.assertCountEqual(finished, self.modules)

    def test_failure_reports_exit_status_and_keeps_running(self):
        failed = self.modules[0]
        result = self.run_replay("4", REPLAY_TEST_FAIL=failed)
        self.assertEqual(result.returncode, 1)
        self.assertIn(f"kernel replay {failed} failed (exit 255)", result.stderr)
        self.assertNotIn(f"kernel replay {failed}:", result.stdout)
        self.assertCountEqual((module for kind, module in self.events() if kind == "finish"),
                              self.modules)


class KernelReplayTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lean = shutil.which("lean")
        if not cls.lean:
            raise RuntimeError("run with the pinned Lean toolchain, e.g. lake env python3")
        prefix = subprocess.check_output([cls.lean, "--print-prefix"], text=True).strip()
        cls.checker = str(Path(prefix) / "bin" / "leanchecker")

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.env = {**os.environ, "LEAN_PATH": str(self.root), "LEAN_NUM_THREADS": "2"}
        self.env.pop("SILMARIL_REPLAY_MODULE", None)
        self.env.pop("SILMARIL_REPLAY_TARGETS", None)
        self.build("Group", "module\n@[expose] public section\ntheorem good : True := True.intro\n")
        self.build("Group.Child", "module\npublic import Group\n"
                   "@[expose] public section\ntheorem child : True := good\n")

    def call(self, args, env=None):
        return subprocess.run(args, env=env or self.env, cwd=self.root,
                              text=True, capture_output=True, timeout=60)

    def build(self, name, text):
        path = self.root.joinpath(*name.split(".")).with_suffix(".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        result = self.call([self.lean, "-DwarningAsError=true", "-o",
                            str(path.with_suffix(".olean")), str(path)])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def driver(self, **mode):
        return self.call([self.lean, "-DwarningAsError=true", str(DRIVER)],
                         {**self.env, **mode})

    def test_target_and_descendant_selection_matches_stock(self):
        stock = self.call([self.checker, "--verbose", "Group", "Group.Child"])
        self.assertEqual(stock.returncode, 0, stock.stdout + stock.stderr)
        expected = {line.removeprefix("replaying ") for line in stock.stdout.splitlines()
                    if line.startswith("replaying ")}
        selected = self.driver(SILMARIL_REPLAY_TARGETS="Group Group.Child")
        self.assertEqual(selected.returncode, 0, selected.stdout + selected.stderr)
        names = selected.stdout.splitlines()
        self.assertEqual(set(names), {"Group", "Group.Child"})
        self.assertEqual(set(names), expected)
        self.assertEqual(len(names), len(set(names)))
        for name in names:
            result = self.driver(SILMARIL_REPLAY_MODULE=name)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_unknown_and_corrupt_modules_fail_closed(self):
        (self.root / "Corrupt.olean").write_bytes(b"not an olean")
        for name in ("Unknown", "Corrupt"):
            stock = self.call([self.checker, name])
            replay = self.driver(SILMARIL_REPLAY_MODULE=name)
            self.assertNotEqual(stock.returncode, 0)
            self.assertNotEqual(replay.returncode, 0)
            self.assertNotIn(": ok", replay.stdout)
        selected = self.driver(SILMARIL_REPLAY_TARGETS="Group Unknown")
        self.assertNotEqual(selected.returncode, 0)
        empty = self.driver(SILMARIL_REPLAY_TARGETS="")
        self.assertNotEqual(empty.returncode, 0)

    def test_malformed_proof_rejected_by_both_kernels(self):
        # Deliberately bypass declaration checking ONLY to manufacture a negative
        # fixture in a temporary directory; neither replay may accept this proof.
        self.build("Bad", '''import Lean
open Lean Elab Command in
run_cmd do
  let decl := Declaration.thmDecl {
    name := `badReplayFixture
    levelParams := []
    type := mkConst ``False
    value := mkConst ``True.intro
  }
  match (← getEnv).addDeclCore 0 1000 decl none false with
  | .ok env => setEnv env
  | .error e => throwError "{e.toMessageData {}}"
''')
        for result in (self.call([self.checker, "Bad"]),
                       self.driver(SILMARIL_REPLAY_MODULE="Bad")):
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("declaration type mismatch", result.stdout + result.stderr)
            self.assertNotIn(": ok", result.stdout)
        # Stock normal mode loads imports, without replaying their declarations.
        self.build("LoadsBad", "import Bad\ntheorem stillTrue : True := True.intro\n")
        for result in (self.call([self.checker, "LoadsBad"]),
                       self.driver(SILMARIL_REPLAY_MODULE="LoadsBad")):
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
