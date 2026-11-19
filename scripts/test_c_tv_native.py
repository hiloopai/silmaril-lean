"""The capped native runner of the C TV scripts (scripts/c-tv/torture.py: launch, run_native), from
the review of #950 (00260e8f): the wall-clock deadline covers the whole lifecycle (a program that
closes its outputs and sleeps or pauses is stopped), the process group is killed after a normal
end too (children do not survive), limits are applied by an exec wrapper (the runner calls it from
worker threads), CPU and file-size limits are reported as such with their signal, outputs are
capped, and tool runs are bounded the same way. Needs a C compiler; skipped without one."""
import concurrent.futures as cf
import importlib.util
import os
import shutil
import subprocess
import tempfile
import time
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("ctv_torture", os.path.join(HERE, "c-tv", "torture.py"))
T = importlib.util.module_from_spec(spec)
spec.loader.exec_module(T)

PROGRAMS = {
    "close_sleep": "#include <unistd.h>\nint main(void) { close(1); close(2); sleep(6); return 0; }\n",
    "pause": "#include <unistd.h>\nint main(void) { close(1); close(2); pause(); return 0; }\n",
    "fork_child": "#include <unistd.h>\nint main(void) { if (fork() == 0) { close(1); close(2); sleep(30); return 0; } return 7; }\n",
    "fork_keep": "#include <unistd.h>\nint main(void) { if (fork() == 0) { sleep(30); return 0; } return 8; }\n",
    "cpu": "int main(void) { volatile unsigned long x = 0; for (;;) x++; }\n",
    "fsize": "#include <stdio.h>\nint main(void) { FILE *f = fopen(\"big.bin\", \"w\"); static char b[65536]; for (;;) fwrite(b, 1, sizeof b, f); }\n",
    "spam": "#include <stdio.h>\nint main(void) { for (;;) puts(\"xxxxxxxxxxxxxxxx\"); }\n",
    "errspam": "#include <stdio.h>\nint main(void) { for (;;) fputs(\"eeeeeeeeeeeeeeee\\n\", stderr); }\n",
    "seg": "int main(void) { return *(volatile int *)0; }\n",
    "hello": "#include <stdio.h>\nint main(void) { puts(\"hi\"); return 3; }\n",
}
EXPECT = {
    "close_sleep": ("timeout", None), "pause": ("timeout", None), "fork_child": ("exit", 7),
    "fork_keep": ("exit", 8), "cpu": ("cpu-limit", 24), "fsize": ("fsize-limit", 25),
    "spam": ("stdout-limit", None), "errspam": ("stderr-limit", None), "seg": ("signal", 11),
    "hello": ("exit", 3),
}


@unittest.skipUnless(shutil.which("gcc") or shutil.which("cc"), "no C compiler")
class NativeRunner(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dir = tempfile.mkdtemp(prefix="ctv-native-")
        cc = shutil.which("gcc") or shutil.which("cc")
        for name, src in PROGRAMS.items():
            path = os.path.join(cls.dir, name + ".c")
            open(path, "w").write(src)
            subprocess.run([cc, "-O0", "-w", path, "-o", os.path.join(cls.dir, name)], check=True)
        T.NATIVE.update(timeoutSeconds=2, cpuSeconds=1)

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir, ignore_errors=True)

    def test_endings_from_worker_threads(self):
        def one(name):
            t = time.monotonic()
            res, out = T.run_native(os.path.join(self.dir, name), self.dir)
            return name, res, out, time.monotonic() - t
        with cf.ThreadPoolExecutor(8) as ex:
            for name, res, out, took in ex.map(one, sorted(PROGRAMS)):
                self.assertEqual((res["ended"], res["code"]), EXPECT[name], (name, res))
                self.assertLess(took, 2 + 3, (name, took))
                self.assertTrue(res["groupGone"], (name, res))
        self.assertEqual(T.run_native(os.path.join(self.dir, "hello"), self.dir)[1], b"hi\n")

    def test_children_do_not_survive(self):
        res, _ = T.run_native(os.path.join(self.dir, "fork_keep"), self.dir)
        self.assertTrue(res["groupKilledAfterEnd"], res)
        self.assertTrue(res["groupGone"], res)

    def test_launch_failures_are_not_exits(self):
        # Missing, non-executable, not an executable format: the program never ran.
        open(os.path.join(self.dir, "notexec"), "w").write("x")
        open(os.path.join(self.dir, "badelf"), "wb").write(b"\x7fELFgarbage")
        os.chmod(os.path.join(self.dir, "badelf"), 0o755)
        for name in ("missing", "notexec", "badelf"):
            res, _ = T.run_native(os.path.join(self.dir, name), self.dir)
            self.assertEqual(res["ended"], "launch-failed", (name, res))
            self.assertIn("Error", res["launchError"], (name, res))
        # A limit the wrapper cannot set (as when a hard limit is below the requested one and the
        # runner is unprivileged; simulated with a value setrlimit cannot take).
        res, _, _ = T.launch([os.path.join(self.dir, "hello")], self.dir, 5, 1 << 20, 1 << 20, limits=(1, "not-a-number", 1 << 20))
        self.assertEqual(res["ended"], "launch-failed", res)
        self.assertEqual(T.run(["/nonexistent/tool"], self.dir, 5)[0], "launch-failed")

    def test_tool_runs_are_bounded(self):
        t = time.monotonic()
        rc, _, _ = T.run(["sh", "-c", "sleep 30 & sleep 30"], self.dir, 1)
        self.assertEqual(rc, "timeout")
        self.assertLess(time.monotonic() - t, 4)
        old = T.TOOL_STDOUT_BYTES
        T.TOOL_STDOUT_BYTES = 1 << 20
        try:
            self.assertEqual(T.run([os.path.join(self.dir, "spam")], self.dir, 5)[0], "output-limit")
        finally:
            T.TOOL_STDOUT_BYTES = old
        self.assertEqual(T.run(["sh", "-c", "echo out; echo err >&2; exit 5"], self.dir, 5), (5, b"out\n", b"err\n"))


if __name__ == "__main__":
    unittest.main()
