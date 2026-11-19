#!/usr/bin/env python3
"""Run the existing Cerberus regressions in at most four isolated command slots.

Only the two large array-item tests are partitioned, by their three original seeds.
Every shard must report its exact seed and completed case count. Kernel compilation
remains in `make check` before this runner; all runtime work stays inside that check.
"""
import argparse
import concurrent.futures as cf
import ctypes
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import threading
import time

ROOT = Path(__file__).resolve().parents[2]
PREFIX = "CERBERUS_SHARD "
EXPECTED = {"core": 56, "machine": 140}
SHARDED = {"CjsonArrayItemContext.lean": "core", "CjsonArrayItemMachine.lean": "machine"}


def validate_output(text, suite, seed):
    records = [json.loads(line[len(PREFIX):]) for line in text.splitlines() if line.startswith(PREFIX)]
    expected = {"schema": "silmaril.cerberus.runtime-shard/1", "suite": suite,
                "seeds": [seed], "cases": EXPECTED[suite]}
    if records != [expected]:
        raise ValueError(f"coverage mismatch: expected {expected}, got {records}")
    return records[0]


def validate_coverage(records):
    for suite, count in EXPECTED.items():
        rows = [row for row in records if row["suite"] == suite]
        if (sorted(row["seeds"] for row in rows) != [[0], [1], [2]] or
                any(row["cases"] != count for row in rows)):
            raise ValueError(f"missing, duplicate or incorrect {suite} shard coverage")
    if len(records) != 6:
        raise ValueError("expected exactly six shard reports")


def plan(lake, python):
    checks = json.loads((ROOT / "tests/cerberus/runtime-checks.json").read_text())
    jobs, shards = [], []
    for kind, path in checks:
        if kind not in {"python", "lean", "lean-run"}:
            raise ValueError(f"unknown runtime command kind: {kind}")
        argv = ([python, "-I", path] if kind == "python" else
                [lake, "env", "lean", "-DwarningAsError=true", *(["--run"] if kind == "lean-run" else []), path])
        suite = SHARDED.get(Path(path).name)
        if suite:
            if kind != "lean-run":
                raise ValueError("a shard must run the original Lean test")
            shards.extend((f"{suite}-{seed}", argv + ["--seed", str(seed)], suite, seed) for seed in range(3))
        else:
            jobs.append((Path(path).stem, argv, None, None))
    if len(checks) != 32 or len(shards) != 6 or len({job[0] for job in jobs + shards}) != 36:
        raise ValueError("the runtime manifest must retain all 32 checks and exactly six distinct shards")
    # The long commands start first; shorter existing checks fill free slots.
    return shards + jobs


def supervise(parent, argv):
    """Keep a command in this supervisor's group, killed if its harness dies.

    This fresh, single-threaded process installs the Linux parent-death signal;
    the threaded harness never uses preexec_fn. Descendants starting their own
    sessions are outside this contract; these repository checks do not do so.
    """
    def terminate(_signal, _frame):
        os.killpg(os.getpgrp(), signal.SIGKILL)
    signal.signal(signal.SIGTERM, terminate)
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(1, signal.SIGTERM, 0, 0, 0) != 0:
        raise OSError(ctypes.get_errno(), "could not install parent-death signal")
    if os.getppid() != parent:
        terminate(None, None)
    child = subprocess.Popen(argv, stdin=subprocess.DEVNULL)
    return child.wait()


class Runner:
    def __init__(self, timeout=240):
        self.timeout = timeout
        self.cancelled = threading.Event()

    def run(self, job):
        name, argv, suite, seed = job
        started = time.monotonic()
        result = {"name": name, "command": argv, "exit": None, "coverage": None}
        if self.cancelled.is_set():
            return result | {"error": "cancelled", "output": "", "seconds": 0}
        with tempfile.TemporaryDirectory(prefix="cerberus-runtime-") as scratch:
            output = Path(scratch) / "output.log"
            env = dict(os.environ, TMPDIR=scratch, LEAN_NUM_THREADS="1")
            with output.open("wb") as log:
                try:
                    p = subprocess.Popen([sys.executable, "-I", __file__, "--supervise", str(os.getpid()), *argv],
                                         cwd=ROOT, env=env, stdin=subprocess.DEVNULL,
                                         stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
                except OSError as error:
                    return result | {"error": f"launch failed: {error}", "output": "", "seconds": 0}
                try:
                    while True:
                        # Observe without reaping: the group ID cannot be reused before its kill.
                        ended = os.waitid(os.P_PID, p.pid, os.WEXITED | os.WNOHANG | os.WNOWAIT)
                        if ended is not None:
                            break
                        if self.cancelled.is_set():
                            result["error"] = "cancelled"
                            break
                        if time.monotonic() - started >= self.timeout:
                            result["error"] = "timeout"
                            break
                        if output.stat().st_size > 16 * 1024 * 1024:
                            result["error"] = "output exceeded 16 MiB"
                            break
                        time.sleep(0.05)
                finally:
                    # Also removes children left after a normal leader exit, before reaping it.
                    try:
                        os.killpg(p.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    _, status, usage = os.wait4(p.pid, 0)
                    p.returncode = os.waitstatus_to_exitcode(status)
                    result.update(exit=p.returncode, cpu_seconds=round(usage.ru_utime + usage.ru_stime, 3))
            result["output"] = output.read_text(errors="replace")
        result["seconds"] = round(time.monotonic() - started, 3)
        if result["exit"] != 0:
            result.setdefault("error", f"child exited {result['exit']}")
        if "error" not in result and suite:
            try:
                result["coverage"] = validate_output(result["output"], suite, seed)
            except (ValueError, TypeError, KeyError) as error:
                result["error"] = str(error)
        return result


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--supervise":
        return supervise(int(sys.argv[2]), sys.argv[3:])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--python", default=sys.executable)
    parser.add_argument("--jobs", type=int, choices=range(1, 5), default=4)
    args = parser.parse_args()
    runner = Runner()
    for sig in (signal.SIGINT, signal.SIGTERM):
        signal.signal(sig, lambda _sig, _frame: runner.cancelled.set())
    started = time.monotonic()
    with cf.ThreadPoolExecutor(args.jobs) as pool:
        try:
            results = list(pool.map(runner.run, plan(args.lake, args.python)))
        except BaseException:
            runner.cancelled.set()
            raise
    for row in results:
        print(f"runtime {row['name']}: {row.get('error', 'pass')} ({row['seconds']}s)")
        print(row["output"], end="" if row["output"].endswith("\n") else "\n")
    records = [row["coverage"] for row in results if row["coverage"]]
    failed = runner.cancelled.is_set() or any("error" in row for row in results)
    try:
        validate_coverage(records)
    except ValueError as error:
        print(error)
        failed = True
    summary = {"jobs": args.jobs, "commands": len(results), "seconds": round(time.monotonic() - started, 3),
               "cpu_seconds": round(sum(row.get("cpu_seconds", 0) for row in results), 3),
               "core_cases": sum(row["cases"] for row in records if row["suite"] == "core"),
               "machine_cases": sum(row["cases"] for row in records if row["suite"] == "machine"),
               "failed": failed}
    print("CERBERUS_RUNTIME " + json.dumps(summary), flush=True)
    return 130 if runner.cancelled.is_set() else int(failed)


if __name__ == "__main__":
    sys.exit(main())
