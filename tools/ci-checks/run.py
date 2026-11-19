#!/usr/bin/env python3
"""Overlap two independent, post-build check phases; keep all work in make check.

The existing runtime supervisor supplies isolated temporary directories, parent-
death cleanup, and kill-before-reap process groups. A failed phase cancels its
peer; the coordinator waits for both results. Feature checks retain their order.
"""
import argparse
import concurrent.futures as cf
import ctypes
import importlib.util
import json
import os
from pathlib import Path
import signal
import sys
import threading
import time

ROOT = Path(__file__).resolve().parents[2]
MUTABLE_INPUTS = [ROOT / "silmaril/logic-graph/pending.toml"]
spec = importlib.util.spec_from_file_location("runtime_supervisor", ROOT / "tools/cerberus-runtime/check.py")
runtime = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runtime)


def capacity():
    """Bound slots by affinity and the container CPU quota, never above eight."""
    cg = Path("/sys/fs/cgroup")
    read = lambda name: (cg / name).read_text().strip() if (cg / name).exists() else None
    cpu, memory = read("cpu.max"), read("memory.max")
    slots = min(8, len(os.sched_getaffinity(0)))
    if cpu and cpu.split()[0] != "max":
        quota, period = map(int, cpu.split())
        slots = min(slots, max(1, quota // period))
    # On a smaller container retain correctness with sequential phases.
    overlap = slots >= 2 and (not memory or memory == "max" or int(memory) >= 8 * 1024**3)
    # Four simultaneous imported runtime environments plus the ELF exporter
    # exceeded the 16 GiB aggregate RSS bound in CI; retain two during overlap.
    runtime_slots = min(2, max(1, slots // 2)) if overlap else min(4, slots)
    release_slots = min(4, slots - runtime_slots) if overlap else min(4, slots)
    return {"affinity_cpus": len(os.sched_getaffinity(0)), "cpu_max": cpu,
            "memory_max": memory, "runtime_slots": runtime_slots,
            "release_slots": release_slots, "overlap": overlap}


def reap_adopted():
    """Reap descendants adopted after cancellation of a nested supervisor."""
    deadline = time.monotonic() + 5
    while True:
        try:
            pid, _ = os.waitpid(-1, os.WNOHANG)
        except ChildProcessError:
            return
        if not pid:
            if time.monotonic() > deadline:
                raise RuntimeError("check descendants did not terminate")
            time.sleep(0.02)


def process_tree_rss():
    """Conservative aggregate RSS of this coordinator and its descendants."""
    rows = {}
    for path in Path("/proc").iterdir():
        if not path.name.isdecimal():
            continue
        try:
            fields = (path / "stat").read_text().rpartition(")")[2].split()
            rows[int(path.name)] = (int(fields[1]), int(fields[21]) * os.sysconf("SC_PAGE_SIZE"))
        except (OSError, IndexError, ValueError):
            continue
    if os.getpid() not in rows:
        raise RuntimeError("cannot measure check process memory")
    descendants = {os.getpid()}
    while True:
        more = {pid for pid, (parent, _) in rows.items() if parent in descendants} - descendants
        if not more:
            return sum(rows[pid][1] for pid in descendants)
        descendants.update(more)


def run_phases(jobs, *, overlap=True, timeout=1200, runner=None):
    runner = runner or runtime.Runner(timeout=timeout)
    results = []
    with cf.ThreadPoolExecutor(2 if overlap else 1) as pool:
        pending = {}
        for name, argv in jobs:
            print("CHECK_PHASE_START " + json.dumps({"name": name, "command": argv}), flush=True)
            pending[pool.submit(runner.run, (name, argv, None, None))] = name
        try:
            for future in cf.as_completed(pending):
                row = future.result()
                results.append(row)
                if row.get("error") or row["exit"] != 0:
                    runner.cancelled.set()
                print(row["output"], end="", flush=True)
                print("CHECK_PHASE_END " + json.dumps({k: v for k, v in row.items() if k != "output"}), flush=True)
        except BaseException:
            runner.cancelled.set()
            raise
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--make", default="make")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--python", default=sys.executable)
    parser.add_argument("--targets", required=True)
    args = parser.parse_args()
    # Adopt/reap grandchildren if a cancelled phase dies before its children.
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(36, 1, 0, 0, 0) != 0:
        raise OSError(ctypes.get_errno(), "could not become child subreaper")
    limits = capacity()
    print("CHECK_CAPACITY " + json.dumps(limits), flush=True)
    runner = runtime.Runner(timeout=1200)
    for sig in (signal.SIGINT, signal.SIGTERM):
        signal.signal(sig, lambda _sig, _frame: runner.cancelled.set())
    common = [f"CHECK_TARGETS={args.targets}", f"LAKE={args.lake}", f"PYTHON={args.python}",
              f"RUNTIME_JOBS={limits['runtime_slots']}", f"RELEASE_JOBS={limits['release_slots']}"]
    jobs = [(name, [args.make, "-j1", "check-" + name, *common]) for name in ["runtime", "features"]]
    # This is actual aggregate container usage (including file cache), not a sum
    # of process RSS values that counts shared imported pages more than once.
    samples, process_samples, monitor_errors = [], [], []
    stopped = threading.Event()
    def sample():
        while not stopped.is_set():
            try:
                rss = process_tree_rss()
                process_samples.append(rss)
                if rss > 16 * 1024**3:
                    monitor_errors.append("check process tree exceeded 16 GiB aggregate RSS")
                    runner.cancelled.set()
            except RuntimeError as error:
                monitor_errors.append(str(error))
                runner.cancelled.set()
            try:
                samples.append(int(Path("/sys/fs/cgroup/memory.current").read_text()))
            except OSError:
                pass
            stopped.wait(0.2)
    # The existing logic incremental regression temporarily edits this input.
    # Restore it even when a failed peer forces cancellation before its EXIT trap.
    original_inputs = {path: path.read_bytes() for path in MUTABLE_INPUTS}
    monitor = threading.Thread(target=sample)
    monitor.start()
    started = time.monotonic()
    try:
        results = run_phases(jobs, overlap=limits["overlap"], runner=runner)
    finally:
        stopped.set()
        monitor.join()
        try:
            reap_adopted()
        finally:
            for path, data in original_inputs.items():
                if not path.exists() or path.read_bytes() != data:
                    path.write_bytes(data)
                    print("CHECK_RESTORED_INPUT " + str(path), flush=True)
    failed = bool(monitor_errors) or any(row.get("error") or row["exit"] != 0 for row in results)
    print("CHECK_PHASES " + json.dumps({"seconds": round(time.monotonic() - started, 3),
          "cpu_seconds": round(sum(row.get("cpu_seconds", 0) for row in results), 3),
          "peak_container_memory_bytes": max(samples, default=None),
          "peak_process_tree_rss_bytes": max(process_samples, default=None),
          "resource_errors": monitor_errors, "failed": failed}), flush=True)
    return 130 if runner.cancelled.is_set() else int(failed)


if __name__ == "__main__":
    sys.exit(main())
