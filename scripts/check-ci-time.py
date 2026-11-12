#!/usr/bin/env python3
"""Fail a separate timing check after the correctness jobs finish.

Time Lake spends compiling modules the run had to build does not count: a pull
request that adds a lot of new proof is not slow CI. Restores, no-op Lake walks,
setup and checks still count. The compile time is read from Lake's job lines in
the run's job logs (`✔ [12/40] Built Foo.Bar (13s)`): each line ends a job that
took the stated time, so the job ran over [line time - duration, line time]. The
union of those intervals across all jobs is the wall time spent compiling.
"""

import json
import os
import re
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path


LIMIT_SECONDS = 240
# GitHub prefixes every log line with its time; Lake's symbol shows the job's log level.
BUILT = re.compile(r"^(\S+Z) (?:\x1b\[[0-9;]*m)*[✔⚠ℹ] \[\d+/\d+\] Built \S+ \(([^)]*)\)")
DURATION = re.compile(r"(\d+(?:\.\d+)?)(ms|s|m|h)")
UNIT = {"ms": 0.001, "s": 1, "m": 60, "h": 3600}


def timestamp(text):
    stamp = datetime.fromisoformat(text.replace("Z", "+00:00"))
    if stamp.tzinfo is None:
        raise ValueError("CI timestamps must include a timezone")
    return stamp


def elapsed_seconds(run, now):
    # The attempt endpoint updates this timestamp on reruns; created_at does not.
    started = timestamp(run["run_started_at"])
    if now.tzinfo is None:
        raise ValueError("CI timestamps must include a timezone")
    elapsed = (now - started).total_seconds()
    if elapsed < 0:
        raise ValueError("CI start is in the future")
    return elapsed


def seconds(duration):
    parts = DURATION.findall(duration)
    if not parts or "".join(n + u for n, u in parts) != duration.replace(" ", ""):
        raise ValueError(f"unrecognised Lake duration: {duration!r}")
    return sum(float(n) * UNIT[u] for n, u in parts)


def compile_seconds(lines, start, end):
    """Wall time within [start, end] during which Lake was building some module."""
    intervals = []
    for line in lines:
        match = BUILT.match(line)
        if match:
            finished = timestamp(match[1])
            began = finished - timedelta(seconds=seconds(match[2]))
            intervals.append((max(began, start), min(finished, end)))
    total, reach = 0.0, start
    for began, finished in sorted(intervals):
        began = max(began, reach)
        if finished > began:
            total += (finished - began).total_seconds()
            reach = finished
    return total


def check(run, now, lines=()):
    elapsed = elapsed_seconds(run, now)
    compiled = compile_seconds(lines, timestamp(run["run_started_at"]), now)
    counted = elapsed - compiled
    message = (f"CI attempt: {elapsed:.1f}s elapsed, of which {compiled:.1f}s compiled "
               f"modules; {counted:.1f}s counts against the {LIMIT_SECONDS}s limit.")
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with Path(summary).open("a") as report:
            report.write(message + "\n")
    print(message)
    if counted > LIMIT_SECONDS:
        print("::error::CI exceeded four minutes outside module compilation. "
              "Correctness checks were allowed to finish.")
        return 1
    return 0


if __name__ == "__main__":
    run = json.loads(Path(sys.argv[1]).read_text())
    lines = [line for log in sys.argv[2:]
             for line in Path(log).read_text(errors="replace").splitlines()]
    raise SystemExit(check(run, datetime.now(timezone.utc), lines))
