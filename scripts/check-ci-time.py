#!/usr/bin/env python3
"""Fail a separate timing check after the correctness jobs finish.

Only the time some job of this attempt is running counts, each job measured from
its `started_at`: a job waiting for a runner is not CI work, so a gap with no job
running (such as main's wait for a 16-vCPU publisher) does not count.

Time Lake spends compiling modules the run had to build does not count either: a pull
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


def running_intervals(run, jobs, now):
    """[started_at, completed_at or now] of every job this attempt ran.

    A rerun keeps its earlier attempts' passing jobs in the list; they ran before
    this attempt's `run_started_at` and are left out.
    """
    if now.tzinfo is None:
        raise ValueError("CI timestamps must include a timezone")
    attempt = timestamp(run["run_started_at"])
    intervals = []
    for job in jobs:
        if job["conclusion"] == "skipped" or not job.get("started_at"):
            continue
        began = timestamp(job["started_at"])
        if began < attempt:
            continue
        finished = timestamp(job["completed_at"]) if job.get("completed_at") else now
        if finished < began or began > now:
            raise ValueError(f"job {job['name']!r} has inconsistent timestamps")
        intervals.append((began, finished))
    return intervals


def union_seconds(intervals):
    """Wall time covered by at least one of `intervals`."""
    total, reach = 0.0, None
    for began, finished in sorted(intervals):
        if reach is not None:
            began = max(began, reach)
        if finished > began:
            total += (finished - began).total_seconds()
            reach = finished
    return total


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


def check(run, jobs, now, lines=()):
    intervals = running_intervals(run, jobs, now)
    if not intervals:
        raise ValueError("no job of this CI attempt has started")
    running = union_seconds(intervals)
    waited = (now - min(began for began, _ in intervals)).total_seconds() - running
    compiled = compile_seconds(lines, timestamp(run["run_started_at"]), now)
    counted = running - compiled
    message = (f"CI attempt: {running:.1f}s with a job running ({waited:.1f}s with none, "
               f"waiting for runners, not counted), of which {compiled:.1f}s compiled "
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
    jobs = [job for page in json.loads(Path(sys.argv[2]).read_text()) for job in page["jobs"]]
    lines = [line for log in sys.argv[3:]
             for line in Path(log).read_text(errors="replace").splitlines()]
    raise SystemExit(check(run, jobs, datetime.now(timezone.utc), lines))
