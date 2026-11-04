#!/usr/bin/env python3
"""Fail a separate timing check after the correctness jobs finish."""

import json
import os
import sys
from datetime import datetime, timezone
from pathlib import Path


LIMIT_SECONDS = 240


def elapsed_seconds(run, now):
    # The attempt endpoint updates this timestamp on reruns; created_at does not.
    started = datetime.fromisoformat(run["run_started_at"].replace("Z", "+00:00"))
    if started.tzinfo is None or now.tzinfo is None:
        raise ValueError("CI timestamps must include a timezone")
    elapsed = (now - started).total_seconds()
    if elapsed < 0:
        raise ValueError("CI start is in the future")
    return elapsed


def check(run, now):
    elapsed = elapsed_seconds(run, now)
    message = f"CI attempt: {elapsed:.1f}s elapsed; limit: {LIMIT_SECONDS}s."
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with Path(summary).open("a") as report:
            report.write(message + "\n")
    print(message)
    if elapsed > LIMIT_SECONDS:
        print("::error::CI exceeded four minutes. Correctness checks were allowed to finish.")
        return 1
    return 0


if __name__ == "__main__":
    run = json.loads(Path(sys.argv[1]).read_text())
    raise SystemExit(check(run, datetime.now(timezone.utc)))
