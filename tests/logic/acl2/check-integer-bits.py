#!/usr/bin/env python3
"""Compare Lean and optionally fresh ACL2 logical evaluations with the pinned snapshot."""

import argparse
import difflib
import os
from pathlib import Path
import re
import subprocess


REVISION = "bc6f4f49e81a0711214a8d91f0d06e0e084d2204"
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
ROW = re.compile(r"^BIT ([a-z0-9-]+) -?\d+$", re.MULTILINE)


def compare(label: str, output: str, expected: str) -> None:
    rows = list(ROW.finditer(output))
    if not rows or len({row[1] for row in rows}) != len(rows):
        raise SystemExit(f"{label}: missing or repeated observations\n{output}")
    actual = "".join(row[0] + "\n" for row in rows)
    if actual != expected:
        raise SystemExit("".join(difflib.unified_diff(
            expected.splitlines(keepends=True), actual.splitlines(keepends=True),
            fromfile="ACL2 8.7 snapshot", tofile=label,
        )))
    print(f"{label} matched {len(rows)} observations")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--acl2-source", type=Path, help="pinned checkout with saved_acl2 built")
    args = parser.parse_args()
    expected = (HERE / "integer-bits-8.7.txt").read_text()
    lean = subprocess.check_output(
        ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
         HERE / "IntegerBitsProbe.lean"], cwd=ROOT, text=True,
    )
    compare("Lean", lean, expected)
    if args.acl2_source is None:
        return
    source = args.acl2_source.resolve()
    revision = subprocess.check_output(["git", "-C", source, "rev-parse", "HEAD"], text=True).strip()
    if revision != REVISION:
        raise SystemExit(f"Expected ACL2 {REVISION}, got {revision}")
    for run in (1, 2):
        native = subprocess.run(
            [source / "saved_acl2"], input=(HERE / "integer-bits-probe.lsp").read_text(),
            cwd=source, env={**os.environ, "ACL2_CUSTOMIZATION": "NONE"},
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, check=True,
        ).stdout
        if "ACL2 Version 8.7" not in native or "ACL2 Error" in native or "******** FAILED ********" in native:
            raise SystemExit(native)
        compare(f"ACL2 run {run}", native, expected)


if __name__ == "__main__":
    main()
