#!/usr/bin/env python3
"""Compare a sample of stock ACL2 8.7 logical evaluations against Lean."""

import argparse
import os
from pathlib import Path
import re
import subprocess


REVISION = "bc6f4f49e81a0711214a8d91f0d06e0e084d2204"
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
ROW = re.compile(r"^SILMARIL ([a-z0-9-]+) (-?\d+)$", re.MULTILINE)


def observations(output: str) -> dict[str, int]:
    rows = ROW.findall(output)
    values = {name: int(value) for name, value in rows}
    if len(rows) != len(values) or not rows:
        raise SystemExit(f"Missing or duplicate observations\n{output}")
    return values


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("acl2_source", type=Path, help="pinned ACL2 checkout with saved_acl2 built")
    args = parser.parse_args()
    source = args.acl2_source.resolve()
    revision = subprocess.check_output(["git", "-C", source, "rev-parse", "HEAD"], text=True).strip()
    if revision != REVISION:
        raise SystemExit(f"Expected ACL2 {REVISION}, got {revision}")
    native = subprocess.run(
        [source / "saved_acl2"],
        input=(HERE / "standard-objects-probe.lsp").read_text(),
        cwd=source, env={**os.environ, "ACL2_CUSTOMIZATION": "NONE"},
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, check=True,
    ).stdout
    if "ACL2 Version 8.7" not in native or "ACL2 Error" in native or "******** FAILED ********" in native:
        raise SystemExit(native)
    lean = subprocess.check_output(
        ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
         HERE / "StandardObjectsProbe.lean"], cwd=ROOT, text=True,
    )
    native_values, lean_values = observations(native), observations(lean)
    if native_values != lean_values:
        for name in sorted(native_values.keys() | lean_values.keys()):
            if native_values.get(name) != lean_values.get(name):
                print(f"{name}: ACL2={native_values.get(name)} Lean={lean_values.get(name)}")
        raise SystemExit(1)
    print(f"ACL2 8.7 and Lean agreed on {len(lean_values)} observations")


if __name__ == "__main__":
    main()
