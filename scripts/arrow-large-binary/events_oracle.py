#!/usr/bin/env python3
"""Validate modern LargeBinary output of both native event source profiles."""
import argparse
import hashlib
from pathlib import Path
import runpy
import subprocess
import sys

import pyarrow as pa


ROOT = Path(__file__).resolve().parents[2]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    if (sys.byteorder != "little" or pa.__version__ != "26.0.1"
            or pa.cpp_build_info.version != "26.0.1"):
        raise SystemExit("oracle requires little-endian PyArrow 26.0.1")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    scripts = ROOT / "scripts/arrow-large-binary"
    expected = runpy.run_path(str(scripts / "stream_fixture.py"))["EXPECTED"]
    verify = runpy.run_path(str(scripts / "stream_writer_oracle.py"))["verify"]
    subprocess.run(
        ["lake", "env", "lean", "-DwarningAsError=true", "--run",
         str(scripts / "TranscodeEvents.lean"), str(output)],
        cwd=ROOT, check=True,
    )
    for source in ("modern", "legacy"):
        wire = (output / f"{source}.arrows").read_bytes()
        ranges, eos = verify(wire, "payload", True, expected)
        print(f"{source} source: SHA-256 {hashlib.sha256(wire).hexdigest()}, records {ranges}, EOS {eos}")


if __name__ == "__main__":
    main()
