"""Check the bounded mixed CSV named bridge through genuine Arrow IPC."""

import argparse
import csv
from hashlib import sha256
import os
from pathlib import Path
from runpy import run_path
import subprocess
import sys

import pyarrow as pa


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def check_pin(path, expected):
    digest = sha256(path.read_bytes()).hexdigest()
    assert digest == expected, f"{path.name}: fixture hash changed"
    print(f"{digest}  {path}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    producer = out / "producer"
    producer.mkdir(parents=True, exist_ok=True)
    assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
    assert sys.version_info[:2] == (3, 13)
    forward = run_path(str(ROOT / "scripts/arrow-mixed-scan-csv-oracle/check.py"))
    reverse = run_path(str(ROOT / "scripts/typed-csv-to-mixed-ipc-oracle/check.py"))
    forward["write_ipc"](producer)
    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Check.lean"), str(out)],
        cwd=ROOT, check=True,
    )
    for name, prior in [("mixed", "mixed"), ("schema-only", "header-only"), ("zero-width", "zero-width")]:
        original = producer / f"{name}.arrows"
        check_pin(original, forward["PINS"][f"{name}.arrows"])
        with pa.ipc.open_stream(original.read_bytes()) as stream:
            schema = stream.schema
        with (out / f"{name}.csv").open(encoding="utf-8", newline="") as stream:
            assert list(csv.reader(stream, strict=True)) == forward["expected_csv"](original)
        reverse["compare"](out, name, schema)
        check_pin(out / f"{name}.csv", forward["PINS"][f"{name}.lean.csv"])
        check_pin(out / f"{name}.arrows", reverse["PINS"][f"{prior}.arrows"])
    print("CPython and PyArrow verified three native streams through named CSV and back.")


if __name__ == "__main__":
    main()
