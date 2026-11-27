"""Check the actual public IPC to typed CSV to IPC composition."""

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
PINS = {
    "producer/mixed.arrows": "00dbda52bd8196ef42269c29a285a74f500870ea437d0767879859695a8ec523",
    "roundtrip.csv": "4e8710e43f56e102eff78b44b35639d9665ebcb8e9d7124b4fb9cf0e3cc47d1d",
    "roundtrip.arrows": "468e5559734466bc3035987012768aec39e628b314e2ac7f8110afa77d9e1655",
}


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
    input_wire = producer / "mixed.arrows"
    with pa.ipc.open_stream(input_wire.read_bytes()) as stream:
        schema = stream.schema
        assert [batch.num_rows for batch in stream] == [2, 0, 2]
    assert schema.names == ["téxt", "amount", "téxt", "required"]

    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Check.lean"), str(out)],
        cwd=ROOT, check=True,
    )
    with (out / "roundtrip.csv").open(encoding="utf-8", newline="") as stream:
        assert list(csv.reader(stream, strict=True)) == forward["expected_csv"](input_wire)
    reverse["compare"](out, "roundtrip", schema)
    for name, expected_digest in PINS.items():
        digest = sha256((out / name).read_bytes()).hexdigest()
        print(f"{digest}  {name}")
        assert digest == expected_digest, f"{name}: fixture hash changed"
    print("CPython and PyArrow verified original descriptors and rows with one complete output batch.")


if __name__ == "__main__":
    main()
