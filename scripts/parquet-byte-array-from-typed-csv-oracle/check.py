"""Compare original selected Parquet slots and actual Lean native returns."""

import argparse
import csv
from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
from runpy import run_path
import subprocess
import sys

import pyarrow as pa


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
INPUTS = {
    "required-empty": [["empty"]],
    "bad-header": [["other"], ["T00FF"]],
    "bad-hex": [["blob"], ["T"], ["N"], ["T00FF"], ["T0a"]],
    "odd-hex": [["blob"], ["T0"]],
    "required-null": [["key"], ["T"], ["N"]],
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    fixtures = out / "input"
    fixtures.mkdir(parents=True, exist_ok=True)
    assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
    assert sys.version_info[:2] == (3, 13) and version("thrift") == "0.25.0"

    forward = ROOT / "scripts/parquet-opaque-typed-csv-oracle/check.py"
    subprocess.run([sys.executable, str(forward), "--out", str(out / "forward")], cwd=ROOT, check=True)
    source = run_path(str(forward))
    for name, records in INPUTS.items():
        with (fixtures / f"{name}.csv").open("w", encoding="utf-8", newline="") as stream:
            csv.writer(stream, lineterminator="\r\n").writerows(records)
    (fixtures / "malformed.csv").write_bytes(b"blob\r\nT\xff\r\n")

    expected = {"required-empty": ("empty", False, [])}
    for file, stem, name, nullable, counts in source["CASES"]:
        groups = source["checked_rows"](out / "forward" / "source" / file, name, nullable, counts)
        values = [value for group in groups for value in group]
        expected[stem] = (name, nullable, values)
        with (out / "forward" / f"{stem}.csv").open(encoding="utf-8", newline="") as stream:
            assert list(csv.reader(stream, strict=True)) == source["tokens"](name, values)

    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
         "--run", str(HERE / "Check.lean"), str(out)],
        cwd=ROOT, check=True,
    )
    thrift = run_path(str(ROOT / "tests/formats/parquet-timestamp-leaf/check-fixtures.py"))
    native = run_path(str(ROOT / "scripts/parquet-plain-byte-array-file-writer-oracle/check.py"))
    for stem, (name, nullable, values) in expected.items():
        wire = (out / f"{stem}.parquet").read_bytes()
        native["check_wire"](thrift, wire, name, nullable, values)
        native["check_pyarrow"](wire, name, nullable, values)

    pins = json.loads((HERE / "sha256.json").read_text(encoding="utf-8"))
    assert set(pins) == {f"{stem}.parquet" for stem in expected} | {
        f"input/{stem}.csv" for stem in (*INPUTS, "malformed")
    }
    for name, digest in pins.items():
        actual = sha256((out / name).read_bytes()).hexdigest()
        assert digest == actual, f"{name}: fixture hash changed"
        print(f"{actual}  {name}")
    print("PyArrow, CPython and Thrift verified the selected slots and all five native return files.")


if __name__ == "__main__":
    main()
