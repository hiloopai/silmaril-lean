"""Compare complete native IPC materialization to independent PyArrow rows."""

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
from runpy import run_path
import subprocess
import sys

import pyarrow as pa


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PREDECESSOR = ROOT / "scripts/parquet-flat-ipc-observation-algebra-oracle/check.py"
PINS = {
    "pyarrow-schema-only.arrows": "31e88ddf84abe137b207df84b05f33798b9c150ed9a42386c59f3718f34ad6b9",
    "pyarrow-one-empty.arrows": "40f35e9d99ebb890e1241bc037759e2abd23c2ae1f8e3557ed10504d22d69013",
}


def make_empty_controls(out):
    with pa.ipc.open_stream((out / "pyarrow-wide.arrows").read_bytes()) as source:
        schema = source.schema
        batches = list(source)
    assert [batch.num_rows for batch in batches] == [12, 0, 6]
    write_stream = run_path(str(PREDECESSOR))["write_stream"]
    write_stream(out / "pyarrow-schema-only.arrows", schema, [])
    write_stream(out / "pyarrow-one-empty.arrows", schema, [batches[1]])


def compare_table(out, name, suffix=".rows.json"):
    wire = (out / f"{name}.arrows").read_bytes()
    with pa.ipc.open_stream(wire) as source:
        fields = [[field.name, field.nullable, str(field.type)] for field in source.schema]
        rows = []
        for batch in source:
            values = [column.to_pylist() for column in batch.columns]
            rows.extend([
                [list(column[i]) if isinstance(column[i], bytes) else column[i] for column in values]
                for i in range(batch.num_rows)
            ])
    expected = {"fields": fields, "rows": rows}
    assert json.loads((out / f"{name}{suffix}").read_text()) == expected, name


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    out = args.out.resolve()
    subprocess.run([sys.executable, "-Bu", str(PREDECESSOR), "--out", str(out)], cwd=ROOT, check=True)
    make_empty_controls(out)
    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Check.lean"), str(out)],
        cwd=ROOT, check=True,
    )
    for name in ("empty-middle-wide", "empty-middle-repeat", "empty-middle-zero-width",
                 "pyarrow-wide", "pyarrow-empty-first", "pyarrow-schema-only", "pyarrow-one-empty"):
        compare_table(out, name)
    for name in ("wide-wide", "empty-middle-repeat", "empty-middle-zero-width", "schema-only-repeat"):
        compare_table(out, name, ".direct.rows.json")
    print("PyArrow verified all four direct Parquet materializations against their IPC observations.")
    for name, expected in PINS.items():
        digest = sha256((out / name).read_bytes()).hexdigest()
        print(f"{digest}  {name}")
        assert digest == expected, f"{name}: fixture hash changed"
    print("PyArrow verified seven ordered Scan tables, including repeated descriptors and 18 zero-width rows.")


if __name__ == "__main__":
    main()
