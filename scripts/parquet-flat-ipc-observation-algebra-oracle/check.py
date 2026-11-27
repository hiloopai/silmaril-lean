"""Check complete positional IPC observations against independent PyArrow output."""

import argparse
from hashlib import sha256
import os
from pathlib import Path
from runpy import run_path
import subprocess
import sys

import pyarrow as pa
import pyarrow.parquet as pq


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PREDECESSOR = ROOT / "scripts/parquet-flat-projection-ipc-events-oracle/check.py"
ORDINALS = [3, 0, 1, 2]
PINS = {
    "pyarrow-wide.arrows": "16799efeb0a52f2585b1966d68b820fd1b791e8a4c0b1277d9cbb016e1375605",
    "pyarrow-empty-first.arrows": "2b05ef53a2a5f16098ccaac47c138baf7c4b22e5bf3604faa75e8c2215570f14",
}


def write_stream(path, schema, batches):
    with pa.OSFile(str(path), "wb") as sink, pa.ipc.new_stream(sink, schema) as stream:
        for batch in batches:
            stream.write_batch(batch)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    out = args.out.resolve()
    subprocess.run([sys.executable, "-Bu", str(PREDECESSOR), "--out", str(out)], cwd=ROOT, check=True)
    source = out / "empty-middle.parquet"
    independent = out / "pyarrow-wide.arrows"
    moved = out / "pyarrow-empty-first.arrows"
    with pq.ParquetFile(source) as parquet:
        selected = [parquet.schema_arrow[i] for i in ORDINALS]
        schema = pa.schema([
            pa.field(field.name, pa.binary_view() if field.type == pa.binary() else field.type,
                     nullable=field.nullable)
            for field in selected
        ])
        batches = []
        for index in range(parquet.num_row_groups):
            group = parquet.read_row_group(index, columns=schema.names, use_threads=False)
            arrays = [group[field.name].combine_chunks().cast(field.type) for field in schema]
            batches.append(pa.RecordBatch.from_arrays(arrays, schema=schema))
    write_stream(independent, schema, batches)
    write_stream(moved, schema, [batches[1], batches[0], batches[2]])
    wire = independent.read_bytes()
    assert wire != (out / "empty-middle-wide.arrows").read_bytes()
    oracle = run_path(str(ROOT / "scripts/parquet-flat-projection-oracle/check.py"))
    oracle["check_ipc"](source, wire, ORDINALS)
    with pa.ipc.open_stream(moved.read_bytes()) as stream:
        actual = list(stream)
        assert [batch.num_rows for batch in actual] == [0, 12, 6]
        assert all(left.equals(right) for left, right in zip(actual, [batches[1], batches[0], batches[2]], strict=True))
    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Check.lean"), str(out)],
        cwd=ROOT, check=True,
    )
    for path in (independent, moved):
        digest = sha256(path.read_bytes()).hexdigest()
        print(f"{digest}  {path.name}")
        assert digest == PINS[path.name], f"{path.name}: fixture hash changed"


if __name__ == "__main__":
    main()
