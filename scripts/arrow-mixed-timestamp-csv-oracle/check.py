"""Compare native Lean bytes with pinned independent Python CSV and PyArrow producers."""

import csv
from hashlib import sha256
import io
import json
from pathlib import Path
import platform
import subprocess
import tempfile

import pyarrow as pa
import pyarrow.parquet as pq


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
FIELDS = [
    pa.field("local_ns", pa.timestamp("ns")),
    pa.field("説明", pa.string()),
    pa.field("code", pa.int32(), nullable=False),
    pa.field("utc_ms", pa.timestamp("ms", "UTC"), nullable=False),
    pa.field("local_us", pa.timestamp("us")),
]
MIN, MAX = -(2**63), 2**63 - 1
GROUPS = [
    [(MIN, "", -(2**31), MAX, None), (None, None, 2**31 - 1, MIN, 0),
     (MAX, "N", 0, -1, -4000)],
    [],
    [(-1, '雪,"λ"\r\n🌍', -42, 0, MIN), (0, "T", 1, 17, MAX),
     (317, "  café  ", 2, -1700, -1)],
]
CASES = {
    "mixed": (FIELDS, GROUPS),
    "header_only": (list(reversed(FIELDS)), []),
    "zero_width": ([], [[(), ()], [], [()]]),
}


def ipc_wire(fields, groups):
    schema = pa.schema(fields)
    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, schema) as writer:
        for rows in groups:
            columns = []
            for index, field in enumerate(fields):
                values = [row[index] for row in rows]
                columns.append(pa.array(values, type=pa.int64()).view(field.type)
                               if pa.types.is_timestamp(field.type) else pa.array(values, type=field.type))
            batch = (pa.RecordBatch.from_arrays(columns, schema=schema) if fields else
                     pa.RecordBatch.from_struct_array(pa.array([{}] * len(rows), type=pa.struct([]))))
            writer.write_batch(batch)
    return sink.getvalue().to_pybytes()


def csv_records(fields, groups):
    header = [field.name for field in fields] or [""]
    rows = [["N" if value is None else "T" + str(value) for value in row] or [""]
            for group in groups for row in group]
    return [header, *rows]


def csv_wire(fields, groups):
    output = io.StringIO(newline="")
    csv.writer(output, lineterminator="\r\n").writerows(csv_records(fields, groups))
    return output.getvalue().encode("utf-8")


def producer_files():
    files = {}
    for name, (fields, groups) in CASES.items():
        files[name + ".arrow"] = ipc_wire(fields, groups)
        files[name + ".csv"] = csv_wire(fields, groups)
    files["control_byte.arrow"] = ipc_wire(FIELDS, [[(0, "x\0y", 0, 0, 0)]])
    assert files["mixed.arrow"].endswith(b"\xff\xff\xff\xff\0\0\0\0")
    files["mutated_late.arrow"] = files["mixed.arrow"] + b"\0"
    return files


def row_values(batch, fields):
    values = [
        batch.column(i).cast(pa.int64()).to_pylist() if pa.types.is_timestamp(field.type)
        else batch.column(i).to_pylist()
        for i, field in enumerate(fields)
    ]
    return [tuple(column[i] for column in values) for i in range(batch.num_rows)]


def check_outputs(directory):
    for name, (fields, groups) in CASES.items():
        expected = [row for group in groups for row in group]
        with (directory / (name + ".lean.csv")).open(encoding="utf-8", newline="") as wire:
            assert list(csv.reader(wire, strict=True)) == csv_records(fields, groups), name
        ipc_wire_bytes = (directory / (name + ".lean.arrow")).read_bytes()
        assert ipc_wire_bytes.endswith(b"\xff\xff\xff\xff\0\0\0\0"), name
        buffer = pa.BufferReader(ipc_wire_bytes)
        with pa.ipc.open_stream(buffer) as reader:
            assert list(reader.schema) == fields, name
            batches = list(reader)
            assert [batch.num_rows for batch in batches] == [len(expected)], name
            assert row_values(batches[0], fields) == expected, name
            assert buffer.tell() == len(ipc_wire_bytes), name
        if fields:
            parquet = pq.ParquetFile(directory / (name + ".lean.parquet"))
            assert list(parquet.schema_arrow) == fields, name
            assert parquet.num_row_groups == 1, name
            assert parquet.metadata.row_group(0).num_rows == len(expected), name
            assert all(parquet.metadata.row_group(0).column(i).compression == "UNCOMPRESSED"
                       for i in range(len(fields))), name
            assert row_values(parquet.read(), fields) == expected, name


def main():
    pins = json.loads((HERE / "fixtures.json").read_text())
    assert platform.python_version() == pins["python"]
    assert pa.__version__ == pins["pyarrow"]
    files = producer_files()
    assert {name: sha256(wire).hexdigest() for name, wire in files.items()} == pins["sha256"]
    with tempfile.TemporaryDirectory(prefix="arrow-mixed-timestamp-csv-") as scratch:
        directory = Path(scratch)
        for name, wire in files.items():
            (directory / name).write_bytes(wire)
        subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                        "--run", str(HERE / "Emit.lean"), scratch], cwd=ROOT, check=True)
        check_outputs(directory)
    print("Python csv and PyArrow independently verified three CSVs, three IPCs, and two Parquet files")


if __name__ == "__main__":
    main()
