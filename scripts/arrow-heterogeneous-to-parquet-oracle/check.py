"""Check native Lean Parquet against genuine pinned PyArrow mixed IPC."""

from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
import platform
import runpy
import struct
import subprocess
import tempfile

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PREVIOUS = runpy.run_path(str(HERE.parent / "arrow-timestamp-ordered-to-parquet-oracle/check.py"))
THRIFT, MIXED, FRAMES, HYBRID = (PREVIOUS[key] for key in ("THRIFT", "MIXED", "FRAMES", "HYBRID"))
MIN, MAX = -(2**63), 2**63 - 1
FIELDS = [
    pa.field("label", pa.string()),
    pa.field("utc_ms", pa.timestamp("ms", "UTC"), nullable=False),
    pa.field("code", pa.int32()),
    pa.field("local_ns", pa.timestamp("ns")),
    pa.field("説明", pa.string(), nullable=False),
    pa.field("local_us", pa.timestamp("us"), nullable=False),
]
POSITIVE = ("native_mixed", "native_reordered", "native_schema_only")


def produce(fields, batches):
    schema = pa.schema(fields)
    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, schema) as writer:
        for batch in batches:
            cols = [
                pa.array(values, type=pa.int64()).view(field.type)
                if pa.types.is_timestamp(field.type) else pa.array(values, type=field.type)
                for field, values in zip(fields, batch, strict=True)
            ]
            writer.write_batch(pa.RecordBatch.from_arrays(cols, schema=schema))
    return sink.getvalue().to_pybytes()


def fixtures():
    positive = [
        [["", None, "原", "café\0λ", "🙂"], [MAX, MIN, -1, 0, 4], [None, -2**31, 0, 2**31 - 1, -1],
         [MIN, None, MAX, 0, -1], ["雪", "", "中文", "null", "a\0b"], [0, MIN, MAX, -999, 37]],
        [[], [], [], [], [], []],
        [[None, "A", ""], [-100, 0, 1], [0, None, 4], [MAX, 0, None], ["λ", "🌍", ""], [MAX, 0, -1]],
    ]
    positions = [2, 3, 4, 1, 0]
    reordered = [FIELDS[i] for i in positions]
    wires = {
        "native_mixed": produce(FIELDS, positive),
        "native_reordered": produce(reordered, [[group[i] for i in positions] for group in
                                                  (positive[2], positive[1])]),
        "native_schema_only": produce(FIELDS, []),
        "native_seconds": produce([FIELDS[2], FIELDS[1].with_type(pa.timestamp("s", "UTC"))],
                                  [[[0, -2], [MIN, MAX]]]),
        "native_duplicate": produce([FIELDS[0], FIELDS[2].with_name("label")], []),
        "native_empty_name": produce([FIELDS[0].with_name(""), FIELDS[1]], []),
        "native_nul_name": produce([FIELDS[0].with_name("a\0b"), FIELDS[1]], []),
        "native_required_null": produce(FIELDS, [[["text"], [None], [0], [MIN], [""], [MAX]]]),
        "native_named_timezone": produce([FIELDS[2], FIELDS[1].with_type(pa.timestamp("ms", "Europe/Berlin"))], []),
        "native_zero_width": produce([], []),
    }
    assert wires["native_seconds"].endswith(b"\xff\xff\xff\xff\0\0\0\0")
    wires["mutated_seconds_trailing"] = wires["native_seconds"] + b"\0"
    wires["mutated_late_trailing"] = wires["native_mixed"] + b"\0"
    return wires


def physical(field):
    return 2 if pa.types.is_timestamp(field.type) else 6 if pa.types.is_string(field.type) else 1


def check_annotation(field, leaf):
    assert leaf[1] == (TType.I32, physical(field))
    assert leaf[3] == (TType.I32, int(field.nullable))
    assert leaf[4] == (TType.STRING, field.name.encode())
    if pa.types.is_timestamp(field.type):
        case = {"ms": 1, "us": 2, "ns": 3}[field.type.unit]
        annotation = leaf[10][1][8][1]
        assert annotation[1] == (TType.BOOL, field.type.tz == "UTC")
        assert annotation[2][1] == {case: (TType.STRUCT, {})}
        if case <= 2:
            assert leaf[6] == (TType.I32, 8 + case)
        else:
            assert 6 not in leaf
    elif pa.types.is_string(field.type):
        assert leaf[10][1] == {1: (TType.STRUCT, {})} and leaf[6] == (TType.I32, 0)
    else:
        assert 6 not in leaf and 10 not in leaf


def scalar_words(field, body):
    if pa.types.is_string(field.type):
        values = []
        cursor = 0
        while cursor < len(body):
            length, = struct.unpack_from("<I", body, cursor)
            cursor += 4
            assert cursor + length <= len(body)
            values.append(body[cursor:cursor + length].decode("utf-8"))
            cursor += length
        return values
    word = "<q" if pa.types.is_timestamp(field.type) else "<i"
    return [value for value, in struct.iter_unpack(word, body)]


def inspect(source_wire, output):
    with pa.ipc.open_stream(source_wire) as source:
        fields = source.schema
        batches = list(source)
    assert output[:4] == output[-4:] == b"PAR1"
    footer = MIXED["metadata"](output)
    root, *leaves = THRIFT["list_field"](footer, 2)
    assert root[5] == (TType.I32, len(fields)) and len(leaves) == len(fields)
    assert footer[3][1] == sum(batch.num_rows for batch in batches)
    for leaf, field in zip(leaves, fields, strict=True):
        check_annotation(field, leaf)

    parquet = pq.ParquetFile(pa.BufferReader(output))
    assert parquet.schema_arrow.equals(fields, check_metadata=True)
    assert parquet.num_row_groups == len(batches)
    cursor = 4
    for group, batch in enumerate(batches):
        native = parquet.read_row_group(group)
        assert native.num_rows == parquet.metadata.row_group(group).num_rows == batch.num_rows
        for position, field in enumerate(fields):
            values = batch.column(position)
            if pa.types.is_timestamp(field.type):
                values = values.cast(pa.int64())
            expected = values.to_pylist()
            assert native.column(position).combine_chunks().equals(batch.column(position))
            metadata = THRIFT["column_metadata"](footer, group, position)
            assert metadata[1] == (TType.I32, physical(field))
            assert metadata[4][1] == 0 and metadata[5][1] == batch.num_rows
            assert metadata[6][1] == metadata[7][1] and metadata[9][1] == cursor
            assert THRIFT["list_field"](metadata, 2) == [0, 3]
            assert THRIFT["list_field"](metadata, 3) == [field.name.encode()] and 11 not in metadata
            stop = cursor + metadata[7][1]
            [(header_start, header, payload_start, body)] = list(FRAMES(output, cursor, stop))
            assert header_start == cursor and payload_start + len(body) == stop
            assert header[1][1] == 0 and header[2][1] == header[3][1] == len(body) and 4 not in header
            assert list(header[5][1][i][1] for i in range(1, 5)) == [batch.num_rows, 0, 3, 3]
            if field.nullable:
                size, = struct.unpack_from("<I", body)
                assert size == 2 * batch.num_rows
                mask = HYBRID(body[4:4 + size], 1, batch.num_rows)
                values = body[4 + size:]
            else:
                mask = [1] * batch.num_rows
                values = body
            assert mask == [int(value is not None) for value in expected]
            assert scalar_words(field, values) == [value for value in expected if value is not None]
            cursor = stop
    footer_size, = struct.unpack_from("<I", output, len(output) - 8)
    assert cursor + footer_size + 8 == len(output)
    return [batch.num_rows for batch in batches]


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    wires = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in wires.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="arrow-heterogeneous-to-parquet-") as folder:
        output = Path(folder)
        for name, wire in wires.items():
            (output / f"{name}.arrow").write_bytes(wire)
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output)],
                       cwd=ROOT, check=True)
        assert {path.stem for path in output.glob("*.parquet")} == set(POSITIVE)
        for name in POSITIVE:
            rows = inspect(wires[name], (output / f"{name}.parquet").read_bytes())
            print(f"{name}: exact mixed footer, PLAIN values and group rows {rows}")


if __name__ == "__main__":
    main()
