"""Check actual Lean Parquet bytes against genuine pinned PyArrow TIMESTAMP IPC."""

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
SCALAR = runpy.run_path(str(HERE.parent / "parquet-timestamp-scalar-dispatch-oracle/check.py"))
THRIFT, MIXED, FRAMES, HYBRID = [SCALAR[name] for name in ("THRIFT", "MIXED", "FRAMES", "HYBRID")]
MIN, MAX = -(2**63), 2**63 - 1
FIELDS = [
    pa.field("utc_ms", pa.timestamp("ms", "UTC")),
    pa.field("local_µs", pa.timestamp("us"), nullable=False),
    pa.field("local_ns", pa.timestamp("ns")),
]


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
        [[MIN, None, MAX, 0, -1], [MAX, MIN, -1000, 0, 19], [None, -1, MIN, MAX, 0]],
        [[], [], []],
        [[], [], []],
        [[None, -17, 0], [-17, 0, MAX], [0, None, MAX]],
    ]
    reordered = [FIELDS[2].with_type(pa.timestamp("ns", "UTC")),
                 FIELDS[0].with_type(pa.timestamp("ms"))]
    wires = {
        "native_ordered": produce(FIELDS, positive),
        "native_reordered": produce(reordered, [[[MIN, 0, None], [MAX, -1, 0]], [[], []]]),
        "native_schema_only": produce(FIELDS, []),
        "native_seconds": produce([FIELDS[0].with_type(pa.timestamp("s", "UTC"))], [[[0, -1]]]),
        "native_named_timezone": produce([FIELDS[0], FIELDS[1].with_type(pa.timestamp("us", "Europe/Berlin"))], []),
        "native_required_null": produce(FIELDS, [[[0], [None], [MIN]]]),
        "native_duplicate": produce([FIELDS[0], FIELDS[0]], []),
        "native_empty_name": produce([FIELDS[0].with_name("")], []),
        "native_nul_name": produce([FIELDS[0].with_name("a\0b")], []),
        "native_zero_width": produce([], []),
        "native_other_type": produce([FIELDS[0], pa.field("other", pa.int32())], []),
    }
    assert wires["native_seconds"].endswith(b"\xff\xff\xff\xff\0\0\0\0")
    wires["mutated_seconds_trailing"] = wires["native_seconds"] + b"\0"
    wires["mutated_late_trailing"] = wires["native_ordered"] + b"\0"
    return wires


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
        assert leaf[1] == (TType.I32, 2)
        assert leaf[3] == (TType.I32, int(field.nullable))
        assert leaf[4] == (TType.STRING, field.name.encode())
        case = {"ms": 1, "us": 2, "ns": 3}[field.type.unit]
        annotation = leaf[10][1][8][1]
        assert annotation[1] == (TType.BOOL, field.type.tz == "UTC")
        assert annotation[2][1] == {case: (TType.STRUCT, {})}
        if case <= 2:
            assert leaf[6] == (TType.I32, 8 + case)
        else:
            assert 6 not in leaf

    parquet = pq.ParquetFile(pa.BufferReader(output))
    assert parquet.schema_arrow.equals(fields, check_metadata=True)
    assert parquet.num_row_groups == len(batches)
    cursor = 4
    for group, batch in enumerate(batches):
        assert parquet.metadata.row_group(group).num_rows == batch.num_rows
        native = parquet.read_row_group(group)
        assert native.num_rows == batch.num_rows
        for position, field in enumerate(fields):
            expected = batch.column(position).cast(pa.int64()).to_pylist()
            assert native.column(position).cast(pa.int64()).to_pylist() == expected
            metadata = THRIFT["column_metadata"](footer, group, position)
            assert metadata[1][1] == 2 and metadata[4][1] == 0 and metadata[5][1] == batch.num_rows
            assert metadata[6][1] == metadata[7][1] and metadata[9][1] == cursor
            assert THRIFT["list_field"](metadata, 2) == [0, 3]
            assert THRIFT["list_field"](metadata, 3) == [field.name.encode()]
            assert 11 not in metadata
            stop = cursor + metadata[7][1]
            [(header_start, header, payload_start, body)] = list(FRAMES(output, cursor, stop))
            assert header_start == cursor and payload_start + len(body) == stop
            assert header[1][1] == 0 and header[2][1] == header[3][1] == len(body)
            assert list(header[5][1][i][1] for i in range(1, 5)) == [batch.num_rows, 0, 3, 3]
            if field.nullable:
                size, = struct.unpack_from("<I", body)
                assert size == 2 * batch.num_rows
                mask = HYBRID(body[4:4 + size], 1, batch.num_rows)
                values = body[4 + size:]
            else:
                mask = [1] * batch.num_rows
                values = body
            assert mask == [int(tick is not None) for tick in expected]
            assert len(values) == 8 * sum(mask)
            assert [value for value, in struct.iter_unpack("<q", values)] == [
                tick for tick in expected if tick is not None]
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
    with tempfile.TemporaryDirectory(prefix="arrow-timestamp-ordered-to-parquet-") as folder:
        output = Path(folder)
        for name, wire in wires.items():
            (output / f"{name}.arrow").write_bytes(wire)
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output)],
                       cwd=ROOT, check=True)
        expected = {"native_ordered", "native_reordered", "native_schema_only"}
        assert {path.stem for path in output.glob("*.parquet")} == expected
        for name in sorted(expected):
            print(f"{name}: exact header, footer and signed ticks, groups "
                  f"{inspect(wires[name], (output / f'{name}.parquet').read_bytes())}")


if __name__ == "__main__":
    main()
