"""Compare actual mixed Lean IPC with pinned independent Parquet and Arrow producers."""

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
from thrift.Thrift import TType

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PREDECESSOR = HERE.parent / "parquet-timestamp-heterogeneous-events-oracle"
P = runpy.run_path(str(PREDECESSOR / "check.py"))
THRIFT, MIXED, FRAMES = (P[name] for name in ("THRIFT", "MIXED", "FRAMES"))
FIELDS = P["FIELDS"]
EOS = b"\xff\xff\xff\xff\0\0\0\0"

CASES = {
    "duplicate_v1": ("native_v1", [3, 0, 1, 2, 1]),
    "reordered_v2": ("native_v2", [2, 1, 0, 3]),
    "zero_width": ("native_v1", []),
    "schema_only": ("native_schema_only", [2, 0, 1]),
    "explicit_zero_row": ("assembled_framed_zero", [1, 2, 0, 3, 2]),
    "zero_width_with_zero_row": ("assembled_framed_zero", []),
    "omit_corrupt": ("mutated_late_timestamp_dictionary_magic", [1, 3, 0]),
}


def framed_zero_group():
    """Give a producer-native empty footer group explicit PLAIN V2 page spans."""
    template = P["produce"]("2.0", [[[], [], [], []]])
    page = runpy.run_path(str(HERE.parent / "parquet-byte-array-to-ipc-oracle/zero_group.py"))[
        "empty_v2_header"]()
    footer = MIXED["metadata"](template)
    group, = THRIFT["list_field"](footer, 4)
    chunks = THRIFT["list_field"](group, 1)
    assert len(chunks) == len(FIELDS) and group[3][1] == 0
    for index, (chunk, field) in enumerate(zip(chunks, FIELDS, strict=True)):
        offset = 4 + index * len(page)
        metadata = chunk[3][1]
        assert metadata[5][1] == 0 and THRIFT["list_field"](metadata, 3) == [field.name.encode()]
        metadata[2] = TType.LIST, (TType.I32, [0, 3])
        metadata[4] = TType.I32, 0
        metadata[6] = metadata[7] = TType.I64, len(page)
        metadata[9] = chunk[2] = TType.I64, offset
        metadata.pop(11, None)
    group[2] = TType.I64, len(page) * len(chunks)
    if 6 in group:
        group[6] = group[2]
    footer[6] = TType.STRING, b"Constructed Thrift empty V2 heterogeneous control"
    encoded = THRIFT["encode"](footer)
    return b"PAR1" + page * len(chunks) + encoded + struct.pack("<I", len(encoded)) + b"PAR1"


def fixture_inputs():
    wires, _, offset = P["fixtures"]()
    hashes = {name: sha256(wire).hexdigest() for name, wire in wires.items()}
    assert hashes == json.loads((PREDECESSOR / "fixtures.json").read_text())
    empty = framed_zero_group()
    parts = [(wires["native_v2"], 0), (empty, 0), (wires["native_v2"], 1)]
    mixed = P["HELPERS"]["ASSEMBLE_GROUPS"](parts)
    mixed = THRIFT["rewrite_footer"](mixed, lambda footer: footer.update({
        6: (TType.STRING, b"Original PyArrow chunks and constructed Thrift empty V2 pages")}))
    parquet = P["open_parquet"](mixed)
    assert parquet.schema_arrow == pa.schema(FIELDS)
    assert [parquet.read_row_group(i).num_rows for i in range(parquet.num_row_groups)] == [5, 0, 3]
    for group, (source, index) in enumerate(parts):
        for col in range(len(FIELDS)):
            meta = THRIFT["column_metadata"](MIXED["metadata"](mixed), group, col)
            original = THRIFT["column_metadata"](MIXED["metadata"](source), index, col)
            start, stop = MIXED["column_extent"](meta)
            lo, hi = MIXED["column_extent"](original)
            assert mixed[start:stop] == source[lo:hi]
            if group == 1:
                [(header_start, header, payload, stored)] = list(FRAMES(mixed, start, stop))
                assert header_start == meta[9][1] and payload == stop and not stored
                assert header[1][1] == 3 and header[2][1] == header[3][1] == 0
                assert {i: header[8][1][i][1] for i in range(1, 7)} == dict.fromkeys(range(1, 7), 0)
    wires["assembled_framed_zero"] = mixed
    return wires, offset


def write_ipc(schema, batches):
    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, schema) as writer:
        for batch in batches:
            writer.write_batch(batch)
    return sink.getvalue().to_pybytes()


def native_ipc():
    code, label, utc, _ = FIELDS
    # Duplicate UTF8 names carry different data to distinguish positions.
    seconds = pa.field("local_seconds", pa.timestamp("s"), nullable=False)
    fields = [seconds, label, utc, code, label]
    schema = pa.schema(fields)
    rows = [[P["MAX"], P["MIN"], -1], ["原", None, ""], [P["MIN"], P["MAX"], None],
            [-2**31, 0, 2**31 - 1], [None, "🙂", "second label"]]
    batches = []
    for columns in (rows, [[], [], [], [], []]):
        arrays = [
            pa.array(values, type=pa.int64()).view(field.type)
            if pa.types.is_timestamp(field.type) else pa.array(values, type=field.type)
            for field, values in zip(fields, columns, strict=True)
        ]
        batches.append(pa.RecordBatch.from_arrays(arrays, schema=schema))
    mixed = write_ipc(schema, batches)
    zero_width = write_ipc(pa.schema([]), [
        pa.RecordBatch.from_struct_array(pa.Array.from_buffers(pa.struct([]), count, [None], children=[]))
        for count in (4, 0, 2)
    ])
    zone = write_ipc(pa.schema([pa.field("zone", pa.timestamp("ms", "Europe/Berlin"))]), [])
    return {
        "native_mixed": mixed,
        "native_zero_width": zero_width,
        "native_named_timezone": zone,
        "mutated_ipc_trailing": mixed + b"\0",
    }


def read_ipc(wire):
    assert wire.endswith(EOS)
    source = pa.BufferReader(wire)
    with pa.ipc.open_stream(source) as reader:
        schema = reader.schema
        batches = list(reader)
        assert source.tell() == len(wire)
    return schema, batches


def compare_parquet(wire, parquet, ordinals):
    schema, batches = read_ipc(wire)
    fields = [parquet.schema_arrow.field(i) for i in ordinals]
    assert schema.equals(pa.schema(fields), check_metadata=True)
    assert len(batches) == parquet.num_row_groups
    for group, batch in enumerate(batches):
        assert batch.num_rows == parquet.metadata.row_group(group).num_rows
        assert batch.num_columns == len(fields)
        for position, field in enumerate(fields):
            expected = parquet.read_row_group(group, columns=[field.name]).column(0).combine_chunks()
            assert batch.column(position).equals(expected)
    return [batch.num_rows for batch in batches]


def compare_native(wire, original):
    schema, batches = read_ipc(wire)
    expected_schema, expected_batches = read_ipc(original)
    assert schema.equals(expected_schema, check_metadata=True)
    for actual, expected in zip(batches, expected_batches, strict=True):
        assert actual.num_rows == expected.num_rows and actual.num_columns == expected.num_columns
        for position in range(actual.num_columns):
            assert actual.column(position).equals(expected.column(position))
    return [batch.num_rows for batch in batches]


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    parquet, offset = fixture_inputs()
    native = native_ipc()
    pins = {"assembled_framed_zero.parquet": sha256(parquet["assembled_framed_zero"]).hexdigest()}
    pins.update({f"{name}.arrow": sha256(wire).hexdigest() for name, wire in native.items()})
    assert pins == json.loads((HERE / "fixtures.json").read_text()), pins
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-heterogeneous-ipc-") as folder:
        output = Path(folder)
        for suffix, fixtures in ((".parquet", parquet), (".arrow", native)):
            for name, wire in fixtures.items():
                (output / (name + suffix)).write_bytes(wire)
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output),
                        str(offset)], cwd=ROOT, check=True)
        readback = {"native_mixed", "native_zero_width"}
        assert {wire.stem for wire in output.glob("*.arrows")} == set(CASES) | readback
        for name, (key, ordinals) in CASES.items():
            rows = compare_parquet((output / f"{name}.arrows").read_bytes(), P["open_parquet"](parquet[key]), ordinals)
            print(f"{name}: exact positional IPC and batches {rows}")
        for name in sorted(readback):
            rows = compare_native((output / f"{name}.arrows").read_bytes(), native[name])
            print(f"{name}: genuine IPC read and re-emission with batches {rows}")


if __name__ == "__main__":
    main()
