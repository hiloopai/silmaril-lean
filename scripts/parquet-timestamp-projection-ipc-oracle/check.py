"""Verify actual Lean ordered TIMESTAMP IPC against pinned independent PyArrow."""

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
PROJECTION = runpy.run_path(str(HERE.parent / "parquet-timestamp-events-projection-oracle/check.py"))
THRIFT, MIXED, FRAMES = (PROJECTION[name] for name in ("THRIFT", "MIXED", "FRAMES"))
SCALAR, FIELDS = PROJECTION["SCALAR"], PROJECTION["FIELDS"]
EOS = b"\xff\xff\xff\xff\0\0\0\0"


def framed_zero_group():
    """Replace the producer's no-data offsets with deterministic empty PLAIN V2 frames."""
    template = PROJECTION["produce"]("2.0", [[[], [], []]])
    page = runpy.run_path(str(HERE.parent / "parquet-byte-array-to-ipc-oracle/zero_group.py"))[
        "empty_v2_header"]()
    footer = MIXED["metadata"](template)
    group, = THRIFT["list_field"](footer, 4)
    chunks = THRIFT["list_field"](group, 1)
    assert len(chunks) == len(FIELDS) and group[3][1] == 0
    for index, (chunk, field) in enumerate(zip(chunks, FIELDS, strict=True)):
        offset = 4 + index * len(page)
        metadata = chunk[3][1]
        assert metadata[5][1] == 0
        metadata[2] = TType.LIST, (TType.I32, [0, 3])
        metadata[4] = TType.I32, 0
        metadata[6] = metadata[7] = TType.I64, len(page)
        metadata[9] = chunk[2] = TType.I64, offset
        metadata.pop(11, None)
        assert THRIFT["list_field"](metadata, 3) == [field.name.encode()]
    group[2] = TType.I64, len(page) * len(chunks)
    if 6 in group:
        group[6] = group[2]
    footer[6] = TType.STRING, b"Constructed Thrift empty V2 timestamp control"
    encoded = THRIFT["encode"](footer)
    return b"PAR1" + page * len(chunks) + encoded + struct.pack("<I", len(encoded)) + b"PAR1"


def fixture_inputs():
    wires, _, evidence = PROJECTION["fixtures"]()
    expected = json.loads((HERE.parent / "parquet-timestamp-events-projection-oracle/fixtures.json").read_text())
    assert {name: sha256(wire).hexdigest() for name, wire in wires.items()} == expected
    empty = framed_zero_group()
    mixed = SCALAR["ASSEMBLE_GROUPS"]([(wires["native_v2"], 0), (empty, 0), (wires["native_v2"], 1)])
    mixed = THRIFT["rewrite_footer"](mixed, lambda footer: footer.update({
        6: (TType.STRING, b"Original PyArrow chunks and constructed Thrift empty V2 pages")}))
    parquet = PROJECTION["open_parquet"](mixed)
    assert parquet.schema_arrow == pa.schema(FIELDS)
    assert [parquet.metadata.row_group(i).num_rows for i in range(parquet.num_row_groups)] == [512, 0, 508]
    assert parquet.read_row_group(1).num_rows == 0
    for group, source, index in ((0, wires["native_v2"], 0), (1, empty, 0), (2, wires["native_v2"], 1)):
        for column in range(len(FIELDS)):
            meta = THRIFT["column_metadata"](MIXED["metadata"](mixed), group, column)
            original = THRIFT["column_metadata"](MIXED["metadata"](source), index, column)
            start, stop = MIXED["column_extent"](meta)
            lo, hi = MIXED["column_extent"](original)
            assert mixed[start:stop] == source[lo:hi]
            if group == 1:
                [(offset, header, payload, stored)] = list(FRAMES(mixed, start, stop))
                assert offset == meta[9][1] and payload == stop and not stored
                assert header[1][1] == 3 and header[2][1] == header[3][1] == 0
                assert {i: header[8][1][i][1] for i in range(1, 7)} == dict.fromkeys(range(1, 7), 0)
                assert header[8][1][7] == (TType.BOOL, False)
    wires["assembled_framed_zero"] = mixed
    return wires, evidence


CASES = {
    "duplicate_v1": ("native_v1", [4, 2, 3, 2]),
    "reordered_v2": ("native_v2", [3, 4, 2]),
    "zero_width": ("native_v1", []),
    "schema_only": ("native_schema_only", [3, 2]),
    "explicit_zero_row": ("assembled_framed_zero", [4, 2, 3, 2]),
    "zero_width_with_zero_row": ("assembled_framed_zero", []),
    "omit_corrupt": ("mutated_late_local_dictionary_crc", [4, 2]),
}


def compare_ipc(wire, parquet, ordinals):
    assert wire.endswith(EOS)
    source = pa.BufferReader(wire)
    fields = [parquet.schema_arrow.field(ordinal - 1) for ordinal in ordinals]
    expected_schema = pa.schema(fields)
    reader = pa.ipc.open_stream(source)
    assert reader.schema.equals(expected_schema, check_metadata=True)
    batches = list(reader)
    assert source.tell() == len(wire) and len(batches) == parquet.num_row_groups
    for group, batch in enumerate(batches):
        assert batch.num_rows == parquet.metadata.row_group(group).num_rows
        assert batch.num_columns == len(fields)
        for position, field in enumerate(fields):
            expected = parquet.read_row_group(group, columns=[field.name]).column(0).cast(pa.int64())
            assert batch.column(position).cast(pa.int64()).equals(expected.combine_chunks())
    return [batch.num_rows for batch in batches]


def native_arrow():
    """Emit a native Arrow control independently of the Parquet source."""
    schema = pa.schema([FIELDS[3], FIELDS[2], FIELDS[3]])
    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, schema) as writer:
        for cols in [[[-2**63, None, 2**63 - 1], [1, -2, 0], [None, 0, -1]], [[], [], []]]:
            arrays = [pa.array(values, type=pa.int64()).view(field.type)
                      for field, values in zip(schema, cols, strict=True)]
            writer.write_batch(pa.RecordBatch.from_arrays(arrays, schema=schema))
    wire = sink.getvalue().to_pybytes()
    assert wire.endswith(EOS)
    return wire


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    wires, evidence = fixture_inputs()
    native = native_arrow()
    hashes = {name: sha256(wire).hexdigest() for name, wire in wires.items()}
    hashes["native_ordered.arrow"] = sha256(native).hexdigest()
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-projection-ipc-") as folder:
        output = Path(folder)
        for name, wire in wires.items():
            (output / f"{name}.parquet").write_bytes(wire)
        (output / "native_ordered.arrow").write_bytes(native)
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {wire.stem for wire in output.glob("*.arrows")} == set(CASES)
        for name, (key, ordinals) in CASES.items():
            rows = compare_ipc((output / f"{name}.arrows").read_bytes(), PROJECTION["open_parquet"](wires[key]),
                               ordinals)
            print(f"{name}: positional schema and signed counts passed with batch rows {rows}")


if __name__ == "__main__":
    main()
