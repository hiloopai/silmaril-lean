"""Compare actual Lean nested IPC with pinned, independently decoded Parquet."""

from hashlib import sha256
from importlib.metadata import version
import json
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
PARQUET = runpy.run_path(str(HERE.parent / "parquet-timestamp-scalar-dispatch-oracle/check.py"))
THRIFT, MIXED, FRAMES, HYBRID, ASSEMBLE = (PARQUET[name] for name in (
    "THRIFT", "MIXED", "FRAMES", "HYBRID", "ASSEMBLE_GROUPS"))
IPC = runpy.run_path(str(HERE.parent / "arrow-struct-int32-oracle/check.py"))
MIN, MAX = -(2**63), 2**63 - 1
LEFT, RIGHT = "signed", "広い"
FIELD = pa.field("座標", pa.struct([
    pa.field(LEFT, pa.int32(), nullable=False), pa.field(RIGHT, pa.int64()),
]))
ROWS = [
    [(-2**31, MIN), (1, None), None, (2, MAX), (-99, 2**42), (0, -2**42),
     None, (2**31 - 1, 2147483648), (77, None), (4, -2147483649), (5, 0), None],
    [(7, -2**55), (-9, None), None, (10, 2**55), (3, MIN), None,
     (12, 17), (-4, None), (0, MAX), None, (8, -198), (1, 42)],
    [None, (42, None)],
]


def produce(field, groups):
    schema = pa.schema([field])
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, compression="NONE", use_dictionary=False, data_page_version="1.0",
                          data_page_size=16, write_batch_size=2, write_page_checksum=False,
                          store_schema=False) as writer:
        for group in groups:
            rows = [None if row is None else {LEFT: row[0], RIGHT: row[1]} for row in group]
            writer.write_table(pa.Table.from_arrays([pa.array(rows, type=field.type)], schema=schema))
    return sink.getvalue().to_pybytes()


def inspect(wire, groups):
    footer = MIXED["metadata"](wire)
    root, parent, first, second = THRIFT["list_field"](footer, 2)
    assert root[5] == (TType.I32, 1) and parent[5] == (TType.I32, 2)
    assert parent[3] == (TType.I32, 1)
    assert [item[4][1].decode() for item in (parent, first, second)] == [FIELD.name, LEFT, RIGHT]
    for leaf, physical, requiredness in zip((first, second), (1, 2), (0, 1), strict=True):
        assert leaf[1] == (TType.I32, physical) and leaf[3] == (TType.I32, requiredness)
        assert not (set(leaf) & {6, 10})
    assert footer[3][1] == sum(map(len, groups))
    parquet = pq.ParquetFile(pa.BufferReader(wire))
    assert list(parquet.schema_arrow) == [FIELD]
    assert parquet.num_row_groups == len(groups)
    result = []
    for ordinal, rows in enumerate(groups):
        rowgroup = parquet.metadata.row_group(ordinal)
        assert rowgroup.num_rows == len(rows)
        actual = parquet.read_row_group(ordinal).column(0).to_pylist()
        assert actual == [None if row is None else {LEFT: row[0], RIGHT: row[1]} for row in rows]
        columns = []
        for position, (name, width, physical, code) in enumerate(((LEFT, 1, 1, "i"), (RIGHT, 2, 2, "q"))):
            column = THRIFT["column_metadata"](footer, ordinal, position)
            assert column[1][1] == physical and column[4][1] == 0 and column[5][1] == len(rows)
            assert THRIFT["list_field"](column, 3) == [FIELD.name.encode(), name.encode()]
            assert not (set(column) & {10, 11})
            start, stop = MIXED["column_extent"](column)
            assert start == rowgroup.column(position).data_page_offset
            assert stop - start == rowgroup.column(position).total_compressed_size
            observed = []
            cursor = 0
            for header_offset, header, payload, body in FRAMES(wire, start, stop):
                assert header[1][1] == 0 and 4 not in header
                assert header[2][1] == header[3][1] == len(body)
                info = header[5][1]
                count = info[1][1]
                assert [info[i][1] for i in (2, 3, 4)] == [0, 3, 3]
                extent, = struct.unpack_from("<I", body)
                levels = HYBRID(body[4:4 + extent], width, count)
                segment = rows[cursor:cursor + count]
                assert levels == [0 if row is None else 1 if row[position] is None else width for row in segment]
                signed = [row[position] for row in segment if row is not None and row[position] is not None]
                assert body[4 + extent:] == struct.pack(f"<{len(signed)}{code}", *signed)
                observed.append((header_offset, payload, extent, levels))
                cursor += count
            assert cursor == len(rows)
            columns.append(observed)
        result.append(columns)
    return result


def empty_group():
    footer = MIXED["metadata"](produce(FIELD, [[]]))
    group, = THRIFT["list_field"](footer, 4)
    chunks = THRIFT["list_field"](group, 1)
    header = {1: (TType.I32, 0), 2: (TType.I32, 4), 3: (TType.I32, 4),
              5: (TType.STRUCT, {i: (TType.I32, value) for i, value in enumerate((0, 0, 3, 3), 1)})}
    page = THRIFT["encode"](header) + b"\0" * 4
    for position, chunk in enumerate(chunks):
        metadata = chunk[3][1]
        offset = 4 + position * len(page)
        metadata[2] = TType.LIST, (TType.I32, [0, 3])
        metadata[6] = metadata[7] = TType.I64, len(page)
        metadata[9] = chunk[2] = TType.I64, offset
    group[2] = TType.I64, len(page) * len(chunks)
    if 6 in group:
        group[6] = group[2]
    footer[6] = TType.STRING, b"Constructed Thrift zero-row V1 group"
    encoded = THRIFT["encode"](footer)
    return b"PAR1" + page * len(chunks) + encoded + struct.pack("<I", len(encoded)) + b"PAR1"


def fixtures():
    clean = produce(FIELD, ROWS)
    captures = inspect(clean, ROWS)
    assert any([len(page[3]) for page in pair[0]] != [len(page[3]) for page in pair[1]] for pair in captures)
    for header, payload, extent, levels in captures[1][1]:
        if clean[payload + 4] == 3 and 1 in levels:
            index = levels.index(1)
            position, shift = payload + 5 + index // 4, 2 * (index % 4)
            damaged = bytearray(clean)
            damaged[position] = (damaged[position] & ~(3 << shift)) | (2 << shift)
            changed = HYBRID(damaged[payload + 4:payload + 4 + extent], 2, len(levels))
            assert changed == levels[:index] + [2] + levels[index + 1:]
            break
    else:
        raise AssertionError("no packed optional wide null to mutate")
    broken = pq.ParquetFile(pa.BufferReader(damaged))
    try:
        broken.read_row_group(1)
    except (OSError, pa.ArrowInvalid):
        pass
    else:
        raise AssertionError("independent producer admitted the short wide payload")
    parts = [(clean, 0), (empty_group(), 0), (clean, 1), (clean, 2)]
    assembled = ASSEMBLE(parts)
    inspect(assembled, [ROWS[0], [], *ROWS[1:]])
    for group, (original, index) in enumerate(parts):
        for column in (0, 1):
            span = THRIFT["column_metadata"](MIXED["metadata"](assembled), group, column)
            source_span = THRIFT["column_metadata"](MIXED["metadata"](original), index, column)
            start, stop = MIXED["column_extent"](span)
            lo, hi = MIXED["column_extent"](source_span)
            assert assembled[start:stop] == original[lo:hi]
    annotated = FIELD.with_type(pa.struct([FIELD.type[0], FIELD.type[1].with_type(pa.timestamp("us"))]))
    optional = FIELD.with_type(pa.struct([FIELD.type[0].with_nullable(True), FIELD.type[1]]))
    schema_only = produce(FIELD, [])
    inspect(schema_only, [])
    return {
        "native": clean, "schema_only": schema_only, "assembled_empty": assembled,
        "annotated_wide": produce(annotated, []), "optional_left": produce(optional, []),
        "edited_late": bytes(damaged),
    }, header


def hashes(inputs):
    return {name: sha256(data).hexdigest() for name, data in inputs.items()}


def main():
    assert platform.python_version() == "3.13.5" and pa.__version__ == "26.0.1"
    assert version("thrift") == "0.25.0"
    inputs, offset = fixtures()
    assert hashes(inputs) == json.loads((HERE / "fixtures.json").read_text())
    with tempfile.TemporaryDirectory(prefix="parquet-nested-point-ipc-") as output:
        directory = Path(output)
        for name, wire in inputs.items():
            (directory / f"{name}.parquet").write_bytes(wire)
        subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
                        str(HERE / "Emit.lean"), output, str(offset)], cwd=ROOT, check=True)
        for name, groups in (("native", ROWS), ("schema_only", []),
                             ("assembled_empty", [ROWS[0], [], *ROWS[1:]])):
            slots = [[(False, None, None) if row is None else (True, *row) for row in group] for group in groups]
            wire = (directory / f"{name}.arrow").read_bytes()
            IPC["check_pyarrow"](wire, FIELD, slots)
            IPC["inspect_wire"](wire, FIELD, slots, canonical=True)
    print("PyArrow and independent Thrift/bitmap checks verified three actual Lean IPC streams")


if __name__ == "__main__":
    main()
