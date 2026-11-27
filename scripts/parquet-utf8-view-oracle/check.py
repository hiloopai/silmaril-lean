"""Regenerate annotated Parquet cases and compare native Utf8View with PyArrow."""

from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
from runpy import run_path
import struct
import subprocess
import sys

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

assert (version("pyarrow"), version("thrift")) == ("26.0.1", "0.25.0")
here = Path(__file__).resolve().parent
root = here.parents[1]
out = Path(sys.argv[1]).resolve()
out.mkdir(parents=True, exist_ok=True)
thrift = run_path(str(root / "tests/formats/parquet-timestamp-leaf/check-fixtures.py"))
i32, i64, marker = TType.I32, TType.I64, TType.STRUCT
groups = [[None, "", "é", "e\u0301", "雪🙂"], [], [None, "ééééééé", "a\x00b", "界"]]
without_empty = [groups[0], groups[2]]
required_groups = [["雪", "", "é"], ["e\u0301", "🙂"]]


def produce(page_version, batches, nullable=True):
    schema = pa.schema([pa.field("row_id", pa.int32(), nullable=False),
                        pa.field("label", pa.string(), nullable=nullable)])
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=page_version,
                          compression="NONE", column_encoding="PLAIN", use_dictionary=False,
                          write_statistics=False, write_page_checksum=False, store_schema=False) as writer:
        for values in batches:
            writer.write_table(pa.Table.from_arrays([
                pa.array(range(len(values)), pa.int32()), pa.array(values, pa.string()),
            ], schema=schema))
    return sink.getvalue().to_pybytes()


def attach_empty_page(wire):
    """Give the producer's empty group explicit zero-slot V2 page spans."""
    zero = i32, 0
    page = thrift["encode"]({
        1: (i32, 3), 2: zero, 3: zero,
        8: (marker, {**dict.fromkeys(range(1, 7), zero), 7: (TType.BOOL, False)}),
    })
    size, = struct.unpack_from("<I", wire, len(wire) - 8)
    start = len(wire) - 8 - size

    def attach(footer):
        group = thrift["list_field"](footer, 4)[1]
        assert group[3] == (i64, 0)
        group[2] = group[6] = i64, 2 * len(page)
        for ordinal in range(2):
            column = thrift["column_metadata"](footer, group=1, column=ordinal)
            assert column[5] == column[7] == column[9] == (i64, 0)
            assert column[2] == (TType.LIST, (i32, [3]))
            column[2] = TType.LIST, (i32, [3, 0])
            column[6] = column[7] = i64, len(page)
            column[9] = i64, start + ordinal * len(page)

    return thrift["rewrite_footer"](wire[:start] + page + page + wire[start:], attach)


def footer_leaf(wire):
    size, = struct.unpack_from("<I", wire, len(wire) - 8)
    memory = TMemoryBuffer(wire[-8-size:-8])
    footer = thrift["read_struct"](TCompactProtocol(memory))
    assert memory.cstringio_buf.tell() == size
    _, decoy, leaf = thrift["list_field"](footer, 2)
    assert decoy[4][1] == b"row_id" and leaf[4][1] == b"label" and leaf[1] == (i32, 6)
    return leaf


def change_leaf(wire, edit):
    return thrift["rewrite_footer"](wire, lambda footer: edit(thrift["list_field"](footer, 2)[2]))


def verify_pages(wire, page_type, expected, nullable=True):
    with pq.ParquetFile(pa.BufferReader(wire)) as file:
        assert file.schema_arrow.field("label") == pa.field("label", pa.string(), nullable=nullable)
        leaf = file.schema.column(1)
        assert (leaf.physical_type, leaf.max_definition_level, leaf.max_repetition_level) == (
            "BYTE_ARRAY", int(nullable), 0,
        )
        assert file.num_row_groups == len(expected)
        extent = []
        for index, values in enumerate(expected):
            table = file.read_row_group(index, columns=["label"])
            assert table.column(0).to_pylist() == values
            chunk = file.metadata.row_group(index).column(1)
            assert chunk.path_in_schema == "label" and chunk.compression == "UNCOMPRESSED"
            assert not chunk.has_dictionary_page
            start = chunk.data_page_offset
            memory = TMemoryBuffer(wire[start:start + chunk.total_compressed_size])
            header = thrift["read_struct"](TCompactProtocol(memory))
            assert header[1] == (i32, page_type) and 4 not in header
            assert header[2] == header[3]
            body = memory.cstringio_buf.tell()
            assert body + header[3][1] == chunk.total_compressed_size
            if page_type == 0:
                policy = header[5][1]
                assert [policy[i][1] for i in range(1, 5)] == [len(values), 0, 3, 3]
                levels = 4 + struct.unpack_from("<I", wire, start + body)[0] if nullable else 0
            else:
                policy = header[8][1]
                assert [policy[i][1] for i in (1, 2, 3, 4, 6)] == [
                    len(values), values.count(None), len(values), 0, 0,
                ]
                levels = policy[5][1]
            scalar = start + body + levels
            end = start + chunk.total_compressed_size
            cursor = scalar
            for value in values:
                if value is not None:
                    size, = struct.unpack_from("<I", wire, cursor)
                    assert wire[cursor+4:cursor+4+size] == value.encode()
                    cursor += 4 + size
            assert cursor == end
            extent.append((start, scalar))
    return extent


v1 = produce("1.0", without_empty)
unframed = produce("2.0", groups)
with pq.ParquetFile(pa.BufferReader(unframed)) as file:
    assert [file.read_row_group(i, columns=["label"]).column(0).to_pylist()
            for i in range(file.num_row_groups)] == groups
v2 = attach_empty_page(unframed)
required = produce("2.0", required_groups, nullable=False)
for wire in (v1, v2, required):
    leaf = footer_leaf(wire)
    assert leaf[6] == (i32, 0) and leaf[10] == (marker, {1: (marker, {})})
verify_pages(v1, 0, without_empty)
verify_pages(required, 3, required_groups, nullable=False)
header, scalar = verify_pages(v2, 3, groups)[2]
assert (header, scalar) == (142, 168)

logical = change_leaf(v2, lambda leaf: leaf.pop(6))
converted = change_leaf(v2, lambda leaf: leaf.pop(10))
conflict = change_leaf(v2, lambda leaf: leaf.__setitem__(6, (i32, 2)))
wrong = change_leaf(v2, lambda leaf: leaf.__setitem__(10, (marker, {4: (marker, {})})))
payload = change_leaf(v2, lambda leaf: leaf[10][1][1][1].update({1: (i32, 0)}))
for edited in (logical, converted):
    assert verify_pages(edited, 3, groups)[2] == (header, scalar)
assert 6 not in footer_leaf(logical) and 10 not in footer_leaf(converted)
assert footer_leaf(conflict)[6][1] == 2 and footer_leaf(wrong)[10][1] == {4: (marker, {})}
assert footer_leaf(payload)[10][1] == {1: (marker, {1: (i32, 0)})}

assert v2[scalar+4:scalar+6] == "é".encode()
bad_text = v2[:scalar+4] + b"\xff" + v2[scalar+5:]
bad_length = v2[:scalar] + struct.pack("<I", 2**31) + v2[scalar+4:]


def erase_annotations(leaf):
    leaf.pop(6)
    leaf.pop(10)


missing = change_leaf(v2, erase_annotations)
opaque = change_leaf(bad_text, erase_annotations)
assert 6 not in footer_leaf(missing) and 10 not in footer_leaf(missing)
for wire, damage in ((bad_text, "text"), (bad_length, "length")):
    with pq.ParquetFile(pa.BufferReader(wire)) as file:
        assert [file.read_row_group(i, columns=["label"]).column(0).to_pylist() for i in range(2)] == groups[:2]
        try:
            group = file.read_row_group(2, columns=["label"])
            group.validate(full=True)
            group.column(0).to_pylist()
        except (ValueError, OSError):
            pass
        else:
            raise AssertionError(f"PyArrow accepted the damaged {damage} group")

inputs = {
    "v1": v1, "v2": v2, "required": required, "logical": logical, "converted": converted,
    "missing": missing, "conflict": conflict, "wrong-logical": wrong, "logical-payload": payload,
    "bad-text": bad_text, "bad-length": bad_length, "opaque": opaque,
}
for name, wire in inputs.items():
    (out / f"{name}.parquet").write_bytes(wire)
print(f"Thrift: later selected header {header}, first PLAIN length at {scalar}, invalid text at slot 1", flush=True)
subprocess.run(
    [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
     "--run", str(here / "Emit.lean"), str(out), str(header)], cwd=root, check=True,
)

for name in ("v1", "v2", "required", "logical", "converted", "opaque"):
    ipc = (out / f"{name}.arrows").read_bytes()
    assert ipc.endswith(b"\xff\xff\xff\xff\x00\x00\x00\x00")
    carrier = pa.BufferReader(ipc)
    with pq.ParquetFile(out / f"{name}.parquet") as file, pa.ipc.open_stream(carrier) as reader:
        kind = pa.binary_view() if name == "opaque" else pa.string_view()
        assert reader.schema == pa.schema([pa.field("label", kind, nullable=name != "required")])
        for index, batch in zip(range(file.num_row_groups), reader, strict=True):
            expected = file.read_row_group(index, columns=["label"]).column(0).to_pylist()
            assert batch.num_rows == len(expected) and batch.column(0).to_pylist() == expected
        assert carrier.tell() == len(ipc)
for name in inputs.keys() - {"v1", "v2", "required", "logical", "converted", "opaque"}:
    assert not (out / f"{name}.arrows").exists()
artifacts = [out / f"{name}.parquet" for name in inputs]
artifacts += [out / f"{name}.arrows" for name in ("v1", "v2", "required", "logical", "converted", "opaque")]
digests = {path.name: sha256(path.read_bytes()).hexdigest() for path in artifacts}
assert digests == json.loads((here / "fixtures.json").read_text(encoding="utf-8"))
for name, digest in digests.items():
    print(f"{digest}  {name}")
print("PyArrow matched five Utf8View streams and the opaque BinaryView control through EOS")
