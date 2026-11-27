"""Check native mixed Parquet files independently with PyArrow and Thrift."""

import argparse
from hashlib import sha256
from importlib.metadata import version
import os
from pathlib import Path
from runpy import run_path
import struct
import subprocess

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
RAW = b"\xff\0\x80"
LONG = b"*" * 20
CASES = {
    "required": (("id", False, [-2**31, 0, 2**31 - 1]), ("raw", False, [b"", RAW, LONG])),
    "mixed": (("ordinal", False, [-2**31, 0, 17, 2**31 - 1, -1]),
              ("payload", True, [None, b"", RAW, None, LONG])),
    "optional-int": (("count", True, [-7, None, 2]), ("raw", False, [RAW, b"", LONG])),
    "both-optional": (("count", True, [None, 5, None]), ("clé", True, [None, b"", RAW])),
    "empty-group": (("id", False, []), ("raw", True, [])),
}
PINS = {
    "both-optional": "c5fb72482e34b37c8db0e87aaf02cc88af8ee80f9483c58758733dd976aeed9f",
    "empty-group": "16d78c2fc305ee765281ca1c62516ce6a8f5cc67d18e1a3303c8faa0a8cbc8e9",
    "mixed": "67bcdf7267686f83c2ac03e55194bc1865dc9000ad64dc33b2bd6373bcf903af",
    "optional-int": "640ac7a13fb576275d97fc67cd6d0edb852b3556382254c221b60fea7777fd03",
    "required": "7e9b22dbea2e31b60f732ff7fd432e502dad6cb42756c0515b74d8154ba0b3c5",
}


def body(nullable, slots, physical):
    levels = bytes(octet for slot in slots for octet in (2, int(slot is not None)))
    prefix = struct.pack("<I", len(levels)) + levels if nullable else b""
    if physical == 1:
        return prefix + b"".join(struct.pack("<i", slot) for slot in slots if slot is not None)
    return prefix + b"".join(struct.pack("<i", len(slot)) + slot for slot in slots if slot is not None)


def check_group(thrift, wire, cursor, group, fields, slots, physical_order, cuts):
    count = len(slots[0])
    assert len(slots[1]) == count and group[3] == (TType.I64, count)
    chunks = thrift["list_field"](group, 1)
    start = cursor
    for chunk, (name, nullable), values, physical, page_counts in zip(
        chunks, fields, slots, physical_order, cuts, strict=True
    ):
        assert chunk[2] == (TType.I64, 0)
        column = chunk[3][1]
        chunk_size = column[7][1]
        assert column == {
            1: (TType.I32, physical), 2: (TType.LIST, (TType.I32, [0, 3])),
            3: (TType.LIST, (TType.STRING, [name.encode()])), 4: (TType.I32, 0),
            5: (TType.I64, count), 6: (TType.I64, chunk_size), 7: (TType.I64, chunk_size),
            9: (TType.I64, cursor),
        }
        stop = cursor + chunk_size
        first_slot = 0
        for page_count in page_counts:
            assert cursor < stop
            page_memory = TMemoryBuffer(wire[cursor:stop])
            header = thrift["read_struct"](TCompactProtocol(page_memory))
            size = header[3][1]
            data = cursor + page_memory.cstringio_buf.tell()
            assert data + size <= stop
            payload = wire[data:data + size]
            assert header == {
                1: (TType.I32, 0), 2: (TType.I32, len(payload)), 3: (TType.I32, len(payload)),
                5: (TType.STRUCT, {1: (TType.I32, page_count), 2: (TType.I32, 0),
                                   3: (TType.I32, 3), 4: (TType.I32, 3)}),
            }
            after = first_slot + page_count
            assert payload == body(nullable, values[first_slot:after], physical)
            cursor = data + size
            first_slot = after
        assert first_slot == count and cursor == stop
    assert group[2] == (TType.I64, cursor - start)
    return cursor


def check_wire_groups(thrift, wire, fields, expected_groups, physical_order=(1, 6), page_cuts=None):
    assert wire[:4] == wire[-4:] == b"PAR1"
    size, = struct.unpack_from("<I", wire, len(wire) - 8)
    start = len(wire) - 8 - size
    footer_memory = TMemoryBuffer(wire[start:-8])
    footer = thrift["read_struct"](TCompactProtocol(footer_memory))
    assert footer_memory.cstringio_buf.tell() == size

    count = sum(len(slots[0]) for slots in expected_groups)
    root, *leaves = thrift["list_field"](footer, 2)
    assert footer[1] == (TType.I32, 1) and footer[3] == (TType.I64, count)
    assert root == {4: (TType.STRING, b"schema"), 5: (TType.I32, 2)}
    for leaf, (name, nullable), physical in zip(leaves, fields, physical_order, strict=True):
        assert leaf == {1: (TType.I32, physical), 3: (TType.I32, int(nullable)), 4: (TType.STRING, name.encode())}
    cursor = 4
    if page_cuts is None:
        page_cuts = [[[len(column)] for column in slots] for slots in expected_groups]
    for group, slots, cuts in zip(thrift["list_field"](footer, 4), expected_groups, page_cuts, strict=True):
        cursor = check_group(thrift, wire, cursor, group, fields, slots, physical_order, cuts)
    assert cursor == start


def check_arrow_groups(wire, fields, expected_groups, physical_order=(1, 6)):
    types = {1: pa.int32(), 6: pa.binary()}
    schema = pa.schema([
        pa.field(name, types[physical], nullable=nullable)
        for (name, nullable), physical in zip(fields, physical_order, strict=True)
    ])
    with pq.ParquetFile(pa.BufferReader(wire)) as source:
        assert source.num_row_groups == len(expected_groups) and source.schema_arrow.equals(schema)
        for index in range(2):
            leaf = source.schema.column(index)
            assert leaf.logical_type.type == "NONE" and leaf.max_repetition_level == 0
            assert leaf.max_definition_level == int(fields[index][1])
        for ordinal, slots in enumerate(expected_groups):
            table = source.read_row_group(ordinal)
            table.validate(full=True)
            assert [column.to_pylist() for column in table.columns] == list(slots)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
    assert version("thrift") == "0.25.0"
    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Write.lean"), str(out)],
        cwd=ROOT, check=True,
    )
    thrift = run_path(str(ROOT / "tests/formats/parquet-timestamp-leaf/check-fixtures.py"))
    for name, columns in CASES.items():
        path = out / f"{name}.parquet"
        wire = path.read_bytes()
        fields = [(name, nullable) for name, nullable, _ in columns]
        groups = [[slots for _, _, slots in columns]]
        check_wire_groups(thrift, wire, fields, groups)
        check_arrow_groups(wire, fields, groups)
        digest = sha256(wire).hexdigest()
        print(f"{digest}  {path.name} ({len(columns[0][2])} rows)")
        assert digest == PINS[name], f"{path.name}: fixture hash changed"
    print("PyArrow and Thrift independently checked all five original Lean files.")


if __name__ == "__main__":
    main()
