"""Check Lean-emitted PLAIN BYTE_ARRAY row groups with PyArrow and Thrift."""

import argparse
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


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
RAW = b"\xff\0\x80"
LONG = bytes(range(256))
CASES = {
    "optional": ("clés", True, [[None, b"", RAW], [], [None, LONG], []]),
    "required": ("raw", False, [[b"", RAW], [], [LONG, b"", RAW]]),
    "schema-only": ("empty", True, []),
    "explicit-empty": ("empty", True, [[]]),
    "singleton": ("clés", True, [[None, b"", RAW, None, LONG]]),
}


def parse_struct(read_struct, wire):
    buffer = TMemoryBuffer(wire)
    fields = read_struct(TCompactProtocol(buffer))
    return fields, buffer.cstringio_buf.tell()


def check_group(thrift, wire, footer_start, start, group, name, nullable, slots):
    (chunk,) = thrift["list_field"](group, 1)
    metadata = chunk[3][1]
    chunk_size = metadata[7][1]
    stop = start + chunk_size
    assert start < stop <= footer_start
    assert group == {
        1: (TType.LIST, (TType.STRUCT, [chunk])),
        2: (TType.I64, chunk_size), 3: (TType.I64, len(slots)),
    }
    assert chunk == {2: (TType.I64, 0), 3: (TType.STRUCT, {
        1: (TType.I32, 6), 2: (TType.LIST, (TType.I32, [0, 3])),
        3: (TType.LIST, (TType.STRING, [name.encode()])), 4: (TType.I32, 0),
        5: (TType.I64, len(slots)), 6: (TType.I64, chunk_size), 7: (TType.I64, chunk_size),
        9: (TType.I64, start),
    })}
    page, header_size = parse_struct(thrift["read_struct"], wire[start:stop])
    body = wire[start + header_size:stop]
    assert page == {
        1: (TType.I32, 0), 2: (TType.I32, len(body)), 3: (TType.I32, len(body)),
        5: (TType.STRUCT, {1: (TType.I32, len(slots)), 2: (TType.I32, 0),
                           3: (TType.I32, 3), 4: (TType.I32, 3)}),
    }
    levels = bytes(octet for slot in slots for octet in (2, int(slot is not None)))
    prefix = struct.pack("<I", len(levels)) + levels if nullable else b""
    scalars = b"".join(struct.pack("<I", len(slot)) + slot for slot in slots if slot is not None)
    assert body == prefix + scalars
    return stop


def check_wire(thrift, wire, name, nullable, groups):
    assert wire[:4] == wire[-4:] == b"PAR1"
    footer_size, = struct.unpack_from("<I", wire, len(wire) - 8)
    footer_start = len(wire) - 8 - footer_size
    assert footer_start >= 4
    footer, consumed = parse_struct(thrift["read_struct"], wire[footer_start:-8])
    assert consumed == footer_size
    assert set(footer) == {1, 2, 3, 4}
    assert footer[1] == (TType.I32, 1)
    assert footer[3] == (TType.I64, sum(map(len, groups)))
    root, leaf = thrift["list_field"](footer, 2)
    assert root == {4: (TType.STRING, b"schema"), 5: (TType.I32, 1)}
    assert leaf == {1: (TType.I32, 6), 3: (TType.I32, int(nullable)), 4: (TType.STRING, name.encode())}
    cursor = 4
    for group, slots in zip(thrift["list_field"](footer, 4), groups, strict=True):
        cursor = check_group(thrift, wire, footer_start, cursor, group, name, nullable, slots)
    assert cursor == footer_start


def check_pyarrow(wire, name, nullable, groups):
    schema = pa.schema([pa.field(name, pa.binary(), nullable=nullable)])
    with pq.ParquetFile(pa.BufferReader(wire)) as source:
        assert source.schema_arrow.equals(schema, check_metadata=True)
        assert source.num_row_groups == len(groups)
        assert source.metadata.num_rows == sum(map(len, groups))
        column = source.schema.column(0)
        assert column.physical_type == "BYTE_ARRAY" and column.logical_type.type == "NONE"
        assert column.max_repetition_level == 0 and column.max_definition_level == int(nullable)
        for index, expected in enumerate(groups):
            group = source.read_row_group(index)
            group.validate(full=True)
            assert group.num_rows == len(expected)
            assert group.column(0).to_pylist() == expected
        table = source.read()
        table.validate(full=True)
        assert table.column(0).to_pylist() == [slot for group in groups for slot in group]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
    assert sys.version_info[:2] == (3, 13) and version("thrift") == "0.25.0"
    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
         "--run", str(HERE / "Write.lean"), str(out)],
        cwd=ROOT, check=True,
    )
    thrift = run_path(str(ROOT / "tests/formats/parquet-timestamp-leaf/check-fixtures.py"))
    pins = json.loads((HERE / "sha256.json").read_text(encoding="utf-8"))
    assert set(pins) == {f"{stem}.parquet" for stem in CASES}
    for stem, case in CASES.items():
        name = f"{stem}.parquet"
        wire = (out / name).read_bytes()
        check_wire(thrift, wire, *case)
        check_pyarrow(wire, *case)
        actual = sha256(wire).hexdigest()
        assert actual == pins[name], f"{name}: fixture hash changed"
        print(f"{actual}  {name}")
    print("PyArrow and Thrift verified all five files, including zero groups and framed empty groups.")


if __name__ == "__main__":
    main()
