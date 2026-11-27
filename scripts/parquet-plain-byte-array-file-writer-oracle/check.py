"""Check actual single-leaf Lean PLAIN BYTE_ARRAY files in PyArrow and Thrift."""

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
    "optional": ("clés", True, [None, b"", RAW, None, LONG]),
    "required": ("raw", False, [b"", RAW, LONG]),
    "optional-empty": ("empty", True, []),
    "required-empty": ("empty", False, []),
}


def check_wire(thrift, wire, name, nullable, values):
    assert wire[:4] == wire[-4:] == b"PAR1"
    footer_size, = struct.unpack_from("<I", wire, len(wire) - 8)
    footer_start = len(wire) - 8 - footer_size
    footer_buf = TMemoryBuffer(wire[footer_start:-8])
    footer = thrift["read_struct"](TCompactProtocol(footer_buf))
    assert footer_buf.cstringio_buf.tell() == footer_size
    root, leaf = thrift["list_field"](footer, 2)
    assert root == {4: (TType.STRING, b"schema"), 5: (TType.I32, 1)}
    assert leaf == {1: (TType.I32, 6), 3: (TType.I32, int(nullable)), 4: (TType.STRING, name.encode())}
    assert footer[1] == (TType.I32, 1) and footer[3] == (TType.I64, len(values))
    assert set(footer) == {1, 2, 3, 4}
    (group,) = thrift["list_field"](footer, 4)
    (chunk,) = thrift["list_field"](group, 1)
    chunk_size = footer_start - 4
    assert group == {1: (TType.LIST, (TType.STRUCT, [chunk])),
                     2: (TType.I64, chunk_size), 3: (TType.I64, len(values))}
    assert chunk == {2: (TType.I64, 0), 3: (TType.STRUCT, {
        1: (TType.I32, 6), 2: (TType.LIST, (TType.I32, [0, 3])),
        3: (TType.LIST, (TType.STRING, [name.encode()])), 4: (TType.I32, 0),
        5: (TType.I64, len(values)), 6: (TType.I64, chunk_size), 7: (TType.I64, chunk_size),
        9: (TType.I64, 4),
    })}
    page_buf = TMemoryBuffer(wire[4:footer_start])
    page = thrift["read_struct"](TCompactProtocol(page_buf))
    header_size = page_buf.cstringio_buf.tell()
    body = wire[4 + header_size:footer_start]
    assert page == {
        1: (TType.I32, 0), 2: (TType.I32, len(body)), 3: (TType.I32, len(body)),
        5: (TType.STRUCT, {1: (TType.I32, len(values)), 2: (TType.I32, 0),
                           3: (TType.I32, 3), 4: (TType.I32, 3)}),
    }
    levels = bytes(octet for slot in values for octet in (2, int(slot is not None)))
    prefix = struct.pack("<I", len(levels)) + levels if nullable else b""
    scalars = b"".join(struct.pack("<I", len(slot)) + slot for slot in values if slot is not None)
    assert body == prefix + scalars


def check_pyarrow(wire, name, nullable, values):
    schema = pa.schema([pa.field(name, pa.binary(), nullable=nullable)])
    with pq.ParquetFile(pa.BufferReader(wire)) as source:
        assert source.schema_arrow.equals(schema, check_metadata=True)
        assert source.num_row_groups == 1 and source.metadata.num_rows == len(values)
        column = source.schema.column(0)
        assert column.physical_type == "BYTE_ARRAY" and column.logical_type.type == "NONE"
        assert column.max_repetition_level == 0 and column.max_definition_level == int(nullable)
        group = source.read_row_group(0)
        group.validate(full=True)
        assert group.column(0).to_pylist() == values


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
    for stem, (name, nullable, values) in CASES.items():
        wire = (out / f"{stem}.parquet").read_bytes()
        check_wire(thrift, wire, name, nullable, values)
        check_pyarrow(wire, name, nullable, values)
    pins = json.loads((HERE / "sha256.json").read_text(encoding="utf-8"))
    assert set(pins) == {f"{stem}.parquet" for stem in CASES}
    for name, digest in pins.items():
        actual = sha256((out / name).read_bytes()).hexdigest()
        assert actual == digest, f"{name}: fixture hash changed"
        print(f"{actual}  {name}")
    print("PyArrow and Thrift verified all physical fields, page and chunk extents, and nullable octets.")


if __name__ == "__main__":
    main()
