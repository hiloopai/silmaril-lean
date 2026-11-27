"""Assemble PyArrow TIMESTAMP chunks with differing codecs and encodings, then compare native IPC."""

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
import zlib

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
FALLBACK = runpy.run_path(str(HERE.parent / "parquet-timestamp-snappy-fallback-oracle/check.py"))
DICTIONARY = FALLBACK["DICTIONARY"]
THRIFT = FALLBACK["THRIFT"]
MIN, MAX = FALLBACK["MIN"], FALLBACK["MAX"]
BATCH = FALLBACK["BATCH"]
PROFILES = [
    ("NONE", "1.0", [0]),
    ("SNAPPY", "2.0", [8]),
    ("NONE", "2.0", [8]),
    ("SNAPPY", "1.0", [0]),
    ("NONE", "1.0", [8, 0, 0]),
    ("SNAPPY", "2.0", [8, 0, 0]),
]


def groups():
    fallback = FALLBACK["groups"]()
    return [[MIN, None, -1, MAX], [None, -4, -4, 20, None, 20], [-8, None, -8, 7],
            [MAX, -13, None, MIN], *fallback]


def produce_plain(unit, zone, codec, page_version, rows):
    schema = pa.schema([pa.field("decoy", pa.int32(), nullable=False),
                        pa.field("ticks", pa.timestamp(unit, zone))])
    target = pa.BufferOutputStream()
    with pq.ParquetWriter(target, schema, version="2.6", data_page_version=page_version,
                          compression=codec, use_dictionary=False, store_schema=False,
                          write_statistics=False) as writer:
        for group in rows:
            table = pa.Table.from_arrays([pa.array(range(len(group)), type=pa.int32()),
                                          pa.array(group, type=pa.int64()).view(schema.field(1).type)],
                                         schema=schema)
            writer.write_table(table)
    return target.getvalue().to_pybytes()


def metadata(wire):
    size, = struct.unpack_from("<I", wire, len(wire) - 8)
    cursor = TMemoryBuffer(wire[-8 - size:-8])
    footer = THRIFT["read_struct"](TCompactProtocol(cursor))
    assert cursor.cstringio_buf.tell() == size
    return footer


def column_extent(column):
    offset = column.get(11, column[9])[1]
    return offset, offset + column[7][1]


def relocate_offset(fields, index, delta):
    kind, value = fields[index]
    assert kind == TType.I64 and value >= 4
    fields[index] = kind, value + delta


def assemble(unit, zone, rows):
    """Copy original chunks verbatim. Rewrite the footer's absolute offsets and group list."""
    body = bytearray(b"PAR1")
    output_groups = []
    base = None
    for ordinal, ((codec, page_version, tags), group_rows) in enumerate(zip(PROFILES, rows, strict=True)):
        if tags == [0]:
            source = produce_plain(unit, zone, codec, page_version, [group_rows])
        else:
            source = DICTIONARY["produce"](unit, zone, page_version, codec=codec, groups=[group_rows],
                                           checksum=codec == "SNAPPY", fallback=0 in tags,
                                           fallback_batch_size=BATCH)
        assert DICTIONARY["read_group"](pq.ParquetFile(pa.BufferReader(source), page_checksum_verification=True),
                                        0) == group_rows
        footer = metadata(source)
        if base is None:
            base = footer
        else:
            assert base[2] == footer[2]
        group, = THRIFT["list_field"](footer, 4)
        group_start = len(body)
        for chunk in THRIFT["list_field"](group, 1):
            column = chunk[3][1]
            assert not (set(chunk) & {1, 4, 5, 6, 7}) and not (set(column) & {10, 14, 15})
            start, stop = column_extent(column)
            delta = len(body) - start
            body.extend(source[start:stop])
            relocate_offset(column, 9, delta)
            if 11 in column:
                relocate_offset(column, 11, delta)
            if chunk[2][1] != 0:
                relocate_offset(chunk, 2, delta)
            assert body[len(body) - (stop - start):] == source[start:stop]
        if 5 in group:
            group[5] = TType.I64, group_start
        if 7 in group:
            group[7] = TType.I16, ordinal
        output_groups.append(group)
    base[3] = TType.I64, sum(map(len, rows))
    base[4] = TType.LIST, (TType.STRUCT, output_groups)
    base[6] = TType.STRING, b"Fixture assembly from PyArrow 26.0.1 column chunks"
    footer = THRIFT["encode"](base)
    return bytes(body) + footer + struct.pack("<I", len(footer)) + b"PAR1"


def inspect(wire, rows):
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.metadata.num_row_groups == len(rows)
    assert [DICTIONARY["read_group"](parquet, i) for i in range(len(rows))] == rows
    footer = metadata(wire)
    frames = []
    for i, (codec, version, tags) in enumerate(PROFILES):
        column = THRIFT["column_metadata"](footer, i, 1)
        assert column[4] == (TType.I32, 1 if codec == "SNAPPY" else 0)
        start, stop = column_extent(column)
        cursor = TMemoryBuffer(wire[start:stop])
        protocol = TCompactProtocol(cursor)
        data, dictionary = [], False
        for ordinal in range(len(tags) + (tags[0] == 8)):
            offset = start + cursor.cstringio_buf.tell()
            header = THRIFT["read_struct"](protocol)
            payload = start + cursor.cstringio_buf.tell()
            stored = cursor.readAll(header[3][1])
            if 4 in header:
                assert header[4][1] % 2**32 == zlib.crc32(stored)
            if header[1][1] == 2:
                assert ordinal == 0 and column[11][1] == offset and header[7][1][2][1] == 0
                dictionary = True
            else:
                if not data:
                    assert column[9][1] == offset
                assert header[1][1] == (0 if version == "1.0" else 3)
                info, tag = (5, 2) if version == "1.0" else (8, 4)
                data.append((offset, header, payload, stored, (info, tag)))
        assert start + cursor.cstringio_buf.tell() == stop
        assert [header[info][1][tag][1] for _, header, _, _, (info, tag) in data] == tags
        assert dictionary == (tags[0] == 8)
        print(f"group {i}: {codec}, V{version[0]}, leading dictionary {dictionary}, data tags {tags}")
        frames.append(data)
    return frames


def retag(wire, data, tag):
    start, header, payload, _, (info, field) = data
    header[info][1][field] = TType.I32, tag
    changed = THRIFT["encode"](header)
    assert len(changed) == payload - start
    assert THRIFT["read_struct"](TCompactProtocol(TMemoryBuffer(changed)))[info][1][field][1] == tag
    return wire[:start] + changed + wire[payload:]


def fixtures():
    rows = groups()
    utc = assemble("ns", "UTC", rows)
    local = assemble("us", None, rows)
    inspect(utc, rows)
    frames = inspect(local, rows)

    def unsupported_codec(footer):
        THRIFT["column_metadata"](footer, 2, 1)[4] = TType.I32, 2

    unknown_codec = THRIFT["rewrite_footer"](local, unsupported_codec)
    unknown_tag = retag(local, frames[3][0], 5)
    after_fallback = retag(local, frames[4][-1], 8)
    offset, header, start, stored, _ = frames[5][-1]
    stored_crc = header[4][1] % 2**32
    checksum_failure = local[:start] + bytes([stored[0] ^ 1]) + local[start + 1:]
    actual_crc = zlib.crc32(checksum_failure[start:start + len(stored)])
    corrupted = pq.ParquetFile(pa.BufferReader(checksum_failure), page_checksum_verification=True)
    assert [DICTIONARY["read_group"](corrupted, i) for i in range(5)] == rows[:5]
    try:
        DICTIONARY["read_group"](corrupted, 5)
    except (pa.ArrowException, OSError) as error:
        assert "CRC" in str(error)
    else:
        raise AssertionError("PyArrow accepted bad stored CRC")
    page_less = produce_plain("us", None, "NONE", "2.0", [rows[0], []])
    empty = THRIFT["column_metadata"](metadata(page_less), 1, 1)
    assert empty[5][1] == empty[6][1] == empty[7][1] == empty[9][1] == 0
    schema_only = produce_plain("us", None, "NONE", "2.0", [])
    assert pq.ParquetFile(pa.BufferReader(schema_only)).metadata.num_row_groups == 0
    files = {"utc": utc, "local": local, "schema_only": schema_only, "page_less": page_less,
             "unknown_codec": unknown_codec, "unknown_tag": unknown_tag,
             "after_fallback": after_fallback, "checksum_failure": checksum_failure}
    return files, [frames[4][-1][0], offset, stored_crc, actual_crc]


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    rows = groups()
    with tempfile.TemporaryDirectory(prefix="timestamp-mixed-groups-") as temporary:
        directory = Path(temporary)
        for name, wire in files.items():
            (directory / (name + ".parquet")).write_bytes(wire)
        for index, group in enumerate(rows):
            (directory / f"rows-{index}.txt").write_text("\n".join("null" if v is None else str(v) for v in group))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(directory),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in directory.glob("*.arrows")} == {"utc", "local", "schema_only"}
        for name, unit, zone, expected in (("utc", "ns", "UTC", rows), ("local", "us", None, rows),
                                           ("schema_only", "us", None, [])):
            FALLBACK["verify_ipc"](name, files[name], (directory / (name + ".arrows")).read_bytes(),
                                   unit, zone, expected)


if __name__ == "__main__":
    main()
