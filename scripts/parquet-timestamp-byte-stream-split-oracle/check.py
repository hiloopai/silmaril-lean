"""Check selected TIMESTAMP BYTE_STREAM_SPLIT against the pinned PyArrow producer."""

from copy import deepcopy
from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
import platform
import random
import runpy
import struct
import subprocess
import tempfile
import zlib

import pyarrow as pa
from thrift.Thrift import TType

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DELTA = runpy.run_path(str(HERE.parent / "parquet-timestamp-delta-oracle/check.py"))
OPEN, READ, HYBRID, VERIFY_IPC = (DELTA[name] for name in ("OPEN", "READ", "HYBRID", "VERIFY_IPC"))
THRIFT, MIXED, FRAMES, GZIP, BAD, CRC, produce = (
    DELTA[name] for name in ("THRIFT", "MIXED", "FRAMES", "GZIP", "BAD", "CRC", "produce"))
MIN, MAX = -(2**63), 2**63 - 1
PATTERN = [MIN, None, MAX, -1, 0, 0x0102030405060708, None, -0x0102030405060708]


def timestamp_groups():
    random_bits = random.Random(5270)
    random_words = [random_bits.getrandbits(64) + MIN for _ in range(500)]
    return [PATTERN * 64, [None] * 24, PATTERN + random_words]


def inspect(wire, field, groups, page_version, codec, checksum):
    parquet, footer = OPEN(wire), MIXED["metadata"](wire)
    _, _, leaf = THRIFT["list_field"](footer, 2)
    assert leaf[1] == (TType.I32, 2) and leaf[3] == (TType.I32, int(field.nullable))
    assert leaf[4] == (TType.STRING, b"ticks")
    timestamp = leaf[10][1][8][1]
    assert timestamp[1] == (TType.BOOL, field.type.tz == "UTC")
    assert timestamp[2][1] == {{"us": 2, "ns": 3}[field.type.unit]: (TType.STRUCT, {})}
    assert parquet.num_row_groups == len(groups) and parquet.schema_arrow.field(1).equals(field)
    captures, flags = [], set()
    for group, rows in enumerate(groups):
        metadata = THRIFT["column_metadata"](footer, group, 1)
        column = parquet.metadata.row_group(group).column(1)
        assert metadata[4][1] == {"NONE": 0, "SNAPPY": 1}[codec]
        assert metadata[1][1] == 2 and metadata[5][1] == len(rows)
        assert THRIFT["list_field"](metadata, 3) == [b"ticks"]
        assert set(THRIFT["list_field"](metadata, 2)) == {3, 9}
        assert 11 not in metadata and not column.has_dictionary_page
        start, stop = MIXED["column_extent"](metadata)
        assert start == metadata[9][1] == column.data_page_offset
        assert stop - start == metadata[7][1] == column.total_compressed_size
        pages = list(FRAMES(wire, start, stop))
        assert pages[0][0] == start and pages[-1][2] + len(pages[-1][3]) == stop
        cursor, group_flags = 0, []
        for _, header, _, stored in pages:
            assert header[3][1] == len(stored) and (4 in header) == checksum
            if checksum:
                assert zlib.crc32(stored) == header[4][1] % 2**32
            if page_version == "1.0":
                assert header[1][1] == 0
                info = header[5][1]
                count = info[1][1]
                assert [info[i][1] for i in (2, 3, 4)] == [9, 3, 3]
                expanded = (pa.Codec("snappy").decompress(stored, header[2][1]).to_pybytes()
                            if codec == "SNAPPY" else stored)
                assert len(expanded) == header[2][1]
                level_stop = 0
                if field.nullable:
                    level_stop = 4 + struct.unpack_from("<I", expanded)[0]
                definitions = expanded[4:level_stop] if field.nullable else b""
                values = expanded[level_stop:]
            else:
                assert header[1][1] == 3
                info = header[8][1]
                count, nulls, page_rows, tag, extent, repetitions = (info[i][1] for i in range(1, 7))
                assert page_rows == count and repetitions == 0 and tag == 9
                assert extent <= min(header[2][1], header[3][1])
                definitions, suffix = stored[:extent], stored[extent:]
                flag = info.get(7, (TType.BOOL, True))[1]
                group_flags.append((flag, len(suffix) > 0))
                expanded_size = header[2][1] - extent
                values = (pa.Codec("snappy").decompress(suffix, expanded_size).to_pybytes()
                          if codec == "SNAPPY" and flag else suffix)
                assert len(suffix) == header[3][1] - extent and len(values) == expanded_size
                assert rows[cursor:cursor + count].count(None) == nulls
            wanted = rows[cursor:cursor + count]
            cursor += count
            assert len(wanted) == count
            mask = [int(value is not None) for value in wanted]
            if field.nullable:
                assert HYBRID(definitions, 1, count) == mask
            else:
                assert not definitions and all(mask)
            count = sum(mask)
            assert len(values) == 8 * count
            signed = [int.from_bytes(values[index::count], "little", signed=True)
                      for index in range(count)]
            assert signed == [value for value in wanted if value is not None]
        assert cursor == len(rows) and READ(parquet, group) == rows
        flags.update(group_flags)
        captures.append(pages)
        print(f"{field.type} {codec} V{page_version[0]} group {group}: "
              f"offsets {[page[0] for page in pages]}, flags {group_flags}")
    return captures, flags


def shorten_final_page(wire, frame):
    """Remove one lane octet, updating only the final page and footer sizes."""
    start, header, payload, stored = frame
    footer = MIXED["metadata"](wire)
    footer_size, = struct.unpack_from("<I", wire, len(wire) - 8)
    assert payload + len(stored) == len(wire) - footer_size - 8
    edited = deepcopy(header)
    assert 4 not in header and header[8][1][5][1] == 0
    assert header[2][1] == header[3][1] == len(stored) and len(stored) % 8 == 0
    for key in (2, 3):
        edited[key] = (TType.I32, len(stored) - 1)
    encoded = THRIFT["encode"](edited)
    delta = len(encoded) - (payload - start) - 1
    group = THRIFT["list_field"](footer, 4)[2]
    column = THRIFT["column_metadata"](footer, 2, 1)
    for fields, keys in ((group, (2, 6)), (column, (6, 7))):
        for key in keys:
            if key in fields:
                kind, size = fields[key]
                assert kind == TType.I64
                fields[key] = kind, size + delta
    serialized = THRIFT["encode"](footer)
    return wire[:start] + encoded + stored[:-1] + serialized + struct.pack("<I", len(serialized)) + b"PAR1"


def fixtures():
    utc = pa.field("ticks", pa.timestamp("ns", "UTC"))
    local = pa.field("ticks", pa.timestamp("us"), nullable=False)
    groups = timestamp_groups()
    required = [[0 if value is None else value for value in group] for group in groups]
    wires, cases, captures = {}, {}, {}
    for kind, field, rows, checksum in (("utc", utc, groups, True), ("local", local, required, False)):
        for page_version in ("1.0", "2.0"):
            for codec in ("NONE", "SNAPPY"):
                name = f"native_{kind}_v{page_version[0]}_{codec.lower()}"
                wire = produce(field, rows, page_version, codec, checksum=checksum, encoding="BYTE_STREAM_SPLIT")
                wires[name], cases[name] = wire, (field, rows)
                captures[name], flags = inspect(wire, field, rows, page_version, codec, checksum)
                if page_version == "2.0" and codec == "SNAPPY" and kind == "utc":
                    assert flags >= {(True, True), (False, True)}

    v1 = "native_utc_v1_snappy"
    v2 = "native_utc_v2_snappy"
    late_v1 = captures[v1][2][0]
    late_v2 = captures[v2][2][0]
    wires["mutated_v1_crc"], v1_crc = CRC(wires[v1], late_v1)
    wires["mutated_v2_crc"], v2_crc = CRC(wires[v2], captures[v2][2][1])
    for name in ("mutated_v1_crc", "mutated_v2_crc"):
        BAD(wires[name], groups, 2, "CRC")
    wires["mutated_v1_level_encoding"] = GZIP["rewrite_header"](wires[v1], late_v1, lambda header:
        header[5][1].update({3: (TType.I32, 4)}))
    wires["mutated_v1_tag"] = GZIP["rewrite_header"](wires[v1], late_v1, lambda header:
        header[5][1].update({2: (TType.I32, 0)}))
    wires["mutated_v2_tag"] = GZIP["retag"](wires[v2], late_v2, 0)

    raw = wires["native_local_v2_none"]
    last = captures["native_local_v2_none"][2][-1]
    wires["mutated_short_lane"] = shorten_final_page(raw, last)
    BAD(wires["mutated_short_lane"], required, 2, "not aligned with type INT64")

    wires["native_plain_control"] = produce(utc, groups, "2.0", "NONE", checksum=True, encoding="PLAIN")
    wires["native_gzip_control"] = produce(utc, groups, "2.0", "GZIP", checksum=True, encoding="BYTE_STREAM_SPLIT")
    assert THRIFT["column_metadata"](MIXED["metadata"](wires["native_gzip_control"]), 0, 1)[4][1] == 2
    first = captures["native_utc_v2_none"][0][0]
    return wires, cases, [*v1_crc, *v2_crc, late_v1[0], late_v2[0], last[0],
                          len(captures["native_local_v2_none"][2]) - 1, first[0], first[1][3][1], first[1][2][1]]


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    wires, cases, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in wires.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-byte-stream-split-") as temporary:
        output = Path(temporary)
        for name, wire in wires.items():
            (output / f"{name}.parquet").write_bytes(wire)
        for name, (_, rows) in cases.items():
            lines = [",".join("null" if value is None else str(value) for value in group) for group in rows]
            (output / f"{name}.txt").write_text("\n".join(lines))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in output.glob("*.arrows")} == set(cases)
        for name, (field, rows) in cases.items():
            VERIFY_IPC((output / f"{name}.arrows").read_bytes(), field, rows)


if __name__ == "__main__":
    main()
