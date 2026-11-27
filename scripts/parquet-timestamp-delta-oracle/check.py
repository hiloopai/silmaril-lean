"""Check selected TIMESTAMP DELTA_BINARY_PACKED against the pinned PyArrow producer."""

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

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ORACLE = runpy.run_path(str(HERE.parent / "parquet-timestamp-uncompressed-v2-oracle/check.py"))
OPEN, READ, ASSEMBLE, HYBRID, VERIFY_IPC = (
    ORACLE[name] for name in ("OPEN", "READ", "ASSEMBLE", "HYBRID", "VERIFY_IPC"))
THRIFT, MIXED, FRAMES, GZIP, BAD = (ORACLE[name] for name in ("THRIFT", "MIXED", "FRAMES", "GZIP", "BAD"))
CRC = ORACLE["DICT"]["CRC"]
MIN, MAX = -(2**63), 2**63 - 1
ROWS = [[MIN, None, MAX, -1, 0, None, MIN] + [i * 1000 for i in range(500)],
        [None] * 24,
        [MAX, None, -1, 0, 1, MIN] + [-i * 1000 for i in range(500)]]


def produce(field, groups, page_version, codec, *, checksum, encoding="DELTA_BINARY_PACKED"):
    schema = pa.schema([pa.field("decoy", pa.int32(), nullable=False), field])
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=page_version,
                          use_dictionary=False, compression={"ticks": codec}, column_encoding={"ticks": encoding},
                          write_page_checksum=checksum, store_schema=False, write_statistics=False,
                          write_batch_size=128, data_page_size=128) as writer:
        for group in groups:
            writer.write_table(pa.Table.from_arrays([pa.array(range(len(group)), type=pa.int32()),
                pa.array(group, type=pa.int64()).view(field.type)], schema=schema))
    return sink.getvalue().to_pybytes()


def decode_delta(raw, expected):
    """Independent pinned-spec parser for the producer's signed INT64 stream."""
    cursor = 0

    def take(size):
        nonlocal cursor
        result = raw[cursor:cursor + size]
        assert len(result) == size
        cursor += size
        return result

    def uleb(bits):
        value = 0
        for shift in range(0, bits, 7):
            byte = take(1)[0]
            value |= (byte & 127) << shift
            if byte < 128:
                assert value < 2**bits
                return value
        raise AssertionError("overlong varint")

    def zigzag(value):
        return (value >> 1) ^ -(value & 1)

    block_size, miniblocks, count = (uleb(31) for _ in range(3))
    first = zigzag(uleb(64))
    assert count == expected
    assert block_size and block_size % 128 == block_size % miniblocks == 0
    width_count = block_size // miniblocks
    assert width_count >= 32 and width_count % 32 == 0
    words, wraps = [first] if count else [], set()
    while len(words) < count:
        left = min(block_size, count - len(words))
        minimum, widths = zigzag(uleb(64)), take(miniblocks)
        for width in widths:
            if not left:
                break
            assert width <= 64
            bits = int.from_bytes(take(width_count * width // 8), "little")
            active = min(left, width_count)
            for i in range(active):
                difference = minimum + ((bits >> (i * width)) & ((1 << width) - 1))
                value = words[-1] + difference
                if value < MIN:
                    wraps.add("below")
                if value > MAX:
                    wraps.add("above")
                words.append((value - MIN) % (2**64) + MIN)
            left -= active
        assert not left
    assert cursor == len(raw)
    return words, wraps


def inspect(wire, field, groups, page_version, codec, checksum):
    parquet, footer = OPEN(wire), MIXED["metadata"](wire)
    _, _, leaf = THRIFT["list_field"](footer, 2)
    assert leaf[1] == (TType.I32, 2) and leaf[3] == (TType.I32, int(field.nullable))
    assert leaf[4] == (TType.STRING, b"ticks")
    timestamp = leaf[10][1][8][1]
    assert timestamp[1] == (TType.BOOL, field.type.tz == "UTC")
    assert timestamp[2][1] == {{"us": 2, "ns": 3}[field.type.unit]: (TType.STRUCT, {})}
    assert parquet.num_row_groups == len(groups) and parquet.schema_arrow.field(1).equals(field)
    captures, flags, wraps = [], set(), set()
    for group, rows in enumerate(groups):
        metadata = THRIFT["column_metadata"](footer, group, 1)
        column = parquet.metadata.row_group(group).column(1)
        assert metadata[4][1] == {"NONE": 0, "SNAPPY": 1}[codec]
        assert metadata[1][1] == 2 and metadata[5][1] == len(rows)
        assert THRIFT["list_field"](metadata, 3) == [b"ticks"]
        assert set(THRIFT["list_field"](metadata, 2)) == {3, 5}
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
                assert [info[i][1] for i in (2, 3, 4)] == [5, 3, 3]
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
                assert page_rows == count and repetitions == 0 and tag == 5
                assert extent <= min(header[2][1], header[3][1])
                definitions, suffix = stored[:extent], stored[extent:]
                flag = info.get(7, (TType.BOOL, True))[1]
                group_flags.append(flag)
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
            signed, directions = decode_delta(values, sum(mask))
            wraps.update(directions)
            assert signed == [value for value in wanted if value is not None]
        assert cursor == len(rows) and READ(parquet, group) == rows
        flags.update(group_flags)
        captures.append(pages)
        print(f"{field.type} {codec} V{page_version[0]} group {group}: "
              f"offsets {[page[0] for page in pages]}, flags {group_flags}")
    assert wraps == {"above", "below"}
    return captures, flags


def fixtures():
    utc = pa.field("ticks", pa.timestamp("ns", "UTC"))
    local = pa.field("ticks", pa.timestamp("us"), nullable=False)
    required = [[0 if value is None else value for value in group] for group in ROWS]
    wires, cases, captures = {}, {}, {}
    for kind, field, groups, checksum in (("utc", utc, ROWS, True), ("local", local, required, False)):
        for page_version in ("1.0", "2.0"):
            for codec in ("NONE", "SNAPPY"):
                name = f"native_{kind}_v{page_version[0]}_{codec.lower()}"
                wire = produce(field, groups, page_version, codec, checksum=checksum)
                wires[name], cases[name] = wire, (field, groups)
                captures[name], flags = inspect(wire, field, groups, page_version, codec, checksum)
                if page_version == "2.0" and codec == "SNAPPY" and kind == "utc":
                    assert flags == {True, False}

    v1 = "native_utc_v1_snappy"
    v2 = "native_utc_v2_snappy"
    late_v1 = captures[v1][2][0]
    late_v2 = captures[v2][2][0]
    wires["mutated_v1_crc"], v1_crc = CRC(wires[v1], late_v1)
    wires["mutated_v2_crc"], v2_crc = CRC(wires[v2], captures[v2][2][1])
    for name in ("mutated_v1_crc", "mutated_v2_crc"):
        BAD(wires[name], ROWS, 2, "CRC")
    wires["mutated_v1_level_encoding"] = GZIP["rewrite_header"](wires[v1], late_v1, lambda header:
        header[5][1].update({3: (TType.I32, 4)}))
    wires["mutated_v1_tag"] = GZIP["rewrite_header"](wires[v1], late_v1, lambda header:
        header[5][1].update({2: (TType.I32, 0)}))
    wires["mutated_v2_tag"] = GZIP["retag"](wires[v2], late_v2, 0)

    raw = "native_local_v2_none"
    broken = captures[raw][2][0]
    assert 4 not in broken[1] and broken[1][8][1][5][1] == 0
    assert broken[3][0] == 0x80  # The valid block size is a multiple of 128.
    at = broken[2]
    # Change only the block size's low bit, retaining the varint width.
    wires["mutated_delta_geometry"] = wires[raw][:at] + b"\x81" + wires[raw][at + 1:]
    assert [READ(OPEN(wires["mutated_delta_geometry"]), i) for i in range(2)] == required[:2]

    selection = [("native_utc_v1_none", 0), (v2, 1), (v1, 2), ("native_utc_v2_none", 0)]
    wire = ASSEMBLE([(wires[name], i) for name, i in selection])
    rows = [ROWS[i] for _, i in selection]
    wires["assembled_versions_codecs"], cases["assembled_versions_codecs"] = wire, (utc, rows)
    assert [READ(OPEN(wire), i) for i in range(len(rows))] == rows
    assembled = MIXED["metadata"](wire)
    for index, (name, source_group) in enumerate(selection):
        start, stop = MIXED["column_extent"](THRIFT["column_metadata"](assembled, index, 1))
        source_start, source_stop = MIXED["column_extent"](THRIFT["column_metadata"](
            MIXED["metadata"](wires[name]), source_group, 1))
        assert wire[start:stop] == wires[name][source_start:source_stop]

    wires["native_plain_control"] = produce(utc, ROWS, "2.0", "NONE", checksum=True, encoding="PLAIN")
    wires["native_gzip_control"] = produce(utc, ROWS, "2.0", "GZIP", checksum=True)
    assert THRIFT["column_metadata"](MIXED["metadata"](wires["native_gzip_control"]), 0, 1)[4][1] == 2
    first = captures["native_utc_v2_none"][0][0]
    return wires, cases, [*v1_crc, *v2_crc, late_v1[0], late_v2[0], broken[0],
                          first[0], first[1][3][1], first[1][2][1]]


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    wires, cases, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in wires.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-delta-") as temporary:
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
