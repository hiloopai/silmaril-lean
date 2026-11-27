"""Check strict Snappy V2 dictionary-only TIMESTAMP against PyArrow and Thrift."""

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
SNAPPY = runpy.run_path(str(HERE.parent / "parquet-timestamp-snappy-dictionary-oracle/check.py"))
ASSEMBLY = runpy.run_path(str(HERE.parent / "parquet-timestamp-gzip-dispatch-v2-oracle/check.py"))
THRIFT, MIXED, GZIP = (ASSEMBLY[name] for name in ("THRIFT", "MIXED", "GZIP"))
READ_GROUP, VERIFY_IPC, CRC = (GZIP[name] for name in ("read_group", "verify_ipc", "corrupt_frame_crc"))
GROUPS = SNAPPY["GROUPS"]


def produce(field, groups, *, checksum, pages="2.0", codec="SNAPPY", dictionary=True):
    schema = pa.schema([pa.field("decoy", pa.int32(), nullable=False), field])
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=pages,
                          compression={"ticks": codec}, use_dictionary=["ticks"] if dictionary else False,
                          write_statistics=False, store_schema=False, write_page_checksum=checksum) as writer:
        for rows in groups:
            ticks = pa.array(rows, type=pa.int64()).view(field.type)
            decoy = pa.array(range(len(rows)), type=pa.int32())
            writer.write_table(pa.Table.from_arrays([decoy, ticks], schema=schema))
    return sink.getvalue().to_pybytes()


def open_checked(wire):
    return pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)


def inspect(wire, field, groups, checksum):
    parquet = open_checked(wire)
    footer = MIXED["metadata"](wire)
    _, _, leaf = THRIFT["list_field"](footer, 2)
    annotation = leaf[10][1][8][1]
    assert leaf[1] == (TType.I32, 2) and leaf[3] == (TType.I32, int(field.nullable))
    assert leaf[4] == (TType.STRING, b"ticks") and annotation[1] == (TType.BOOL, field.type.tz == "UTC")
    unit = {"us": 2, "ns": 3}[field.type.unit]
    assert annotation[2][1] == {unit: (TType.STRUCT, {})}
    assert parquet.schema_arrow.field(1).equals(field) and parquet.num_row_groups == len(groups)
    codec = pa.Codec("snappy")
    captures, flags = [], set()
    for index, rows in enumerate(groups):
        metadata = THRIFT["column_metadata"](footer, index, 1)
        assert THRIFT["column_metadata"](footer, index, 0)[4][1] == 0
        assert metadata[1][1] == 2 and metadata[4][1] == 1 and metadata[5][1] == len(rows)
        column = parquet.metadata.row_group(index).column(1)
        assert column.encodings == ("PLAIN", "RLE", "RLE_DICTIONARY")
        start, stop = MIXED["column_extent"](metadata)
        dictionary, data = list(ASSEMBLY["frames"](wire, start, stop))
        assert start == dictionary[0] == column.dictionary_page_offset == metadata[11][1]
        assert data[0] == column.data_page_offset == metadata[9][1]
        for _, header, _, body in (dictionary, data):
            assert (4 in header) == checksum
            if checksum:
                assert header[4][1] % 2**32 == zlib.crc32(body)
        _, header, _, body = dictionary
        assert header[1][1] == 2 and header[7][1][2][1] == 0
        assert header[2][1] == 8 * header[7][1][1][1]
        words = [value for value, in struct.iter_unpack("<q", codec.decompress(body, header[2][1]).to_pybytes())]
        present = [slot for slot in rows if slot is not None]
        assert words == list(dict.fromkeys(present))
        _, header, body_start, body = data
        assert header[1][1] == 3
        info = header[8][1]
        assert [info[i][1] for i in (1, 2, 3, 4, 6)] == [len(rows), rows.count(None), len(rows), 8, 0]
        definitions, compressed = info[5][1], info[7][1]
        assert definitions <= min(header[2][1], header[3][1])
        raw_levels, stored = body[:definitions], body[definitions:]
        if field.nullable:
            assert SNAPPY["hybrid"](raw_levels, 1, len(rows)) == [int(slot is not None) for slot in rows]
        else:
            assert definitions == 0 and all(slot is not None for slot in rows)
        expected = header[2][1] - definitions
        expanded = codec.decompress(stored, expected).to_pybytes() if compressed else stored
        assert len(expanded) == expected
        assert [words[i] for i in SNAPPY["hybrid"](expanded[1:], expanded[0], len(present))] == present
        assert READ_GROUP(parquet, index) == rows
        print(f"{field.type} group {index}: dictionary {dictionary[0]}, V2 data {data[0]}, "
              f"{definitions} raw definition bytes, compressed suffix {compressed}")
        flags.add(compressed)
        captures.append((dictionary, data, body_start + definitions))
    assert flags == {True, False}
    return captures


def assert_bad(wire, groups, index, reason=None):
    parquet = open_checked(wire)
    assert [READ_GROUP(parquet, before) for before in range(index)] == groups[:index]
    try:
        READ_GROUP(parquet, index)
    except (pa.ArrowException, OSError) as error:
        if reason is not None:
            assert reason.lower() in str(error).lower(), str(error)
    else:
        raise AssertionError("PyArrow accepted the damaged selected frame")


def fixtures():
    utc = pa.field("ticks", pa.timestamp("ns", "UTC"))
    local = pa.field("ticks", pa.timestamp("us"), nullable=False)
    required = [[0 if slot is None else slot for slot in group] for group in GROUPS]
    cases = {"utc_nanos": (utc, GROUPS), "local_micros": (local, required)}
    wires = {"utc_nanos": produce(utc, GROUPS, checksum=True),
             "local_micros": produce(local, required, checksum=False)}
    optional_frames = inspect(wires["utc_nanos"], utc, GROUPS, True)
    required_frames = inspect(wires["local_micros"], local, required, False)
    dictionary, data, _ = optional_frames[2]
    wires["bad_dictionary"], dict_crc = CRC(wires["utc_nanos"], dictionary)
    wires["bad_levels"], level_crc = CRC(wires["utc_nanos"], data)
    assert_bad(wires["bad_dictionary"], GROUPS, 2, "CRC")
    assert_bad(wires["bad_levels"], GROUPS, 2, "CRC")
    _, data, suffix = required_frames[2]
    assert data[1][8][1][7][1]
    original = wires["local_micros"]
    wires["bad_suffix"] = original[:suffix] + bytes([original[suffix] ^ 1]) + original[suffix + 1:]
    assert_bad(wires["bad_suffix"], required, 2)

    v1 = produce(utc, GROUPS[2:], checksum=True, pages="1.0")
    assembled = ASSEMBLY["assemble"]([(wires["utc_nanos"], 0), (wires["utc_nanos"], 1), (v1, 0)])
    wires["late_v1_assembly"] = assembled
    parquet = open_checked(assembled)
    assert [READ_GROUP(parquet, group) for group in range(3)] == GROUPS
    _, v1_page = list(SNAPPY["raw_frames"](assembled, parquet.metadata.row_group(2).column(1)))
    assert v1_page[1][1][1] == 0 and v1_page[1][5][1][2][1] == 8

    fallback_rows = [GROUPS[1], list(range(160))]
    # One dictionary-only group fits in a single write batch. The next genuinely falls back.
    fallback = GZIP["produce"](utc, fallback_rows, codec="SNAPPY", page_version="2.0", fallback=True)
    files = open_checked(fallback)
    assert [READ_GROUP(files, group) for group in range(2)] == fallback_rows
    first, second = [list(SNAPPY["raw_frames"](fallback, files.metadata.row_group(group).column(1)))[1:]
                     for group in range(2)]
    assert [frame[1][8][1][4][1] for frame in first] == [8]
    tags = [frame[1][8][1][4][1] for frame in second]
    assert tags == sorted(tags, reverse=True) and set(tags) == {8, 0}
    plain = tags.index(0)
    wires["late_fallback"] = fallback
    wires["plain_v2"] = produce(utc, GROUPS, checksum=True, dictionary=False)
    wires["uncompressed_v2"] = produce(utc, GROUPS, checksum=False, codec="NONE")
    cases["late_fallback_prefix"] = utc, fallback_rows[:1]
    evidence = [*dict_crc, *level_crc, data[0], v1_page[0], plain + 1, second[plain][0],
                optional_frames[0][0][0], optional_frames[0][1][0]]
    return wires, cases, evidence


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    wires, cases, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in wires.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-snappy-dictionary-v2-") as temporary:
        output = Path(temporary)
        for name, wire in wires.items():
            (output / f"{name}.parquet").write_bytes(wire)
        for name, (_, rows) in cases.items():
            lines = [",".join("null" if value is None else str(value) for value in group) for group in rows]
            (output / f"{name}.txt").write_text("\n".join(lines))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in output.glob("*.arrows")} == {"utc_nanos", "local_micros"}
        for name in ("utc_nanos", "local_micros"):
            field, rows = cases[name]
            VERIFY_IPC((output / f"{name}.arrows").read_bytes(), field, rows)


if __name__ == "__main__":
    main()
