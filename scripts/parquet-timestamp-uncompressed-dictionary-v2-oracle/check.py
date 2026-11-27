"""Verify strict codec-0 TIMESTAMP V2 dictionaries against PyArrow and Thrift."""

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
from thrift.Thrift import TType

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PLAIN = runpy.run_path(str(HERE.parent / "parquet-timestamp-uncompressed-v2-oracle/check.py"))
THRIFT, MIXED, GZIP = (PLAIN[name] for name in ("THRIFT", "MIXED", "GZIP"))
OPEN, READ, HYBRID, VERIFY_IPC = (PLAIN[name] for name in ("OPEN", "READ", "HYBRID", "VERIFY_IPC"))
FRAMES, ASSEMBLE = (PLAIN[name] for name in ("FRAMES", "ASSEMBLE"))
PRODUCE, CRC, BAD = PLAIN["produce"], PLAIN["DICT"]["CRC"], PLAIN["BAD"]
RAW_FRAMES = PLAIN["DICT"]["SNAPPY"]["raw_frames"]
PRODUCE_FALLBACK = PLAIN["DICT"]["GZIP"]["produce"]


def check_stored(frame, checksum):
    _, header, _, body = frame
    assert header[2][1] == header[3][1] == len(body)
    assert (4 in header) == checksum
    if checksum:
        assert header[4][1] % 2**32 == zlib.crc32(body)


def inspect(wire, field, groups, checksum, changed_flag=None):
    parquet = OPEN(wire)
    footer = MIXED["metadata"](wire)
    _, _, leaf = THRIFT["list_field"](footer, 2)
    assert leaf[1] == (TType.I32, 2) and leaf[3] == (TType.I32, int(field.nullable))
    assert leaf[4] == (TType.STRING, b"ticks")
    annotation = leaf[10][1][8][1]
    assert annotation[1] == (TType.BOOL, field.type.tz == "UTC")
    unit = {"us": 2, "ns": 3}[field.type.unit]
    assert annotation[2][1] == {unit: (TType.STRUCT, {})}
    assert parquet.schema_arrow.field(1).equals(field) and parquet.num_row_groups == len(groups)

    captures, dictionaries = [], []
    for group, rows in enumerate(groups):
        metadata = THRIFT["column_metadata"](footer, group, 1)
        column = parquet.metadata.row_group(group).column(1)
        assert column.compression == "UNCOMPRESSED" and column.has_dictionary_page
        assert metadata[1][1] == 2 and metadata[4][1] == 0 and metadata[5][1] == len(rows)
        assert THRIFT["list_field"](metadata, 3) == [b"ticks"]
        assert set(THRIFT["list_field"](metadata, 2)) == {0, 3, 8}
        start, stop = MIXED["column_extent"](metadata)
        assert stop - start == column.total_compressed_size == metadata[6][1]
        dictionary, *pages = FRAMES(wire, start, stop)
        assert start == dictionary[0] == metadata[11][1] == column.dictionary_page_offset
        assert pages[0][0] == metadata[9][1] == column.data_page_offset
        check_stored(dictionary, checksum)
        _, header, _, body = dictionary
        assert header[1][1] == 2 and header[7][1][2][1] == 0
        assert header[7][1][1][1] * 8 == len(body)
        words = [value for value, in struct.iter_unpack("<q", body)]
        assert words == list(dict.fromkeys(value for value in rows if value is not None))
        dictionaries.append(tuple(words))

        cursor = 0
        for ordinal, page in enumerate(pages, start=1):
            check_stored(page, checksum)
            _, header, _, body = page
            assert header[1][1] == 3
            info = header[8][1]
            count, nulls, page_rows, encoding, level_bytes, repetition = (info[i][1] for i in range(1, 7))
            slots = rows[cursor:cursor + count]
            cursor += count
            assert len(slots) == count == page_rows and slots.count(None) == nulls
            assert repetition == 0 and encoding == 8 and level_bytes <= len(body)
            flag = info[7][1] if 7 in info else None
            expected = changed_flag[2] if changed_flag is not None and (group, ordinal) == changed_flag[:2] else False
            assert flag is expected
            raw_levels, suffix = body[:level_bytes], body[level_bytes:]
            mask = [int(value is not None) for value in slots]
            if field.nullable:
                assert HYBRID(raw_levels, 1, count) == mask
            else:
                assert raw_levels == b"" and all(mask)
            assert len(suffix) == header[2][1] - level_bytes == header[3][1] - level_bytes
            indices = HYBRID(suffix[1:], suffix[0], sum(mask))
            assert [words[index] for index in indices] == [value for value in slots if value is not None]
        assert cursor == len(rows) and READ(parquet, group) == rows
        captures.append((dictionary, pages))
        print(f"{field.type} group {group}: dictionary {start}, V2 references {[p[0] for p in pages]}")
    assert len(set(dictionaries)) == len(groups)
    return captures


def fixtures():
    utc = pa.field("ticks", pa.timestamp("ns", "UTC"))
    local = pa.field("ticks", pa.timestamp("us"), nullable=False)
    rows = PLAIN["DICT"]["GROUPS"]
    required = [[row[0] if value is None else value for value in row] for row in rows]
    cases = {"native_utc": (utc, rows, True), "native_local": (local, required, False)}
    wires = {name: PRODUCE(field, groups, checksum=checksum, dictionary=True)
             for name, (field, groups, checksum) in cases.items()}
    captures = {name: inspect(wires[name], *case) for name, case in cases.items()}
    assert all(sum(len(pages) for _, pages in groups) == 25 for groups in captures.values())
    good, literal = wires["native_utc"], wires["native_local"]
    dictionary, late = captures["native_utc"][2]
    assert len(late) > 1
    wires["mutated_true_flag"] = GZIP["rewrite_header"](good, late[-1], lambda header:
        header[8][1].update({7: (TType.BOOL, True)}))
    wires["mutated_absent_flag"] = PLAIN["remove_last_flag"](good, late[-1], 2)
    for name, flag in (("mutated_true_flag", True), ("mutated_absent_flag", None)):
        cases[name] = cases["native_utc"]
        _, pages = inspect(wires[name], *cases[name], (2, len(late), flag))[-1]
        assert pages[-1][3] == late[-1][3] and pages[-1][1][4] == late[-1][1][4]

    wires["mutated_dictionary_crc"], dict_crc = CRC(good, dictionary)
    wires["mutated_levels_crc"], levels_crc = CRC(good, late[-1])
    for name in ("mutated_dictionary_crc", "mutated_levels_crc"):
        BAD(wires[name], rows, 2, "CRC")

    # A packed literal reference into the third group's three-entry dictionary.
    _, local_pages = captures["native_local"][2]
    ref_offset, ref_header, ref_start, suffix = local_pages[-1]
    assert ref_header[8][1][5][1] == 0 and suffix[:2] == b"\x02\x03"
    modified = suffix[2] | 3
    assert HYBRID(bytes([3, modified]) + suffix[3:], 2, ref_header[8][1][1][1])[0] == 3
    wires["mutated_reference"] = literal[:ref_start + 2] + bytes([modified]) + literal[ref_start + 3:]
    BAD(wires["mutated_reference"], required, 2)

    def unequal_true(header):
        header[2] = TType.I32, header[2][1] + 1
        header[8][1][7] = TType.BOOL, True

    wires["mutated_true_size"] = GZIP["rewrite_header"](good, late[-1], unequal_true)
    wires["mutated_false_size"] = GZIP["rewrite_header"](good, late[-1], lambda header:
        header.update({2: (TType.I32, header[2][1] + 1)}))
    for name in ("mutated_true_size", "mutated_false_size"):
        assert [READ(OPEN(wires[name]), index) for index in range(2)] == rows[:2]

    wires["native_v1"] = PRODUCE(local, required[2:], checksum=False, dictionary=True, pages="1.0")
    wires["assembled_late_v1"] = ASSEMBLE([(literal, 0), (literal, 1), (wires["native_v1"], 0)])
    parquet = OPEN(wires["assembled_late_v1"])
    assert [READ(parquet, i) for i in range(3)] == required
    _, v1, *_ = RAW_FRAMES(
        wires["assembled_late_v1"], parquet.metadata.row_group(2).column(1))
    assert v1[1][1][1] == 0 and v1[1][5][1][2][1] == 8

    fallback_rows = [rows[1], [None if i % 5 == 0 else i - 80 for i in range(160)]]
    wires["native_fallback"] = PRODUCE_FALLBACK(
        utc, fallback_rows, codec="NONE", page_version="2.0", fallback=True, checksum=False)
    parquet = OPEN(wires["native_fallback"])
    assert [READ(parquet, i) for i in range(2)] == fallback_rows
    _, *first = RAW_FRAMES(
        wires["native_fallback"], parquet.metadata.row_group(0).column(1))
    _, *second = RAW_FRAMES(
        wires["native_fallback"], parquet.metadata.row_group(1).column(1))
    assert all(frame[1][1][1] == 3 for frame in first + second)
    tags = [frame[1][8][1][4][1] for frame in second]
    assert [frame[1][8][1][4][1] for frame in first] == [8]
    assert tags == sorted(tags, reverse=True) and set(tags) == {8, 0}
    plain_index = tags.index(0)
    print(f"Native fallback group 1: V2 data encodings {tags}, first PLAIN offset {second[plain_index][0]}")

    wires["native_plain"] = PRODUCE(utc, rows, checksum=False)
    wires["native_snappy"] = PRODUCE(utc, rows, checksum=False, dictionary=True, codec="SNAPPY")
    first_dict, first_pages = captures["native_utc"][0]
    evidence = [*dict_crc, *levels_crc, len(late), ref_offset, len(local_pages), v1[0],
                plain_index + 1, second[plain_index][0], first_dict[0], first_pages[0][0]]
    return wires, cases, fallback_rows, evidence


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    wires, cases, fallback_rows, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in wires.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-uncompressed-dictionary-v2-") as temporary:
        output = Path(temporary)
        for name, wire in wires.items():
            (output / f"{name}.parquet").write_bytes(wire)
        counts = {name: rows for name, (_, rows, _) in cases.items()} | {"fallback": fallback_rows}
        for name, rows in counts.items():
            lines = [",".join("null" if value is None else str(value) for value in group) for group in rows]
            (output / f"{name}.txt").write_text("\n".join(lines))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in output.glob("*.arrows")} == set(cases)
        outputs = {}
        for name, (field, rows, _) in cases.items():
            stream = (output / f"{name}.arrows").read_bytes()
            VERIFY_IPC(stream, field, rows)
            outputs[name] = stream
        assert outputs["native_utc"] == outputs["mutated_true_flag"] == outputs["mutated_absent_flag"]


if __name__ == "__main__":
    main()
