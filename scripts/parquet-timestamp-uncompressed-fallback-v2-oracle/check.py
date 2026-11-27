"""Check strict codec-0 V2 TIMESTAMP fallback with genuine PyArrow files."""

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

import pyarrow as pa
from thrift.Thrift import TType

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE = runpy.run_path(str(HERE.parent / "parquet-timestamp-snappy-fallback-v2-oracle/check.py"))
LITERAL = runpy.run_path(str(HERE.parent / "parquet-timestamp-uncompressed-dictionary-v2-oracle/check.py"))
PLAIN = LITERAL["PLAIN"]
THRIFT, MIXED, ASSEMBLE, SPLICE = (BASE[name] for name in ("THRIFT", "MIXED", "ASSEMBLE", "SPLICE"))
CRC, READ_GROUP, VERIFY_IPC = (BASE[name] for name in ("CRC", "READ_GROUP", "VERIFY_IPC"))
OPEN, BAD, HYBRID = (BASE[name] for name in ("OPEN", "BAD", "HYBRID"))
BATCH, MIN, MAX = (BASE[name] for name in ("BATCH", "MIN", "MAX"))
RAW_FRAMES, CHECK_STORED = (LITERAL[name] for name in ("RAW_FRAMES", "check_stored"))


def produce(field, groups, *, checksum, pages="2.0"):
    return BASE["produce"](field, groups, checksum=checksum, pages=pages, codec="NONE")


def inspect(wire, field, groups, checksum, changed_flag=None):
    parquet = OPEN(wire)
    footer = MIXED["metadata"](wire)
    _, _, leaf = THRIFT["list_field"](footer, 2)
    annotation = leaf[10][1][8][1]
    assert leaf[1] == (TType.I32, 2) and leaf[3] == (TType.I32, int(field.nullable))
    assert leaf[4] == (TType.STRING, b"ticks") and annotation[1] == (TType.BOOL, field.type.tz == "UTC")
    unit = {"us": 2, "ns": 3}[field.type.unit]
    assert annotation[2][1] == {unit: (TType.STRUCT, {})}
    assert parquet.schema_arrow.field(1).equals(field) and parquet.num_row_groups == len(groups)
    captured = []
    for index, expected in enumerate(groups):
        metadata = THRIFT["column_metadata"](footer, index, 1)
        assert THRIFT["column_metadata"](footer, index, 0)[4][1] == 0
        assert metadata[1][1] == 2 and metadata[4][1] == 0 and metadata[5][1] == len(expected)
        assert THRIFT["list_field"](metadata, 3) == [b"ticks"]
        column = parquet.metadata.row_group(index).column(1)
        assert column.encodings == ("PLAIN", "RLE", "RLE_DICTIONARY")
        start, stop = MIXED["column_extent"](metadata)
        dictionary, *pages = PLAIN["FRAMES"](wire, start, stop)
        assert start == dictionary[0] == metadata[11][1] == column.dictionary_page_offset
        assert stop - start == column.total_compressed_size == metadata[6][1]
        assert pages[0][0] == metadata[9][1] == column.data_page_offset
        for frame in (dictionary, *pages):
            CHECK_STORED(frame, checksum)
        _, header, _, stored = dictionary
        assert header[1][1] == 2 and header[7][1][2][1] == 0
        assert header[2][1] == 8 * header[7][1][1][1]
        entries = [word for word, in struct.iter_unpack("<q", stored)]
        cursor, tags, flags, referenced = 0, [], [], []
        for ordinal, (_, header, _, stored) in enumerate(pages, start=1):
            assert header[1][1] == 3
            info = header[8][1]
            count, nulls, rows, tag, size, repetition = (info[i][1] for i in range(1, 7))
            flag = info[7][1] if 7 in info else None
            expected_flag = changed_flag[2] if changed_flag is not None and (index, ordinal) == changed_flag[:2] else False
            assert flag is expected_flag
            slots = expected[cursor:cursor + count]
            cursor += count
            assert rows == count == len(slots) == BATCH and slots.count(None) == nulls
            assert repetition == 0 and size <= min(header[2][1], header[3][1])
            levels, suffix = stored[:size], stored[size:]
            if field.nullable:
                assert HYBRID(levels, 1, count) == [int(slot is not None) for slot in slots]
            else:
                assert size == 0 and all(slot is not None for slot in slots)
            assert len(suffix) == header[2][1] - size == header[3][1] - size
            present = [slot for slot in slots if slot is not None]
            if tag == 8:
                assert [entries[i] for i in HYBRID(suffix[1:], suffix[0], len(present))] == present
                referenced.extend(present)
            else:
                assert tag == 0 and [word for word, in struct.iter_unpack("<q", suffix)] == present
            tags.append(tag)
            flags.append(flag)
        assert tags == [8, 0, 0] and cursor == len(expected)
        assert entries == list(dict.fromkeys(referenced))
        assert READ_GROUP(parquet, index) == expected
        print(f"{field.type} group {index}: original dictionary at {dictionary[0]}, tags {tags}, flags {flags}")
        captured.append((dictionary, pages))
    return captured


def fixtures():
    first, last = BASE["PRIOR"]["groups"]()
    sparse = [None] * BATCH
    sparse[2], sparse[-1] = MIN, MAX
    rows = [first, sparse + first[-BATCH:] + first[BATCH:2 * BATCH], last]
    noise_pages = [2, 1, 1]
    noise = random.Random(78199)
    required = []
    for group, noise_page in zip(rows, noise_pages, strict=True):
        required.append([value if value is not None else
                         (noise.randrange(MIN, MAX + 1) if slot // BATCH == noise_page else 0)
                         for slot, value in enumerate(group)])
    utc = pa.field("ticks", pa.timestamp("ns", "UTC"))
    local = pa.field("ticks", pa.timestamp("us"), nullable=False)
    cases = {"utc_nanos": (utc, rows), "local_micros": (local, required)}
    files = {"utc_nanos": produce(utc, rows, checksum=True),
             "local_micros": produce(local, required, checksum=False)}
    optional = inspect(files["utc_nanos"], utc, rows, True)
    mandatory = inspect(files["local_micros"], local, required, False)
    good = files["utc_nanos"]
    dictionary, (reference, plain, last_plain) = optional[1]
    files["mutated_true_reference_flag"] = SPLICE["rewrite_header"](good, reference, lambda header:
        header[8][1].update({7: (TType.BOOL, True)}))
    files["mutated_absent_plain_flag"] = PLAIN["remove_last_flag"](good, optional[2][1][-1], 2)
    for name, group, ordinal, flag in (("mutated_true_reference_flag", 1, 1, True),
                                       ("mutated_absent_plain_flag", 2, 3, None)):
        cases[name] = cases["utc_nanos"]
        _, pages = inspect(files[name], utc, rows, True, (group, ordinal, flag))[group]
        changed, original = pages[ordinal - 1], optional[group][1][ordinal - 1]
        assert changed[3] == original[3] and changed[1][4] == original[1][4]

    files["mutated_dictionary_crc"], dict_crc = CRC(good, dictionary)
    files["mutated_reference_crc"], ref_crc = CRC(good, reference)
    files["mutated_plain_crc"], plain_crc = CRC(good, plain)
    two_pages, _ = CRC(files["mutated_plain_crc"], last_plain)
    files["mutated_competing_crc"], _ = CRC(two_pages, optional[2][0])
    for label in ("mutated_dictionary_crc", "mutated_reference_crc", "mutated_plain_crc", "mutated_competing_crc"):
        BAD(files[label], rows, 1, "CRC")

    def unequal_true(header):
        header[2] = TType.I32, header[2][1] + 1
        header[8][1][7] = TType.BOOL, True

    files["mutated_reference_size"] = SPLICE["rewrite_header"](good, reference, unequal_true)
    files["mutated_plain_size"] = SPLICE["rewrite_header"](good, plain, unequal_true)
    files["mutated_false_size"] = SPLICE["rewrite_header"](good, plain, lambda header:
        header.update({2: (TType.I32, header[2][1] + 1)}))
    for label in ("mutated_reference_size", "mutated_plain_size", "mutated_false_size"):
        assert READ_GROUP(OPEN(files[label]), 0) == rows[0]

    local_ref = mandatory[2][1][0]
    ref_start = local_ref[2]
    assert local_ref[1][8][1][5][1] == 0 and local_ref[3][0] <= 32
    local_wire = files["local_micros"]
    files["mutated_reference_width"] = local_wire[:ref_start] + bytes([33]) + local_wire[ref_start + 1:]
    BAD(files["mutated_reference_width"], required, 2)

    files["mutated_reentry"] = SPLICE["retag"](files["mutated_plain_crc"], last_plain, 8)
    files["mutated_starts_plain"] = SPLICE["retag"](good, reference, 0)
    files["native_v1_component"] = produce(local, required[2:], checksum=False, pages="1.0")
    files["native_dictionary_only_component"] = PLAIN["produce"](local, required[2:], checksum=False, dictionary=True)
    first_two = [(local_wire, 0), (local_wire, 1)]
    files["assembled_late_v1"] = ASSEMBLE(first_two + [(files["native_v1_component"], 0)])
    files["assembled_dictionary_only"] = ASSEMBLE(first_two + [(files["native_dictionary_only_component"], 0)])
    v1_file, dictionary_file = (OPEN(files[name]) for name in ("assembled_late_v1", "assembled_dictionary_only"))
    for parquet in (v1_file, dictionary_file):
        assert [READ_GROUP(parquet, index) for index in range(3)] == required
    _, *v1_pages = RAW_FRAMES(files["assembled_late_v1"], v1_file.metadata.row_group(2).column(1))
    assert all(frame[1][1][1] == 0 for frame in v1_pages)
    assert [frame[1][5][1][2][1] for frame in v1_pages] == [8, 0, 0]
    _, *dict_pages = RAW_FRAMES(files["assembled_dictionary_only"], dictionary_file.metadata.row_group(2).column(1))
    assert dict_pages and all(frame[1][8][1][4][1] == 8 for frame in dict_pages)

    files["native_plain"] = PLAIN["produce"](utc, rows, checksum=True)
    files["native_snappy"] = BASE["produce"](utc, rows, checksum=False)
    evidence = [*dict_crc, *ref_crc, *plain_crc, local_ref[0], last_plain[0],
                v1_pages[0][0], optional[0][0][0], optional[0][1][1][0],
                optional[0][1][0][1][2][1]]
    return files, cases, evidence


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, cases, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-uncompressed-fallback-v2-") as temporary:
        output = Path(temporary)
        for name, wire in files.items():
            (output / f"{name}.parquet").write_bytes(wire)
        for name, (_, rows) in cases.items():
            lines = [",".join("null" if value is None else str(value) for value in group) for group in rows]
            (output / f"{name}.txt").write_text("\n".join(lines))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in output.glob("*.arrows")} == set(cases)
        outputs = {}
        for name, (field, rows) in cases.items():
            outputs[name] = (output / f"{name}.arrows").read_bytes()
            VERIFY_IPC(outputs[name], field, rows)
        assert outputs["utc_nanos"] == outputs["mutated_true_reference_flag"] == outputs["mutated_absent_plain_flag"]


if __name__ == "__main__":
    main()
