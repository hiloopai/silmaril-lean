"""Check strict Snappy V2 TIMESTAMP fallback with genuine PyArrow files."""

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
import pyarrow.parquet as pq
from thrift.Thrift import TType

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DICT = runpy.run_path(str(HERE.parent / "parquet-timestamp-snappy-dictionary-v2-oracle/check.py"))
PRIOR = runpy.run_path(str(HERE.parent / "parquet-timestamp-snappy-fallback-oracle/check.py"))
SPLICE = runpy.run_path(str(HERE.parent / "parquet-timestamp-gzip-fallback-v2-oracle/check.py"))
THRIFT, MIXED, ASSEMBLE = DICT["THRIFT"], DICT["MIXED"], DICT["ASSEMBLY"]["assemble"]
CRC, READ_GROUP, VERIFY_IPC = (DICT[name] for name in ("CRC", "READ_GROUP", "VERIFY_IPC"))
OPEN, BAD, HYBRID = DICT["open_checked"], DICT["assert_bad"], DICT["SNAPPY"]["hybrid"]
BATCH, MIN, MAX = (PRIOR[name] for name in ("BATCH", "MIN", "MAX"))


def produce(field, groups, *, checksum, pages="2.0", codec="SNAPPY"):
    schema = pa.schema([pa.field("decoy", pa.int32(), nullable=False), field])
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=pages,
                          compression={"ticks": codec}, use_dictionary=["ticks"], write_statistics=False,
                          store_schema=False, write_page_checksum=checksum, dictionary_pagesize_limit=8,
                          write_batch_size=BATCH, data_page_size=24) as writer:
        for group in groups:
            ticks = pa.array(group, type=pa.int64()).view(field.type)
            decoy = pa.array(range(len(group)), type=pa.int32())
            writer.write_table(pa.Table.from_arrays([decoy, ticks], schema=schema))
    return sink.getvalue().to_pybytes()


def inspect(wire, field, groups, checksum):
    parquet = OPEN(wire)
    footer = MIXED["metadata"](wire)
    _, _, leaf = THRIFT["list_field"](footer, 2)
    annotation = leaf[10][1][8][1]
    assert leaf[1] == (TType.I32, 2) and leaf[3] == (TType.I32, int(field.nullable))
    assert leaf[4] == (TType.STRING, b"ticks") and annotation[1] == (TType.BOOL, field.type.tz == "UTC")
    unit = {"us": 2, "ns": 3}[field.type.unit]
    assert annotation[2][1] == {unit: (TType.STRUCT, {})}
    assert parquet.schema_arrow.field(1).equals(field) and parquet.num_row_groups == len(groups)
    codec = pa.Codec("snappy")
    captured, all_flags = [], set()
    for index, expected in enumerate(groups):
        metadata = THRIFT["column_metadata"](footer, index, 1)
        assert THRIFT["column_metadata"](footer, index, 0)[4][1] == 0
        assert metadata[1][1] == 2 and metadata[4][1] == 1 and metadata[5][1] == len(expected)
        assert THRIFT["list_field"](metadata, 3) == [b"ticks"]
        column = parquet.metadata.row_group(index).column(1)
        assert column.encodings == ("PLAIN", "RLE", "RLE_DICTIONARY")
        start, stop = MIXED["column_extent"](metadata)
        dictionary, *pages = list(DICT["ASSEMBLY"]["frames"](wire, start, stop))
        assert start == dictionary[0] == metadata[11][1] == column.dictionary_page_offset
        assert pages[0][0] == metadata[9][1] == column.data_page_offset
        for _, header, _, stored in (dictionary, *pages):
            assert (4 in header) == checksum and header[3][1] == len(stored)
            if checksum:
                assert header[4][1] % 2**32 == zlib.crc32(stored)
        _, header, _, stored = dictionary
        assert header[1][1] == 2 and header[7][1][2][1] == 0
        assert header[2][1] == 8 * header[7][1][1][1]
        entries = [word for word, in struct.iter_unpack("<q", codec.decompress(stored, header[2][1]).to_pybytes())]
        cursor, tags, flags, referenced = 0, [], [], []
        for _, header, _, stored in pages:
            assert header[1][1] == 3
            info = header[8][1]
            count, nulls, rows, tag, size, repetition, compressed = (info[i][1] for i in range(1, 8))
            slots = expected[cursor:cursor + count]
            cursor += count
            assert rows == count == len(slots) == BATCH and slots.count(None) == nulls
            assert repetition == 0 and size <= min(header[2][1], header[3][1])
            levels, suffix = stored[:size], stored[size:]
            if field.nullable:
                assert HYBRID(levels, 1, count) == [int(slot is not None) for slot in slots]
            else:
                assert size == 0 and all(slot is not None for slot in slots)
            expanded_size = header[2][1] - size
            words = codec.decompress(suffix, expanded_size).to_pybytes() if compressed else suffix
            assert len(words) == expanded_size
            present = [slot for slot in slots if slot is not None]
            if tag == 8:
                assert [entries[i] for i in HYBRID(words[1:], words[0], len(present))] == present
                referenced.extend(present)
            else:
                assert tag == 0 and [word for word, in struct.iter_unpack("<q", words)] == present
            tags.append(tag)
            flags.append(compressed)
        assert tags == [8, 0, 0] and cursor == len(expected)
        assert entries == list(dict.fromkeys(referenced))
        assert READ_GROUP(parquet, index) == expected
        print(f"{field.type} group {index}: original dictionary at {dictionary[0]}, tags {tags}, flags {flags}")
        captured.append((dictionary, pages))
        all_flags.update(zip(tags, flags, strict=True))
    assert all_flags == {(8, True), (8, False), (0, True), (0, False)}
    return captured


def flip_suffix(wire, frame):
    _, header, start, body = frame
    info = header[8][1]
    assert 4 not in header and info[7][1] and info[5][1] < len(body)
    suffix = start + info[5][1]
    return wire[:suffix] + bytes([wire[suffix] ^ 1]) + wire[suffix + 1:]


def fixtures():
    first, last = PRIOR["groups"]()
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
    files["mutated_dictionary_crc"], dict_crc = CRC(good, dictionary)
    files["mutated_reference_crc"], ref_crc = CRC(good, reference)
    files["mutated_plain_crc"], plain_crc = CRC(good, plain)
    files["mutated_competing_crc"], _ = CRC(files["mutated_plain_crc"], optional[2][0])
    for label in ("mutated_dictionary_crc", "mutated_reference_crc", "mutated_plain_crc", "mutated_competing_crc"):
        BAD(files[label], rows, 1, "CRC")

    local_ref, _, local_plain = mandatory[2][1]
    files["mutated_reference_suffix"] = flip_suffix(files["local_micros"], local_ref)
    files["mutated_plain_suffix"] = flip_suffix(files["local_micros"], local_plain)
    for label in ("mutated_reference_suffix", "mutated_plain_suffix"):
        BAD(files[label], required, 2)

    files["mutated_reentry"] = SPLICE["retag"](files["mutated_plain_crc"], last_plain, 8)
    files["mutated_starts_plain"] = SPLICE["retag"](good, reference, 0)
    v1 = produce(utc, rows[2:], checksum=True, pages="1.0")
    dict_only = DICT["produce"](utc, rows[2:], checksum=True)
    first_two = [(good, 0), (good, 1)]
    files["assembled_late_v1"] = ASSEMBLE(first_two + [(v1, 0)])
    files["assembled_dictionary_only"] = ASSEMBLE(first_two + [(dict_only, 0)])
    v1_file, dictionary_file = (OPEN(files[name]) for name in ("assembled_late_v1", "assembled_dictionary_only"))
    for parquet in (v1_file, dictionary_file):
        assert [READ_GROUP(parquet, index) for index in range(3)] == rows
    _, *v1_pages = list(DICT["SNAPPY"]["raw_frames"](files["assembled_late_v1"],
                                                    v1_file.metadata.row_group(2).column(1)))
    assert all(frame[1][1][1] == 0 for frame in v1_pages)
    assert [frame[1][5][1][2][1] for frame in v1_pages] == [8, 0, 0]
    _, *dict_pages = list(DICT["SNAPPY"]["raw_frames"](files["assembled_dictionary_only"],
                                                       dictionary_file.metadata.row_group(2).column(1)))
    assert dict_pages and all(frame[1][8][1][4][1] == 8 for frame in dict_pages)

    files["plain_only"] = DICT["produce"](utc, rows, checksum=True, dictionary=False)
    files["uncompressed"] = produce(utc, rows, checksum=False, codec="NONE")
    evidence = [*dict_crc, *ref_crc, *plain_crc, local_ref[0], local_plain[0], last_plain[0],
                reference[0], v1_pages[0][0], optional[0][0][0], optional[0][1][1][0],
                optional[0][1][0][1][2][1]]
    return files, cases, evidence


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, cases, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-snappy-fallback-v2-") as temporary:
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
        for name, (field, rows) in cases.items():
            VERIFY_IPC((output / f"{name}.arrows").read_bytes(), field, rows)


if __name__ == "__main__":
    main()
