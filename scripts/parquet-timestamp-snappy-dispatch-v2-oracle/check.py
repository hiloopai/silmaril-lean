"""Verify Snappy V2 TIMESTAMP dispatch on pinned PyArrow files and assemblies."""

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
FALLBACK = runpy.run_path(str(HERE.parent / "parquet-timestamp-snappy-fallback-v2-oracle/check.py"))
DICT, THRIFT, MIXED = (FALLBACK[name] for name in ("DICT", "THRIFT", "MIXED"))
ASSEMBLE, CRC, READ_GROUP, VERIFY_IPC = (FALLBACK[name] for name in ("ASSEMBLE", "CRC", "READ_GROUP", "VERIFY_IPC"))
OPEN, BAD, HYBRID = (FALLBACK[name] for name in ("OPEN", "BAD", "HYBRID"))
BATCH = FALLBACK["BATCH"]


def inspect(wire, field, groups, profiles, checksum):
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
    observed, flags_by_tag = [], set()
    for index, (expected, profile) in enumerate(zip(groups, profiles, strict=True)):
        metadata = THRIFT["column_metadata"](footer, index, 1)
        assert metadata[1][1] == 2 and metadata[4][1] == 1 and metadata[5][1] == len(expected)
        assert THRIFT["list_field"](metadata, 3) == [b"ticks"]
        column = parquet.metadata.row_group(index).column(1)
        start, stop = MIXED["column_extent"](metadata)
        assert stop - start == column.total_compressed_size
        has_dict = profile != "plain"
        assert set(THRIFT["list_field"](metadata, 2)) == ({0, 3, 8} if has_dict else {0, 3})
        original = list(DICT["ASSEMBLY"]["frames"](wire, start, stop))
        for _, header, _, stored in original:
            assert (4 in header) == checksum and header[3][1] == len(stored)
            if checksum:
                assert header[4][1] % 2**32 == zlib.crc32(stored)
        dictionary, entries = None, []
        if has_dict:
            dictionary, *original = original
            assert start == dictionary[0] == metadata[11][1] == column.dictionary_page_offset
            _, header, _, body = dictionary
            assert header[1][1] == 2 and header[7][1][2][1] == 0
            assert header[2][1] == 8 * header[7][1][1][1]
            decoded = codec.decompress(body, header[2][1]).to_pybytes()
            entries = [word for word, in struct.iter_unpack("<q", decoded)]
        else:
            assert 11 not in metadata and column.dictionary_page_offset is None
        assert original[0][0] == metadata[9][1] == column.data_page_offset
        cursor, tags, flags, referenced = 0, [], [], []
        for _, header, _, stored in original:
            assert header[1][1] == 3
            info = header[8][1]
            count, nulls, rows, tag, size, repetition, compressed = (info[i][1] for i in range(1, 8))
            slots = expected[cursor:cursor + count]
            cursor += count
            assert rows == count == len(slots) and slots.count(None) == nulls
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
        expected_tags = {"plain": [0] * len(original), "references": [8] * len(original), "fallback": [8, 0, 0]}
        assert tags == expected_tags[profile] and cursor == len(expected)
        assert entries == list(dict.fromkeys(referenced)) and READ_GROUP(parquet, index) == expected
        print(f"{field.type} group {index}: {profile}, original tags {tags}, flags {flags}")
        observed.append((dictionary, original, stop - start))
        flags_by_tag.update(zip(tags, flags, strict=True))
    assert flags_by_tag == {(8, True), (8, False), (0, True), (0, False)}
    return observed


def fixtures():
    prior_files, prior_cases, _ = FALLBACK["fixtures"]()
    prior_pins = json.loads((FALLBACK["HERE"] / "fixtures.json").read_text())
    files, cases, captured = {}, {}, {}
    for name in ("utc", "local"):
        predecessor = "utc_nanos" if name == "utc" else "local_micros"
        assert sha256(prior_files[predecessor]).hexdigest() == prior_pins[predecessor]
        field, fallback_rows = prior_cases[predecessor]
        checksum = field.nullable
        small, large = (DICT["GROUPS"][i] for i in (1, 0))
        if not field.nullable:
            small, large = ([0 if value is None else value for value in rows] for rows in (small, large))
        native_rows = [small, fallback_rows[0], large, fallback_rows[1]]
        plain_rows = [large, fallback_rows[1][BATCH:2 * BATCH]]
        native = FALLBACK["produce"](field, native_rows, checksum=checksum)
        plain = DICT["produce"](field, plain_rows, checksum=checksum, dictionary=False)
        files[f"native_{name}"] = native
        files[f"plain_{name}_producer"] = plain
        files[f"assembled_{name}"] = ASSEMBLE([(native, 0), (plain, 0), (native, 1), (native, 2),
                                                (plain, 1), (native, 3)])
        cases[f"native_{name}"] = (field, native_rows, ["references", "fallback", "references", "fallback"])
        assembled_rows = [small, plain_rows[0], fallback_rows[0], large, plain_rows[1], fallback_rows[1]]
        cases[f"assembled_{name}"] = (field, assembled_rows,
                                      ["references", "plain", "fallback", "references", "plain", "fallback"])
    for name, (field, rows, profiles) in cases.items():
        captured[name] = inspect(files[name], field, rows, profiles, field.nullable)

    good = files["assembled_utc"]
    field, rows, _ = cases["assembled_utc"]
    (_, plain, _), (_, mixed, chunk_bytes), (dictionary, references, _) = captured["assembled_utc"][1:4]
    files["mutated_plain_crc"], plain_crc = CRC(good, plain[0])
    files["mutated_dictionary_crc"], dict_crc = CRC(good, dictionary)
    files["mutated_reference_crc"], reference_crc = CRC(good, references[0])
    files["mutated_fallback_crc"], fallback_crc = CRC(good, mixed[1])
    files["mutated_competing_crc"], _ = CRC(files["mutated_dictionary_crc"], plain[0])
    for label, index in (("mutated_plain_crc", 1), ("mutated_dictionary_crc", 3),
                         ("mutated_reference_crc", 3), ("mutated_fallback_crc", 2), ("mutated_competing_crc", 1)):
        BAD(files[label], rows, index, "CRC")

    files["mutated_reentry"] = FALLBACK["SPLICE"]["retag"](files["mutated_fallback_crc"], mixed[-1], 8)

    def shift_data_offset(footer):
        metadata = THRIFT["column_metadata"](footer, 2, 1)
        assert metadata[9] == (TType.I64, mixed[0][0])
        metadata[9] = (TType.I64, mixed[0][0] + 1)

    files["mutated_data_offset"] = THRIFT["rewrite_footer"](good, shift_data_offset)
    assert [READ_GROUP(OPEN(files["mutated_data_offset"]), i) for i in range(2)] == rows[:2]

    v1 = DICT["produce"](field, rows[2:3], checksum=True, pages="1.0")
    files["assembled_v1"] = ASSEMBLE([(good, 0), (good, 1), (v1, 0)])
    parquet = OPEN(files["assembled_v1"])
    assert [READ_GROUP(parquet, i) for i in range(3)] == rows[:3]
    v1_pages = list(DICT["SNAPPY"]["raw_frames"](files["assembled_v1"], parquet.metadata.row_group(2).column(1)))[1:]
    assert v1_pages and all(page[1][1][1] == 0 and page[1][5][1][2][1] == 8 for page in v1_pages)
    files["wrong_codec"] = DICT["produce"](field, rows[:1], checksum=False, codec="NONE")
    assert chunk_bytes > captured["assembled_utc"][0][2]
    evidence = [*plain_crc, *dict_crc, *reference_crc, *fallback_crc, mixed[-1][0], mixed[0][0],
                v1_pages[0][0], chunk_bytes - 1]
    return files, cases, evidence


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, cases, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-snappy-dispatch-v2-") as temporary:
        output = Path(temporary)
        for name, wire in files.items():
            (output / f"{name}.parquet").write_bytes(wire)
        for name, (_, rows, profiles) in cases.items():
            lines = [profile + "," + ",".join("null" if value is None else str(value) for value in group)
                     for profile, group in zip(profiles, rows, strict=True)]
            (output / f"{name}.txt").write_text("\n".join(lines))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in output.glob("*.arrows")} == set(cases)
        for name, (field, rows, _) in cases.items():
            VERIFY_IPC((output / f"{name}.arrows").read_bytes(), field, rows)


if __name__ == "__main__":
    main()
