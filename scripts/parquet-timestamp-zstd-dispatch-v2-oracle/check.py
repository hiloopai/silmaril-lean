"""Check native and unchanged-chunk assembled Zstd V2 TIMESTAMP dispatch."""

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
import pyarrow.parquet as pq
from thrift.Thrift import TType

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
FALLBACK = runpy.run_path(str(HERE.parent / "parquet-timestamp-zstd-fallback-v2-oracle/check.py"))
PLAIN, THRIFT, GZIP, MIXED, DISPATCH = (FALLBACK[name] for name in ("PLAIN", "THRIFT", "GZIP", "MIXED", "DISPATCH"))
BATCH, MIN, MAX = (FALLBACK[name] for name in ("BATCH", "MIN", "MAX"))
PRODUCE, CHECK_STORED = FALLBACK["PRODUCE"], FALLBACK["CHECK_STORED"]
CORRUPT_MAGIC, REPLACE_STORED, RETAG = (FALLBACK[name] for name in ("CORRUPT_MAGIC", "REPLACE_STORED", "RETAG"))


def inspect(wire, field, groups, profiles, checksum, extent):
    footer = MIXED["metadata"](wire)
    footer_size, = struct.unpack_from("<I", wire, len(wire) - 8)
    footer_start = len(wire) - 8 - footer_size
    _, decoy, leaf = THRIFT["list_field"](footer, 2)
    assert 10 not in decoy and leaf[1] == (TType.I32, 2)
    assert leaf[3] == (TType.I32, int(field.nullable)) and leaf[4] == (TType.STRING, b"ticks")
    annotation = leaf[10][1][8][1]
    assert annotation[1] == (TType.BOOL, field.type.tz == "UTC")
    unit = {"us": 2, "ns": 3}[field.type.unit]
    assert annotation[2][1] == {unit: (TType.STRUCT, {})}

    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.schema_arrow.field(1).equals(field) and parquet.num_row_groups == len(groups)
    codec = pa.Codec("zstd")
    captures, all_flags, original_entries = [], set(), []
    for index, (rows, profile) in enumerate(zip(groups, profiles, strict=True)):
        assert THRIFT["column_metadata"](footer, index, 0)[4] == (TType.I32, 0)
        metadata = THRIFT["column_metadata"](footer, index, 1)
        column = parquet.metadata.row_group(index).column(1)
        assert metadata[1] == (TType.I32, 2) and metadata[4] == (TType.I32, 6)
        assert THRIFT["list_field"](metadata, 3) == [b"ticks"]
        has_dictionary = profile != "plain"
        assert set(THRIFT["list_field"](metadata, 2)) == ({0, 3, 8} if has_dictionary else {0, 3})
        assert metadata[5][1] == column.num_values == len(rows)
        start, stop = MIXED["column_extent"](metadata)
        assert stop - start == column.total_compressed_size and 4 <= start < stop <= footer_start
        assert GZIP["read_group"](parquet, index) == rows

        pages = list(DISPATCH["frames"](wire, start, stop))
        dictionary, entries = None, []
        if has_dictionary:
            dictionary, *pages = pages
            assert dictionary[0] == metadata[11][1] == start == column.dictionary_page_offset
            _, dictionary_header, _, dictionary_body = dictionary
            assert dictionary_header[1] == (TType.I32, 2)
            dictionary_info = dictionary_header[7][1]
            assert dictionary_info[2] == (TType.I32, 0)
            CHECK_STORED(dictionary, checksum)
            assert extent(dictionary_body) == len(dictionary_body)
            assert PLAIN["FLAT"]["first_block"](dictionary_body)["dictionary_field_bytes"] == 0
            words = codec.decompress(dictionary_body, dictionary_header[2][1]).to_pybytes()
            entries = [word for word, in struct.iter_unpack("<q", words)]
            assert len(words) == dictionary_header[2][1] == 8 * dictionary_info[1][1]
            original_entries.append(tuple(entries))
        else:
            assert 11 not in metadata and column.dictionary_page_offset is None
        assert pages[0][0] == metadata[9][1] == column.data_page_offset

        cursor, flags, tags, referenced = 0, [], [], []
        for frame in pages:
            _, header, _, body = frame
            assert header[1][1] == 3
            CHECK_STORED(frame, checksum)
            info = header[8][1]
            count, nulls, page_rows, tag, levels, repetitions, flag = (info[i][1] for i in range(1, 8))
            slots = rows[cursor:cursor + count]
            cursor += count
            assert len(slots) == count == page_rows and slots.count(None) == nulls
            assert tag in (8, 0) and repetitions == 0 and levels <= min(header[2][1], header[3][1])
            definitions, suffix = body[:levels], body[levels:]
            mask = [int(slot is not None) for slot in slots]
            hybrid = DISPATCH["FALLBACK"]["ORACLE"]["hybrid"]
            if field.nullable:
                assert hybrid(definitions, 1, count) == mask
            else:
                assert not definitions and all(mask)
            exact = header[2][1] - levels
            if flag:
                assert extent(suffix) == len(suffix)
                assert PLAIN["FLAT"]["first_block"](suffix)["dictionary_field_bytes"] == 0
                values = codec.decompress(suffix, exact).to_pybytes()
            else:
                assert header[3][1] == header[2][1]
                values = suffix
            assert len(values) == exact
            present = [slot for slot in slots if slot is not None]
            if tag == 8:
                indices = hybrid(values[1:], values[0], sum(mask))
                assert [entries[i] for i in indices] == present
                referenced.extend(present)
            else:
                assert [word for word, in struct.iter_unpack("<q", values)] == present
            tags.append(tag)
            flags.append(flag)
        expected_tags = {"plain": [0] * len(pages), "references": [8] * len(pages), "fallback": [8, 0, 0]}
        assert cursor == len(rows) and tags == expected_tags[profile]
        assert entries == list(dict.fromkeys(referenced))
        all_flags.update(zip(tags, flags, strict=True))
        captures.append((dictionary, pages))
        print(f"{field.type} group {index}: {profile}, tags {tags}, flags {flags}")
    assert len(set(original_entries)) == len(original_entries)
    assert all_flags == {(8, False), (8, True), (0, False), (0, True)}
    return captures


def fixtures():
    generator = random.Random(62023)
    dense = [[generator.randrange(MIN, MAX + 1) for _ in range(BATCH)] for _ in range(3)]
    first = [MIN, None, -19, MAX, -19, None, MIN, MAX] * (BATCH // 8)
    later = [-719528, MAX, None, MIN, MIN, None, MAX, -719528] * (BATCH // 8)
    sparse = [None] * BATCH
    sparse[2], sparse[63] = MIN, MAX
    native_groups = [[MIN, None] * 32, first + later + dense[0], [MAX, None] * 64, sparse + dense[1] + first]
    plain_groups = [first + dense[2] + later, dense[1] + first]
    extent = PLAIN["DATE_V1"]["frame_extent"]()
    cases, files, observed = {}, {}, {}
    for label, field, checksum in (
        ("utc", pa.field("ticks", pa.timestamp("ns", "UTC")), True),
        ("local", pa.field("ticks", pa.timestamp("us"), nullable=False), False),
    ):
        native, plain = native_groups, plain_groups
        if not field.nullable:
            native = [[value if value is not None else fill for value in group]
                      for fill, group in zip([MIN, 0, MAX, 0], native, strict=True)]
            plain = [[value if value is not None else 0 for value in group] for group in plain]
        native_wire = PRODUCE(field, native, checksum=checksum, dictionary_limit=16)
        plain_wire = PLAIN["produce"](field, plain, checksum=checksum)
        files[f"native_{label}"] = native_wire
        files[f"plain_{label}_producer"] = plain_wire
        files[f"assembled_{label}"] = DISPATCH["assemble"]([
            (native_wire, 0), (plain_wire, 0), (native_wire, 1), (native_wire, 2), (plain_wire, 1), (native_wire, 3)
        ])
        cases[f"native_{label}"] = (field, native, ["references", "fallback", "references", "fallback"], checksum)
        cases[f"assembled_{label}"] = (
            field, [native[0], plain[0], native[1], native[2], plain[1], native[3]],
            ["references", "plain", "fallback", "references", "plain", "fallback"], checksum,
        )
    for label, case in cases.items():
        observed[label] = inspect(files[label], *case, extent)

    good = files["assembled_utc"]
    (_, first_plain), (_, fallback_data), (dictionary, references), (_, raw_plain), (_, tail) = (
        observed["assembled_utc"][1:]
    )
    compressed_plain = first_plain[-1]
    assert compressed_plain[1][8][1][7][1]
    assert not raw_plain[0][1][8][1][7][1] and not references[0][1][8][1][7][1]
    files["bad_plain_crc"], plain_crc = GZIP["corrupt_frame_crc"](good, first_plain[0])
    files["bad_dictionary_crc"], dict_crc = GZIP["corrupt_frame_crc"](good, dictionary)
    files["bad_fallback_crc"], fallback_crc = GZIP["corrupt_frame_crc"](good, fallback_data[0])
    files["bad_plain_magic"] = CORRUPT_MAGIC(good, compressed_plain, compressed_plain[1][8][1][5][1], extent)
    files["bad_fallback_magic"] = CORRUPT_MAGIC(good, fallback_data[1], fallback_data[1][1][8][1][5][1], extent)
    files["bad_dictionary_magic"] = CORRUPT_MAGIC(good, dictionary, 0, extent)
    files["two_bad_groups"], _ = GZIP["corrupt_frame_crc"](files["bad_dictionary_crc"], first_plain[0])
    files["bad_plain_flag"] = PLAIN["DATE_V2"]["change_flag"](good, raw_plain[0], True, THRIFT)
    files["bad_reentry"] = RETAG(good, tail[-1], 8)
    frame = references[0]
    levels = frame[1][8][1][5][1]
    stored = frame[3]
    files["bad_reference_width"] = REPLACE_STORED(good, frame,
        (stored[:levels] + bytes([width]) + stored[levels + 1:] for width in range(33, 256)))

    field, groups, _, _ = cases["assembled_utc"]
    for name, index, reason in (
        ("bad_plain_crc", 1, "CRC"), ("bad_dictionary_crc", 3, "CRC"),
        ("bad_fallback_crc", 2, "CRC"), ("bad_plain_magic", 1, "zstd"),
        ("bad_fallback_magic", 2, "zstd"), ("bad_dictionary_magic", 3, "zstd"), ("two_bad_groups", 1, "CRC"),
    ):
        parquet = pq.ParquetFile(pa.BufferReader(files[name]), page_checksum_verification=True)
        assert [GZIP["read_group"](parquet, i) for i in range(index)] == groups[:index]
        try:
            GZIP["read_group"](parquet, index)
        except (pa.ArrowException, OSError) as error:
            assert reason.lower() in str(error).lower(), str(error)
        else:
            raise AssertionError("PyArrow accepted original group with damaged integrity bytes")

    files["plain_v1"] = PLAIN["produce"](field, groups[1:2], checksum=True, pages="1.0")
    files["dictionary_v1"] = PRODUCE(field, native_groups, pages="1.0", dictionary_limit=16)
    files["snappy"] = PLAIN["produce"](field, groups[1:2], checksum=True, codec="SNAPPY")
    v1_offsets = [pq.ParquetFile(pa.BufferReader(files[name])).metadata.row_group(0).column(1).data_page_offset
                  for name in ("plain_v1", "dictionary_v1")]
    first_dict, first_refs = observed["native_utc"][0]
    refs_cap = sum(frame[1][2][1] for frame in [first_dict, *first_refs]) - 1
    plain_cap = sum(frame[1][2][1] for frame in first_plain) - 1
    evidence = [*plain_crc, *dict_crc, *fallback_crc, compressed_plain[0], fallback_data[1][0],
                raw_plain[0][0], tail[-1][0], references[0][0], refs_cap, plain_cap, *v1_offsets]
    return files, cases, evidence


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, cases, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-zstd-dispatch-v2-") as temporary:
        output = Path(temporary)
        for name, wire in files.items():
            (output / (name + ".parquet")).write_bytes(wire)
        for name, (_, groups, profiles, _) in cases.items():
            lines = [profile + "," + ",".join("null" if v is None else str(v) for v in group)
                     for profile, group in zip(profiles, groups, strict=True)]
            (output / (name + ".txt")).write_text("\n".join(lines))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in output.glob("*.arrows")} == set(cases)
        for name, (field, groups, _, _) in cases.items():
            GZIP["verify_ipc"]((output / (name + ".arrows")).read_bytes(), field, groups)


if __name__ == "__main__":
    main()
