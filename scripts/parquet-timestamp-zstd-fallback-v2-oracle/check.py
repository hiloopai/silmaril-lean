"""Check native Zstd V2 TIMESTAMP dictionary fallback and Lean Arrow IPC."""

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
DICTIONARY = runpy.run_path(str(HERE.parent / "parquet-timestamp-zstd-dictionary-v2-oracle/check.py"))
PLAIN, THRIFT, GZIP, MIXED, DISPATCH = (DICTIONARY[name] for name in ("PLAIN", "THRIFT", "GZIP", "MIXED", "DISPATCH"))
BATCH, MIN, MAX = (DICTIONARY[name] for name in ("BATCH", "MIN", "MAX"))
PRODUCE, CHECK_STORED = DICTIONARY["produce"], DICTIONARY["check_stored"]
CORRUPT_MAGIC, REPLACE_STORED = DICTIONARY["corrupt_magic"], DICTIONARY["replace_stored"]
HEADER_EDIT, RETAG = (DISPATCH["FALLBACK"][name] for name in ("rewrite_header", "retag"))


def inspect(wire, field, groups, checksum, extent):
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
    for index, rows in enumerate(groups):
        assert THRIFT["column_metadata"](footer, index, 0)[4] == (TType.I32, 0)
        metadata = THRIFT["column_metadata"](footer, index, 1)
        column = parquet.metadata.row_group(index).column(1)
        assert metadata[1] == (TType.I32, 2) and metadata[4] == (TType.I32, 6)
        assert THRIFT["list_field"](metadata, 3) == [b"ticks"]
        assert set(THRIFT["list_field"](metadata, 2)) == {0, 3, 8}
        assert metadata[5][1] == column.num_values == len(rows)
        start, stop = MIXED["column_extent"](metadata)
        assert start == column.dictionary_page_offset and stop - start == column.total_compressed_size
        assert 4 <= start < column.data_page_offset < stop <= footer_start
        assert GZIP["read_group"](parquet, index) == rows

        dictionary, *pages = DISPATCH["frames"](wire, start, stop)
        assert dictionary[0] == metadata[11][1] == start
        assert pages[0][0] == metadata[9][1] == column.data_page_offset
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
        assert cursor == len(rows) and tags == [8, 0, 0]
        assert entries == list(dict.fromkeys(referenced))
        all_flags.update(zip(tags, flags, strict=True))
        captures.append((dictionary, pages))
        print(f"{field.type} group {index}: dictionary {start}, tags {tags}, flags {flags}")
    assert len(set(original_entries)) == len(groups)
    assert all_flags == {(8, False), (8, True), (0, False), (0, True)}
    return captures


def fixtures():
    generator = random.Random(62023)
    dense = [[generator.randrange(MIN, MAX + 1) for _ in range(BATCH)] for _ in range(3)]
    first = [MIN, None, -19, MAX, -19, None, MIN, MAX] * (BATCH // 8)
    later = [-719528, MAX, None, MIN, MIN, None, MAX, -719528] * (BATCH // 8)
    sparse = [None] * BATCH
    sparse[2], sparse[63] = MIN, MAX
    groups = [first + later + dense[0], sparse + dense[1] + first, later + first + dense[2]]
    required = [[value if value is not None else 0 for value in group] for group in groups]
    cases = {
        "utc_nanos": (pa.field("ticks", pa.timestamp("ns", "UTC")), groups, True),
        "local_micros": (pa.field("ticks", pa.timestamp("us"), nullable=False), required, False),
    }
    extent = PLAIN["DATE_V1"]["frame_extent"]()
    files, observed = {}, {}
    for name, (field, ticks, checksum) in cases.items():
        files[name] = PRODUCE(field, ticks, checksum=checksum, dictionary_limit=8)
        observed[name] = inspect(files[name], field, ticks, checksum, extent)

    wire = files["utc_nanos"]
    (first_dictionary, first_pages), (dictionary, data), (_, tail) = observed["utc_nanos"]
    reference, raw_plain, compressed_plain = data
    assert [page[1][8][1][7][1] for page in data] == [False, False, True]
    assert tail[0][1][8][1][7][1]
    files["mutated_dictionary_crc"], dictionary_crc = GZIP["corrupt_frame_crc"](wire, dictionary)
    files["mutated_reference_crc"], ref_crc = GZIP["corrupt_frame_crc"](wire, reference)
    files["mutated_plain_crc"], plain_crc = GZIP["corrupt_frame_crc"](wire, raw_plain)
    files["mutated_dictionary_magic"] = CORRUPT_MAGIC(wire, dictionary, 0, extent)
    files["mutated_reference_magic"] = CORRUPT_MAGIC(wire, tail[0], tail[0][1][8][1][5][1], extent)
    files["mutated_plain_magic"] = CORRUPT_MAGIC(wire, compressed_plain, compressed_plain[1][8][1][5][1], extent)
    files["mutated_two_groups"], _ = GZIP["corrupt_frame_crc"](files["mutated_reference_magic"], raw_plain)
    files["mutated_raw_plain_flag_true"] = PLAIN["DATE_V2"]["change_flag"](wire, raw_plain, True, THRIFT)
    files["mutated_frame_flag_false"] = PLAIN["DATE_V2"]["change_flag"](wire, compressed_plain, False, THRIFT)
    files["mutated_rows_before_crc"] = HEADER_EDIT(files["mutated_dictionary_crc"], compressed_plain, lambda header:
        header[8][1].update({key: (TType.I32, header[8][1][key][1] + 1) for key in (1, 3)}))

    files["mutated_reentry"] = RETAG(files["mutated_plain_crc"], compressed_plain, 8)
    files["mutated_unknown_before_reentry"] = RETAG(files["mutated_reentry"], reference, 5)
    files["mutated_starts_plain"] = RETAG(wire, reference, 0)
    body = reference[3]
    levels = reference[1][8][1][5][1]
    files["mutated_raw_width"] = REPLACE_STORED(wire, reference,
        (body[:levels] + bytes([width]) + body[levels + 1:] for width in range(33, 256)))
    files["mutated_two_pages"] = REPLACE_STORED(files["mutated_plain_magic"], reference,
        (body[:levels] + bytes([width]) + body[levels + 1:] for width in range(33, 256)))

    for name, index, reason in (
        ("mutated_dictionary_crc", 1, "CRC"), ("mutated_reference_crc", 1, "CRC"),
        ("mutated_plain_crc", 1, "CRC"), ("mutated_dictionary_magic", 1, "zstd"),
        ("mutated_reference_magic", 2, "zstd"), ("mutated_plain_magic", 1, "zstd"),
        ("mutated_two_groups", 1, "CRC"),
    ):
        opened = pq.ParquetFile(pa.BufferReader(files[name]), page_checksum_verification=True)
        assert [GZIP["read_group"](opened, i) for i in range(index)] == groups[:index]
        try:
            GZIP["read_group"](opened, index)
        except (pa.ArrowException, OSError) as error:
            assert reason.lower() in str(error).lower(), str(error)
        else:
            raise AssertionError("PyArrow accepted the damaged original payload")

    field = cases["utc_nanos"][0]
    files["v1"] = PRODUCE(field, groups, pages="1.0", dictionary_limit=8)
    files["plain_only"] = PLAIN["produce"](field, groups, checksum=True)
    files["dictionary_only"] = PRODUCE(field, [first * 3])
    v1 = pq.ParquetFile(pa.BufferReader(files["v1"]))
    assert GZIP["read_group"](v1, 0) == groups[0]
    v1_offset = v1.metadata.row_group(0).column(1).data_page_offset
    dictionary_only = pq.ParquetFile(pa.BufferReader(files["dictionary_only"]))
    column = dictionary_only.metadata.row_group(0).column(1)
    _, *reference_only = DISPATCH["frames"](files["dictionary_only"], column.dictionary_page_offset,
                                             column.dictionary_page_offset + column.total_compressed_size)
    assert [f[1][8][1][4][1] for f in reference_only] == [8, 8, 8]
    data_expanded = sum(f[1][2][1] for f in first_pages)
    cap = data_expanded + first_dictionary[1][2][1] - 1
    assert data_expanded <= cap
    evidence = [*dictionary_crc, *ref_crc, *plain_crc, compressed_plain[0], tail[0][0],
                first_dictionary[0], first_pages[1][0], v1_offset, cap]
    return files, cases, evidence


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, cases, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-zstd-fallback-v2-") as temporary:
        output = Path(temporary)
        for name, wire in files.items():
            (output / (name + ".parquet")).write_bytes(wire)
        for name, (_, groups, _) in cases.items():
            lines = [",".join("null" if value is None else str(value) for value in group) for group in groups]
            (output / (name + ".txt")).write_text("\n".join(lines))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in output.glob("*.arrows")} == set(cases)
        for name, (field, groups, _) in cases.items():
            GZIP["verify_ipc"]((output / (name + ".arrows")).read_bytes(), field, groups)


if __name__ == "__main__":
    main()
