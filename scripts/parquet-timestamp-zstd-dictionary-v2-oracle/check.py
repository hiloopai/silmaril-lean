"""Check native Zstd dictionary-only V2 TIMESTAMP and Lean Arrow IPC."""

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
PLAIN = runpy.run_path(str(HERE.parent / "parquet-timestamp-zstd-v2-oracle/check.py"))
THRIFT, GZIP, MIXED, DISPATCH = (PLAIN[name] for name in ("THRIFT", "GZIP", "MIXED", "DISPATCH"))
BATCH, MIN, MAX = (PLAIN[name] for name in ("BATCH", "MIN", "MAX"))


def produce(field, groups, *, checksum=True, pages="2.0", dictionary_limit=2**20):
    schema = pa.schema([pa.field("decoy", pa.int32(), nullable=False), field])
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=pages,
                          compression={field.name: "ZSTD"}, compression_level={field.name: 3},
                          use_dictionary=[field.name], dictionary_pagesize_limit=dictionary_limit,
                          write_statistics=False, store_schema=False, write_page_checksum=checksum,
                          write_batch_size=BATCH, data_page_size=24) as writer:
        for group in groups:
            slots = pa.array(group, type=pa.int64()).view(field.type)
            writer.write_table(pa.Table.from_arrays([pa.array(range(len(group)), type=pa.int32()), slots],
                                                    schema=schema))
    return sink.getvalue().to_pybytes()


def check_stored(frame, checksum):
    _, header, _, body = frame
    assert header[3][1] == len(body) and (4 in header) == checksum
    if checksum:
        assert header[4][1] % 2**32 == zlib.crc32(body)


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
        check_stored(dictionary, checksum)
        assert extent(dictionary_body) == len(dictionary_body)
        assert PLAIN["FLAT"]["first_block"](dictionary_body)["dictionary_field_bytes"] == 0
        words = codec.decompress(dictionary_body, dictionary_header[2][1]).to_pybytes()
        entries = [word for word, in struct.iter_unpack("<q", words)]
        assert len(words) == dictionary_header[2][1] == 8 * dictionary_info[1][1]
        assert entries == list(dict.fromkeys(value for value in rows if value is not None))
        original_entries.append(tuple(entries))

        cursor, flags = 0, []
        for frame in pages:
            _, header, _, body = frame
            assert header[1][1] == 3
            check_stored(frame, checksum)
            info = header[8][1]
            count, nulls, page_rows, tag, levels, repetitions, flag = (info[i][1] for i in range(1, 8))
            slots = rows[cursor:cursor + count]
            cursor += count
            assert len(slots) == count == page_rows and slots.count(None) == nulls
            assert tag == 8 and repetitions == 0 and levels <= min(header[2][1], header[3][1])
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
                refs = codec.decompress(suffix, exact).to_pybytes()
            else:
                assert header[3][1] == header[2][1]
                refs = suffix
            assert len(refs) == exact and refs
            indices = hybrid(refs[1:], refs[0], sum(mask))
            assert [entries[i] for i in indices] == [s for s in slots if s is not None]
            flags.append(flag)
        assert cursor == len(rows)
        all_flags.update(flags)
        captures.append((dictionary, pages))
        print(f"{field.type} group {index}: dictionary {start}, pages {[p[0] for p in pages]}, flags {flags}")
    assert len(set(original_entries)) == len(groups)
    assert all_flags == {False, True}
    return captures


def replace_stored(wire, frame, candidates):
    for candidate in candidates:
        try:
            changed, crc = PLAIN["DATE_V1"]["replace_stored"](wire, frame, candidate, THRIFT)
        except AssertionError:
            continue
        assert crc == zlib.crc32(candidate)
        return changed
    raise AssertionError("no candidate retains the original Compact CRC field extent")


def corrupt_magic(wire, frame, levels, extent):
    body = frame[3]
    candidates = (body[:levels] + bytes([body[levels] ^ 1, octet]) + body[levels + 2:]
                  for octet in range(256))
    changed = replace_stored(wire, frame, candidates)
    start = frame[2]
    assert changed[start:start + levels] == body[:levels]
    assert extent(changed[start + levels:start + len(body)]) is None
    return changed


def fixtures():
    groups = [[MIN, None, -19, MAX, -19, None, MIN, MAX] * 8,
              [-719528, MAX, None, MIN, MIN, None, MAX, -719528] * 48,
              [None, -4, MAX, 107, 107, None, MAX, -4] * 8]
    required = [[value if value is not None else 0 for value in group] for group in groups]
    cases = {
        "utc_nanos": (pa.field("ticks", pa.timestamp("ns", "UTC")), groups, True),
        "local_micros": (pa.field("ticks", pa.timestamp("us"), nullable=False), required, False),
    }
    extent = PLAIN["DATE_V1"]["frame_extent"]()
    files, observed = {}, {}
    for name, (field, ticks, checksum) in cases.items():
        files[name] = produce(field, ticks, checksum=checksum)
        observed[name] = inspect(files[name], field, ticks, checksum, extent)

    wire = files["utc_nanos"]
    (first_dict, first_pages), (dictionary, pages), (_, raw_pages) = observed["utc_nanos"]
    late, raw = pages[-1], raw_pages[0]
    levels, raw_levels = late[1][8][1][5][1], raw[1][8][1][5][1]
    assert len(pages) == 3 and late[1][8][1][7][1] and levels > 0
    assert len(raw_pages) == 1 and not raw[1][8][1][7][1] and raw_levels > 0
    files["mutated_dictionary_crc"], dictionary_crc = GZIP["corrupt_frame_crc"](wire, dictionary)
    files["mutated_reference_crc"], ref_crc = GZIP["corrupt_frame_crc"](wire, late)
    files["mutated_raw_crc"], raw_crc = GZIP["corrupt_frame_crc"](wire, raw)
    files["mutated_dictionary_magic"] = corrupt_magic(wire, dictionary, 0, extent)
    files["mutated_reference_magic"] = corrupt_magic(wire, late, levels, extent)
    files["mutated_two_groups"], _ = GZIP["corrupt_frame_crc"](files["mutated_reference_magic"], raw)
    files["mutated_raw_flag_true"] = PLAIN["DATE_V2"]["change_flag"](wire, raw, True, THRIFT)
    files["mutated_frame_flag_false"] = PLAIN["DATE_V2"]["change_flag"](wire, late, False, THRIFT)

    header_edit = DISPATCH["FALLBACK"]["rewrite_header"]
    files["mutated_rows_before_crc"] = header_edit(files["mutated_dictionary_crc"], late, lambda h:
        h[8][1].update({key: (TType.I32, h[8][1][key][1] + 1) for key in (1, 3)}))
    files["mutated_dictionary_encoding"] = header_edit(wire, dictionary, lambda h:
        h[7][1].update({2: (TType.I32, 2)}))
    body = raw[3]
    assert body[raw_levels] == 2 and body[raw_levels + 1] % 2 == 1
    files["mutated_reference_width"] = replace_stored(wire, raw,
        (body[:raw_levels] + bytes([width]) + body[raw_levels + 1:] for width in range(33, 256)))
    files["mutated_reference_index"] = replace_stored(wire, raw,
        (body[:raw_levels + 2] + bytes([octet]) + body[raw_levels + 3:] for octet in range(3, 256, 4)))

    for name, index, reason in (
        ("mutated_dictionary_crc", 1, "CRC"), ("mutated_reference_crc", 1, "CRC"),
        ("mutated_raw_crc", 2, "CRC"), ("mutated_dictionary_magic", 1, "zstd"),
        ("mutated_reference_magic", 1, "zstd"), ("mutated_two_groups", 1, "zstd"),
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
    files["v1_dictionary"] = produce(field, groups, pages="1.0")
    files["v2_plain"] = PLAIN["produce"](field, groups, checksum=True)
    files["v2_fallback"] = produce(field, groups[1:2], dictionary_limit=8)
    v1_offset = pq.ParquetFile(pa.BufferReader(files["v1_dictionary"])).metadata.row_group(0).column(1).data_page_offset
    fallback = pq.ParquetFile(pa.BufferReader(files["v2_fallback"]))
    column = fallback.metadata.row_group(0).column(1)
    _, *fallback_pages = DISPATCH["frames"](files["v2_fallback"], column.dictionary_page_offset,
                                           column.dictionary_page_offset + column.total_compressed_size)
    assert [f[1][8][1][4][1] for f in fallback_pages] == [8, 0, 0]
    assert GZIP["read_group"](fallback, 0) == groups[1]
    data_expanded = sum(f[1][2][1] for f in first_pages)
    cap = data_expanded + first_dict[1][2][1] - 1
    assert data_expanded <= cap
    evidence = [*dictionary_crc, *ref_crc, *raw_crc, v1_offset, fallback_pages[1][0], first_dict[0], first_pages[0][0], cap]
    return files, cases, evidence


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, cases, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-zstd-dictionary-v2-") as temporary:
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
