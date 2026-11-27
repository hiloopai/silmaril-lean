"""Check native Zstandard PLAIN V2 TIMESTAMP and Lean Arrow V5 readback."""

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
DISPATCH = runpy.run_path(str(HERE.parent / "parquet-timestamp-gzip-dispatch-v2-oracle/check.py"))
DATE_V1 = runpy.run_path(str(HERE.parent / "parquet-date-zstd-v1-oracle/check.py"))
DATE_V2 = runpy.run_path(str(HERE.parent / "parquet-date-zstd-v2-oracle/check.py"))
FLAT = runpy.run_path(str(HERE.parent / "parquet-flat-zstd/check.py"))
THRIFT, GZIP, MIXED = DISPATCH["THRIFT"], DISPATCH["GZIP"], DISPATCH["MIXED"]
BATCH = 128
MIN, MAX = -(2**63), 2**63 - 1


def produce(field, groups, *, checksum, pages="2.0", dictionary=False, codec="ZSTD"):
    schema = pa.schema([pa.field("decoy", pa.int32(), nullable=False), field])
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=pages,
                          compression={field.name: codec}, compression_level={field.name: 3} if codec == "ZSTD" else None,
                          use_dictionary=[field.name] if dictionary else False, write_statistics=False,
                          store_schema=False, write_page_checksum=checksum, write_batch_size=BATCH,
                          data_page_size=24) as writer:
        for group in groups:
            slots = pa.array(group, type=pa.int64()).view(field.type)
            writer.write_table(pa.Table.from_arrays([pa.array(range(len(group)), type=pa.int32()), slots],
                                                    schema=schema))
    return sink.getvalue().to_pybytes()


def inspect(wire, field, groups, checksum, extent):
    footer = MIXED["metadata"](wire)
    footer_size, = struct.unpack_from("<I", wire, len(wire) - 8)
    footer_start = len(wire) - 8 - footer_size
    _, decoy, leaf = THRIFT["list_field"](footer, 2)
    assert 10 not in decoy and leaf[1] == (TType.I32, 2)
    assert leaf[3] == (TType.I32, int(field.nullable)) and leaf[4] == (TType.STRING, b"ticks")
    annotation = leaf[10][1][8][1]
    assert annotation[1] == (TType.BOOL, field.type.tz == "UTC")
    unit = {"ms": 1, "us": 2, "ns": 3}[field.type.unit]
    assert annotation[2][1] == {unit: (TType.STRUCT, {})}

    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.schema_arrow.field(1).equals(field) and parquet.num_row_groups == len(groups)
    codec = pa.Codec("zstd")
    captures, observed = [], []
    for index, rows in enumerate(groups):
        assert THRIFT["column_metadata"](footer, index, 0)[4] == (TType.I32, 0)
        metadata = THRIFT["column_metadata"](footer, index, 1)
        column = parquet.metadata.row_group(index).column(1)
        assert metadata[1] == (TType.I32, 2) and metadata[4] == (TType.I32, 6)
        assert THRIFT["list_field"](metadata, 3) == [b"ticks"]
        assert set(THRIFT["list_field"](metadata, 2)) == {0, 3}
        assert 11 not in metadata and column.dictionary_page_offset is None
        assert metadata[5][1] == column.num_values == len(rows)
        start, stop = MIXED["column_extent"](metadata)
        assert start == column.data_page_offset and stop - start == column.total_compressed_size
        assert 4 <= start < stop <= footer_start
        assert GZIP["read_group"](parquet, index) == rows

        frames = list(DISPATCH["frames"](wire, start, stop))
        cursor, flags = 0, []
        for _, header, _, body in frames:
            assert header[1][1] == 3 and header[3][1] == len(body)
            assert (4 in header) == checksum
            if checksum:
                assert header[4][1] % 2**32 == zlib.crc32(body)
            info = header[8][1]
            count, nulls, page_rows, tag, levels, repetitions, flag = (info[i][1] for i in range(1, 8))
            slots = rows[cursor:cursor + count]
            cursor += count
            assert len(slots) == count == page_rows and slots.count(None) == nulls
            assert tag == 0 and repetitions == 0 and levels <= min(header[2][1], header[3][1])
            definitions, suffix = body[:levels], body[levels:]
            mask = [int(slot is not None) for slot in slots]
            if field.nullable:
                assert DISPATCH["FALLBACK"]["ORACLE"]["hybrid"](definitions, 1, count) == mask
            else:
                assert not definitions and all(mask)
            exact = header[2][1] - levels
            if flag:
                assert extent(suffix) == len(suffix)
                assert FLAT["first_block"](suffix)["dictionary_field_bytes"] == 0
                values = codec.decompress(suffix, exact).to_pybytes()
            else:
                assert header[3][1] == header[2][1]
                values = suffix
            assert len(values) == exact
            assert [value for value, in struct.iter_unpack("<q", values)] == [s for s in slots if s is not None]
            flags.append(flag)
        assert cursor == len(rows)
        captures.append(frames)
        observed.append(flags)
        print(f"{field.type} group {index}: frames {[frame[0] for frame in frames]}, Zstd suffix flags {flags}")
    return captures, observed


def fixtures():
    generator = random.Random(48603)
    raw = [[generator.randrange(MIN, MAX + 1) for _ in range(BATCH)] for _ in range(5)]
    optional = [MIN, None, MAX, 0, None, -1, -1, 6] * (BATCH // 8)
    required = [MIN, MAX, 0, -1, 4, 6, 6, 0] * (BATCH // 8)
    admitted = {
        "utc_nanos": (pa.field("ticks", pa.timestamp("ns", "UTC")),
                      [optional + raw[0] + optional, raw[1] + optional + optional, optional + raw[2]], True),
        "local_micros": (pa.field("ticks", pa.timestamp("us"), nullable=False),
                         [required + raw[3], raw[4] + required], False),
        "raw_local_millis": (pa.field("ticks", pa.timestamp("ms")),
                             [raw[0] + [None] * BATCH, raw[1]], True),
    }
    extent = DATE_V1["frame_extent"]()
    files, observed = {}, {}
    for name, (field, groups, checksum) in admitted.items():
        files[name] = produce(field, groups, checksum=checksum)
        observed[name], flags = inspect(files[name], field, groups, checksum, extent)
        assert {flag for group in flags for flag in group} == ({False} if name == "raw_local_millis" else {True, False})
    _, all_null_info, _, all_null_body = observed["raw_local_millis"][0][1]
    assert all_null_info[8][1][2][1] == BATCH == all_null_info[8][1][1][1]
    assert all_null_info[8][1][5][1] == len(all_null_body)

    wire = files["utc_nanos"]
    field, groups, _ = admitted["utc_nanos"]
    first = observed["utc_nanos"][0][0]
    raw_page, _, late = observed["utc_nanos"][1]
    later = observed["utc_nanos"][2][0]
    offset, header, _, stored = late
    definitions = header[8][1][5][1]
    assert header[8][1][7][1] and definitions > 0 and not raw_page[1][8][1][7][1]
    files["mutated_late_crc"], crc = GZIP["corrupt_frame_crc"](wire, late)
    # Change the magic while keeping the recomputed Compact CRC field at its original width.
    malformed = stored[:definitions] + bytes([stored[definitions] ^ 0x19]) + stored[definitions + 1:]
    assert extent(malformed[definitions:]) is None
    files["mutated_late_magic"], recomputed = DATE_V1["replace_stored"](wire, late, malformed, THRIFT)
    assert recomputed == zlib.crc32(malformed)
    files["mutated_raw_flag_true"] = DATE_V2["change_flag"](wire, raw_page, True, THRIFT)
    files["mutated_frame_flag_false"] = DATE_V2["change_flag"](wire, late, False, THRIFT)
    header_edit = DISPATCH["FALLBACK"]["rewrite_header"]
    files["mutated_null_count"] = header_edit(wire, late, lambda h:
        h[8][1].update({2: (TType.I32, h[8][1][2][1] + 1)}))
    files["mutated_level_extent"] = header_edit(wire, late, lambda h:
        h[8][1].update({5: (TType.I32, len(stored) + 1)}))
    files["mutated_two_groups"], _ = GZIP["corrupt_frame_crc"](files["mutated_late_magic"], later)
    files["mutated_early_crc"], early_crc = GZIP["corrupt_frame_crc"](wire, first)
    for name, index, reason in (
        ("mutated_late_crc", 1, "CRC"), ("mutated_late_magic", 1, "zstd"),
        ("mutated_two_groups", 1, "zstd"), ("mutated_early_crc", 0, "CRC"),
    ):
        parquet = pq.ParquetFile(pa.BufferReader(files[name]), page_checksum_verification=True)
        assert [GZIP["read_group"](parquet, i) for i in range(index)] == groups[:index]
        try:
            GZIP["read_group"](parquet, index)
        except (pa.ArrowException, OSError) as error:
            assert reason.lower() in str(error).lower(), str(error)
        else:
            raise AssertionError("PyArrow accepted original group with damaged integrity bytes")

    files["v1"] = produce(field, groups[:1], checksum=True, pages="1.0")
    files["dictionary_v2"] = produce(field, groups[:1], checksum=True, dictionary=True)
    files["snappy_v2"] = produce(field, groups[:1], checksum=True, codec="SNAPPY")
    v1 = pq.ParquetFile(pa.BufferReader(files["v1"]))
    assert GZIP["read_group"](v1, 0) == groups[0]
    v1_offset = v1.metadata.row_group(0).column(1).data_page_offset
    evidence = [*crc, *early_crc, offset, raw_page[0], v1_offset, first[1][3][1], first[1][2][1]]
    return files, admitted, evidence


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, admitted, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-zstd-v2-") as temporary:
        output = Path(temporary)
        for name, wire in files.items():
            (output / (name + ".parquet")).write_bytes(wire)
        for name, (_, groups, _) in admitted.items():
            lines = [",".join("null" if value is None else str(value) for value in group) for group in groups]
            (output / (name + ".txt")).write_text("\n".join(lines))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in output.glob("*.arrows")} == set(admitted)
        for name, (field, groups, _) in admitted.items():
            GZIP["verify_ipc"]((output / (name + ".arrows")).read_bytes(), field, groups)


if __name__ == "__main__":
    main()
