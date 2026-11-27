"""Compare selected scalar and strict V2 dictionary groups against native Parquet and Arrow."""

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
COMPRESSED = runpy.run_path(str(HERE.parent / "parquet-timestamp-scalar-codecs-oracle/check.py"))
SCALAR = COMPRESSED["SCALAR"]
THRIFT, MIXED, FRAMES, OPEN, READ, HYBRID, CRC, BAD, VERIFY_IPC = (
    SCALAR[name] for name in ("THRIFT", "MIXED", "FRAMES", "OPEN", "READ", "HYBRID", "CRC", "BAD", "VERIFY_IPC"))
CODECS = {"none": 0, "snappy": 1, "gzip": 2, "zstd": 6}


def produce_dictionary(field, groups, codec, fallback, pages="2.0"):
    schema = pa.schema([pa.field("decoy", pa.int32(), nullable=False), field])
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=pages,
                          compression={"ticks": codec.upper()}, use_dictionary=["ticks"],
                          write_statistics=False, store_schema=False, write_page_checksum=True,
                          dictionary_pagesize_limit=16 if fallback else 1024 * 1024,
                          write_batch_size=128, data_page_size=24) as writer:
        for group in groups:
            ticks = pa.array(group, type=pa.int64()).view(field.type)
            decoy = pa.array(range(len(group)), type=pa.int32())
            writer.write_table(pa.Table.from_arrays([decoy, ticks], schema=schema))
    return sink.getvalue().to_pybytes()


def frames_at(wire, index):
    _, metadata = SCALAR["metadata"](wire, index)
    start, stop = MIXED["column_extent"](metadata)
    frames = list(FRAMES(wire, start, stop))
    assert frames[0][0] == start and frames[-1][2] + len(frames[-1][3]) == stop
    return metadata, frames


def check_footer(wire, field, groups):
    parquet = OPEN(wire)
    _, _, leaf = THRIFT["list_field"](MIXED["metadata"](wire), 2)
    assert leaf[1] == (TType.I32, 2) and leaf[3] == (TType.I32, int(field.nullable))
    assert leaf[4] == (TType.STRING, b"ticks")
    timestamp = leaf[10][1][8][1]
    assert timestamp[1] == (TType.BOOL, field.type.tz == "UTC")
    assert timestamp[2][1] == {{"us": 2, "ns": 3}[field.type.unit]: (TType.STRUCT, {})}
    assert parquet.schema_arrow.field(1).equals(field) and parquet.num_row_groups == len(groups)
    return parquet


def inspect_dictionary(wire, field, groups, codec, fallback, codecs):
    parquet = check_footer(wire, field, groups)
    selected = []
    for index, rows in enumerate(groups):
        metadata, frames = frames_at(wire, index)
        assert metadata[4][1] == codec and metadata[5][1] == len(rows)
        assert metadata[1][1] == 2 and THRIFT["list_field"](metadata, 3) == [b"ticks"]
        assert set(THRIFT["list_field"](metadata, 2)) == {0, 3, 8}
        assert 10 not in metadata and frames[0][0] == metadata[11][1]
        column = parquet.metadata.row_group(index).column(1)
        assert column.dictionary_page_offset == frames[0][0]
        assert column.total_compressed_size == metadata[7][1]
        assert sum(payload - offset + header[2][1] for offset, header, payload, _ in frames) == metadata[6][1]
        for _, header, _, body in frames:
            assert header[3][1] == len(body) and zlib.crc32(body) == header[4][1] % 2**32
        (_, description, _, stored), *data = frames
        entries_header = description[7][1]
        assert description[1][1] == 2 and entries_header[2][1] == 0
        entries = codecs[codec](stored, description[2][1])
        assert len(entries) == description[2][1] == 8 * entries_header[1][1]
        dictionary = [word for word, in struct.iter_unpack("<q", entries)]
        assert data[0][0] == metadata[9][1] == column.data_page_offset
        cursor, tags, referenced = 0, [], []
        for _, header, _, stored in data:
            assert header[1][1] == 3
            info = header[8][1]
            count, nulls, page_rows, tag, level_bytes, repetitions = (info[i][1] for i in range(1, 7))
            assert page_rows == count and repetitions == 0
            assert level_bytes <= min(header[2][1], header[3][1])
            page = rows[cursor:cursor + count]
            cursor += count
            assert len(page) == count and page.count(None) == nulls
            levels, suffix = stored[:level_bytes], stored[level_bytes:]
            mask = [int(tick is not None) for tick in page]
            if field.nullable:
                assert HYBRID(levels, 1, count) == mask
            else:
                assert not levels and all(mask)
            flag = info.get(7, (TType.BOOL, True))[1]
            decoded_size = header[2][1] - level_bytes
            values = codecs[codec if flag else 0](suffix, decoded_size)
            assert len(values) == decoded_size
            expected = [tick for tick in page if tick is not None]
            if tag == 8:
                observed = [dictionary[index] for index in HYBRID(values[1:], values[0], len(expected))]
                referenced.extend(observed)
            else:
                assert tag == 0
                observed = [word for word, in struct.iter_unpack("<q", values)]
            assert observed == expected
            tags.append(tag)
        assert tags == ([8, 0, 0, 0] if fallback else [8, 8, 8, 8])
        assert dictionary == list(dict.fromkeys(referenced)) and cursor == len(rows)
        assert READ(parquet, index) == rows
        selected.append(dictionary)
        print(f"group {index}: codec {codec}, dictionary entries {len(dictionary)}, V2 tags {tags}")
    assert len(set(map(tuple, selected))) == len(groups)


def fixtures():
    extent = COMPRESSED["DATE_ZSTD"]["frame_extent"]()
    codecs = {**SCALAR["BASE_CODECS"], 2: COMPRESSED["gzip_body"],
              6: lambda stored, size: COMPRESSED["zstd_body"](extent, stored, size)}
    utc = pa.field("ticks", pa.timestamp("ns", "UTC"))
    local = pa.field("ticks", pa.timestamp("us"), nullable=False)
    raw = SCALAR["BSS"]["timestamp_groups"]()
    dict_rows = [raw[0], raw[2]]
    required = [[0 if tick is None else tick for tick in group] for group in dict_rows]
    wires, cases = {}, {}

    def add_dictionary(name, field, groups, codec, fallback):
        print(name)
        wire = produce_dictionary(field, groups, codec, fallback)
        inspect_dictionary(wire, field, groups, CODECS[codec], fallback, codecs)
        wires[name], cases[name] = wire, (field, groups, [f"dictionary_{codec}"] * len(groups))

    for codec in CODECS:
        for mode in ("references", "fallback"):
            add_dictionary(f"native_{codec}_{mode}", utc, dict_rows, codec, mode == "fallback")
    add_dictionary("native_local_snappy_references", local, required, "snappy", False)

    for name, group, pages, codec, tag in (
        ("native_scalar_delta", 0, "1.0", "GZIP", "delta"),
        ("native_scalar_split", 2, "2.0", "ZSTD", "split"),
        ("native_scalar_plain", 0, "1.0", "NONE", "plain"),
    ):
        print(name)
        groups = [raw[group]]
        value_tag, encoding = SCALAR["TAGS"][tag]
        wire = SCALAR["produce"](utc, groups, pages, codec, checksum=True, encoding=encoding)
        SCALAR["inspect"](wire, utc, groups, [{value_tag}], codecs=codecs)
        wires[name], cases[name] = wire, (utc, groups, [f"scalar_{codec.lower()}"])

    origins = [
        ("native_scalar_delta", 0), ("native_none_references", 0), ("native_scalar_split", 0),
        ("native_snappy_fallback", 1), ("native_gzip_references", 1), ("native_zstd_fallback", 0),
        ("native_scalar_plain", 0), ("native_zstd_references", 1), ("native_gzip_fallback", 1),
        ("native_snappy_references", 0), ("native_none_fallback", 1),
    ]
    assembled = SCALAR["ASSEMBLE_GROUPS"]([(wires[name], index) for name, index in origins])
    rows = [cases[name][1][index] for name, index in origins]
    modes = [cases[name][2][index] for name, index in origins]
    parquet = check_footer(assembled, utc, rows)
    captures = []
    for group, (name, index) in enumerate(origins):
        metadata, frames = frames_at(assembled, group)
        source_metadata, source = frames_at(wires[name], index)
        assert SCALAR["chunk_bytes"](assembled, group) == SCALAR["chunk_bytes"](wires[name], index)
        assert metadata[4] == source_metadata[4] and metadata[2] == source_metadata[2]
        assert metadata[5][1] == len(rows[group])
        assert metadata[9][1] == frames[int(11 in metadata)][0]
        if 11 in metadata:
            assert metadata[11][1] == frames[0][0]
        assert READ(parquet, group) == rows[group]
        captures.append(frames)
        print(f"assembled group {group}: {modes[group]}, original frame offsets {[frame[0] for frame in frames]}")
    wires["assembled_mixed"], cases["assembled_mixed"] = assembled, (utc, rows, modes)

    wires["mutated_late_zstd_crc"], zstd = CRC(assembled, captures[7][0])
    wires["mutated_late_gzip_crc"], gzip = CRC(assembled, captures[8][1])
    wires["mutated_competing_crc"], _ = CRC(wires["mutated_late_zstd_crc"], captures[8][1])
    for name, index in (("mutated_late_zstd_crc", 7), ("mutated_late_gzip_crc", 8),
                        ("mutated_competing_crc", 7)):
        BAD(wires[name], rows, index, "CRC")

    def set_codec(footer):
        THRIFT["column_metadata"](footer, 5, 1)[4] = (TType.I32, 7)
    wires["mutated_unsupported_codec"] = THRIFT["rewrite_footer"](assembled, set_codec)
    _, meta = SCALAR["metadata"](assembled, 5)
    tags = THRIFT["list_field"](meta, 2)
    assert tags == [0, 3, 8]
    wires["mutated_dictionary_encodings"] = SCALAR["footer_tags"](assembled, 5, tags + [5, 9])
    for name in ("mutated_unsupported_codec", "mutated_dictionary_encodings"):
        assert SCALAR["chunk_bytes"](wires[name], 5) == SCALAR["chunk_bytes"](assembled, 5)
    wires["mutated_dictionary_data_tag"] = SCALAR["GZIP"]["retag"](assembled, captures[3][1], 9)

    native_v1 = produce_dictionary(utc, [rows[5]], "snappy", False, pages="1.0")
    v1 = SCALAR["ASSEMBLE_GROUPS"]([(assembled, i) for i in range(5)] + [(native_v1, 0)])
    _, v1_frames = frames_at(v1, 5)
    assert v1_frames[1][1][1][1] == 0
    assert SCALAR["chunk_bytes"](v1, 5) == SCALAR["chunk_bytes"](native_v1, 0)
    assert [READ(OPEN(v1), i) for i in range(6)] == rows[:6]
    wires["native_dictionary_v1_control"] = native_v1
    wires["assembled_late_dictionary_v1"] = v1
    return wires, cases, [*zstd, *gzip, captures[3][1][0], v1_frames[1][0]]


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    wires, cases, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in wires.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-scalar-dictionary-") as temporary:
        output = Path(temporary)
        for name, wire in wires.items():
            (output / f"{name}.parquet").write_bytes(wire)
        for name, (_, rows, modes) in cases.items():
            lines = [mode + "," + ",".join("null" if tick is None else str(tick) for tick in group)
                     for mode, group in zip(modes, rows, strict=True)]
            (output / f"{name}.txt").write_text("\n".join(lines))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in output.glob("*.arrows")} == set(cases)
        for name, (field, rows, _) in cases.items():
            VERIFY_IPC((output / f"{name}.arrows").read_bytes(), field, rows)


if __name__ == "__main__":
    main()
