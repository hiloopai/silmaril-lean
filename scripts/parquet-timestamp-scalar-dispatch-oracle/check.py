"""Compare header-selected TIMESTAMP scalar decoding with pinned native producers."""

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
BSS = runpy.run_path(str(HERE.parent / "parquet-timestamp-byte-stream-split-oracle/check.py"))
DELTA = BSS["DELTA"]
OPEN, READ, HYBRID, VERIFY_IPC, THRIFT, MIXED, FRAMES, GZIP, BAD, CRC, produce = (
    BSS[name] for name in ("OPEN", "READ", "HYBRID", "VERIFY_IPC", "THRIFT", "MIXED", "FRAMES",
                           "GZIP", "BAD", "CRC", "produce"))
ASSEMBLE_GROUPS = DELTA["ASSEMBLE"]
TAGS = {"plain": (0, "PLAIN"), "delta": (5, "DELTA_BINARY_PACKED"), "split": (9, "BYTE_STREAM_SPLIT")}
BASE_CODECS = {
    0: lambda stored, _: stored,
    1: lambda stored, size: pa.Codec("snappy").decompress(stored, size).to_pybytes(),
}


def metadata(wire, group=0):
    footer = MIXED["metadata"](wire)
    return footer, THRIFT["column_metadata"](footer, group, 1)


def chunk_bytes(wire, group):
    _, column = metadata(wire, group)
    start, stop = MIXED["column_extent"](column)
    return wire[start:stop]


def frame_tag(header):
    if header[1][1] == 0:
        return header[5][1][2][1]
    assert header[1][1] == 3
    return header[8][1][4][1]


def read_scalars(tag, body, present):
    if tag == 5:
        return DELTA["decode_delta"](body, present)[0]
    assert len(body) == 8 * present
    if tag == 0:
        return [value for value, in struct.iter_unpack("<q", body)]
    assert tag == 9
    return [int.from_bytes(body[index::present], "little", signed=True) for index in range(present)]


def inspect(wire, field, groups, expected_tags, codecs=BASE_CODECS):
    parquet = OPEN(wire)
    assert parquet.num_row_groups == len(groups) and parquet.schema_arrow.field(1).equals(field)
    captures = []
    for index, expected in enumerate(groups):
        footer, column = metadata(wire, index)
        _, _, leaf = THRIFT["list_field"](footer, 2)
        assert leaf[1] == (TType.I32, 2) and leaf[3] == (TType.I32, int(field.nullable))
        annotation = leaf[10][1][8][1]
        assert annotation[1] == (TType.BOOL, field.type.tz == "UTC")
        assert annotation[2][1] == {{"us": 2, "ns": 3}[field.type.unit]: (TType.STRUCT, {})}
        codec = column[4][1]
        assert codec in codecs and column[1][1] == 2 and column[5][1] == len(expected)
        assert THRIFT["list_field"](column, 3) == [b"ticks"] and not (set(column) & {10, 11})
        start, stop = MIXED["column_extent"](column)
        native_column = parquet.metadata.row_group(index).column(1)
        assert start == column[9][1] == native_column.data_page_offset
        assert stop - start == column[7][1] == native_column.total_compressed_size
        pages = list(FRAMES(wire, start, stop))
        assert pages[0][0] == start and pages[-1][2] + len(pages[-1][3]) == stop
        tags = [frame_tag(header) for _, header, _, _ in pages]
        assert set(tags) == expected_tags[index] and set(THRIFT["list_field"](column, 2)) == {3, *tags}
        assert sum(payload - pos + header[2][1] for pos, header, payload, _ in pages) == column[6][1]
        cursor = 0
        for (_, header, _, stored), tag in zip(pages, tags, strict=True):
            assert len(stored) == header[3][1]
            if 4 in header:
                assert zlib.crc32(stored) == header[4][1] % 2**32
            if header[1][1] == 0:
                info = header[5][1]
                count = info[1][1]
                assert info[3][1] == info[4][1] == 3
                body = codecs[codec](stored, header[2][1])
                assert len(body) == header[2][1]
                value_start = 4 + struct.unpack_from("<I", body)[0] if field.nullable else 0
                levels = body[4:value_start] if field.nullable else b""
                values = body[value_start:]
            else:
                info = header[8][1]
                count, nulls, rows, level_bytes, repetitions = (info[key][1] for key in (1, 2, 3, 5, 6))
                assert rows == count and repetitions == 0
                assert level_bytes <= min(header[2][1], header[3][1])
                levels, suffix = stored[:level_bytes], stored[level_bytes:]
                expanded = header[2][1] - level_bytes
                flag = info.get(7, (TType.BOOL, True))[1]
                values = codecs[codec if flag else 0](suffix, expanded)
                assert len(values) == expanded and expected[cursor:cursor + count].count(None) == nulls
            slots = expected[cursor:cursor + count]
            cursor += count
            assert len(slots) == count
            mask = [int(tick is not None) for tick in slots]
            if field.nullable:
                assert HYBRID(levels, 1, count) == mask
            else:
                assert not levels and all(mask)
            assert read_scalars(tag, values, sum(mask)) == [tick for tick in slots if tick is not None]
        assert cursor == len(expected) and READ(parquet, index) == expected
        print(f"group {index}: codec {codec}, tags {tags}, offsets {[page[0] for page in pages]}")
        captures.append(pages)
    return captures


def assemble_chunk(parts, template):
    """Replace the final selected chunk with original complete frames from one-group inputs."""
    footer, target = metadata(template)
    start, stop = MIXED["column_extent"](target)
    footer_size, = struct.unpack_from("<I", template, len(template) - 8)
    assert stop == len(template) - 8 - footer_size
    chunks, sized_columns = [], []
    for source in parts:
        _, column = metadata(source)
        assert column[4] == target[4]
        chunks.append(chunk_bytes(source, 0))
        sized_columns.append(column)
    group, = THRIFT["list_field"](footer, 4)
    assert sum(column[5][1] for column in sized_columns) == target[5][1] == group[3][1]
    for key, group_key in ((6, 2), (7, 6)):
        total = sum(column[key][1] for column in sized_columns)
        if group_key in group:
            group[group_key] = (TType.I64, group[group_key][1] + total - target[key][1])
        target[key] = (TType.I64, total)
    target[2] = TType.LIST, (TType.I32, [0, 3, 5, 9])
    encoded = THRIFT["encode"](footer)
    assembled = template[:start] + b"".join(chunks) + encoded + struct.pack("<I", len(encoded)) + b"PAR1"
    assert chunk_bytes(assembled, 0) == b"".join(chunks)
    return assembled


def make_mixed_chunk(field, codec, versions, selected_rows):
    joined = sum(selected_rows, [])
    template = produce(field, [joined], versions[0], codec, checksum=True, encoding="PLAIN")
    parts = [produce(field, [rows], version, codec, checksum=True, encoding=TAGS[profile][1])
             for rows, version, profile in zip(selected_rows, versions, ("delta", "plain", "split"), strict=True)]
    return assemble_chunk(parts, template), [joined]


def footer_tags(wire, group, tags):
    def edit(footer):
        THRIFT["column_metadata"](footer, group, 1)[2] = (TType.LIST, (TType.I32, tags))
    return THRIFT["rewrite_footer"](wire, edit)


def fixtures():
    utc = pa.field("ticks", pa.timestamp("ns", "UTC"))
    local = pa.field("ticks", pa.timestamp("us"), nullable=False)
    rows = BSS["timestamp_groups"]()
    required = [[0 if tick is None else tick for tick in group] for group in rows]
    wires, cases = {}, {}
    for profile, (tag, encoding) in TAGS.items():
        for page_version, field, groups in (("1.0", local, required), ("2.0", utc, rows)):
            for codec in ("NONE", "SNAPPY"):
                name = f"native_{profile}_v{page_version[0]}_{codec.lower()}"
                print(name)
                wire = produce(field, groups, page_version, codec, checksum=profile != "plain" or page_version == "2.0",
                               encoding=encoding)
                inspect(wire, field, groups, [{tag}] * len(groups))
                wires[name], cases[name] = wire, (field, groups)
    segments = [rows[0][:8], rows[2][:10], rows[2][10:20]]
    for name, codec, versions in (
            ("assembled_chunk_none", "NONE", ("1.0", "2.0", "1.0")),
            ("assembled_chunk_snappy", "SNAPPY", ("2.0", "1.0", "2.0"))):
        print(name)
        wire, groups = make_mixed_chunk(utc, codec, versions, segments)
        pages, = inspect(wire, utc, groups, [{0, 5, 9}])
        assert [frame_tag(header) for _, header, _, _ in pages] == [5, 0, 9]
        assert all(4 in header for _, header, _, _ in pages)
        assert [header[1][1] for _, header, _, _ in pages] == [0 if v == "1.0" else 3 for v in versions]
        wires[name], cases[name] = wire, (utc, groups)

    mixed = [("native_plain_v2_none", 0), ("native_delta_v2_snappy", 1),
             ("assembled_chunk_snappy", 0), ("native_split_v2_none", 2)]
    wire = ASSEMBLE_GROUPS([(wires[name], i) for name, i in mixed])
    groups = [cases[name][1][i] for name, i in mixed]
    print("assembled_groups")
    captures = inspect(wire, utc, groups, [{0}, {5}, {0, 5, 9}, {9}])
    for index, (name, original) in enumerate(mixed):
        assert chunk_bytes(wire, index) == chunk_bytes(wires[name], original)
    wires["assembled_groups"], cases["assembled_groups"] = wire, (utc, groups)
    _, plain, split = captures[2]
    wires["mutated_late_crc"], crc = CRC(wire, plain)
    BAD(wires["mutated_late_crc"], groups, 2, "CRC")
    wires["mutated_undeclared_split"] = footer_tags(wire, 2, [0, 3, 5])
    wires["mutated_unsupported_tag"] = GZIP["retag"](wire, split, 7)
    wires["mutated_footer_tag"] = footer_tags(wire, 2, [0, 3, 5, 9, 7])
    assert chunk_bytes(wires["mutated_undeclared_split"], 2) == chunk_bytes(wire, 2)
    assert chunk_bytes(wires["mutated_footer_tag"], 2) == chunk_bytes(wire, 2)
    wires["native_unsupported_codec"] = produce(utc, rows, "2.0", "BROTLI", checksum=True, encoding="PLAIN")
    wires["native_dictionary"] = DELTA["ORACLE"]["produce"](utc, rows, checksum=True, dictionary=True)
    return wires, cases, [*crc, split[0]]


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    wires, cases, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in wires.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-scalar-dispatch-") as temporary:
        output = Path(temporary)
        for name, wire in wires.items():
            (output / f"{name}.parquet").write_bytes(wire)
        for name, (_, rows) in cases.items():
            lines = [",".join("null" if tick is None else str(tick) for tick in group) for group in rows]
            (output / f"{name}.txt").write_text("\n".join(lines))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in output.glob("*.arrows")} == set(cases)
        for name, (field, rows) in cases.items():
            VERIFY_IPC((output / f"{name}.arrows").read_bytes(), field, rows)


if __name__ == "__main__":
    main()
