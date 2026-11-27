"""Verify strict codec-0 PLAIN V2 TIMESTAMP on PyArrow and Thrift fixtures."""

from copy import deepcopy
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
DICT = runpy.run_path(str(HERE.parent / "parquet-timestamp-snappy-dictionary-v2-oracle/check.py"))
GZIP = runpy.run_path(str(HERE.parent / "parquet-timestamp-gzip-fallback-v2-oracle/check.py"))
THRIFT, MIXED = DICT["THRIFT"], DICT["MIXED"]
FRAMES, ASSEMBLE = (DICT["ASSEMBLY"][name] for name in ("frames", "assemble"))
OPEN, BAD = DICT["open_checked"], DICT["assert_bad"]
READ, VERIFY_IPC, HYBRID = DICT["READ_GROUP"], DICT["VERIFY_IPC"], DICT["SNAPPY"]["hybrid"]


def produce(field, groups, *, checksum, pages="2.0", codec="NONE", dictionary=False):
    schema = pa.schema([pa.field("decoy", pa.int32(), nullable=False), field])
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=pages,
                          compression={"ticks": codec}, use_dictionary=["ticks"] if dictionary else False,
                          write_statistics=False, store_schema=False, write_page_checksum=checksum,
                          write_batch_size=16, data_page_size=48) as writer:
        for rows in groups:
            ticks = pa.array(rows, type=pa.int64()).view(field.type)
            decoy = pa.array(range(len(rows)), type=pa.int32())
            writer.write_table(pa.Table.from_arrays([decoy, ticks], schema=schema))
    return sink.getvalue().to_pybytes()


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
    all_frames = []
    for index, expected in enumerate(groups):
        metadata = THRIFT["column_metadata"](footer, index, 1)
        column = parquet.metadata.row_group(index).column(1)
        assert column.compression == "UNCOMPRESSED" and not column.has_dictionary_page
        assert metadata[1][1] == 2 and metadata[4][1] == 0 and metadata[5][1] == len(expected)
        assert THRIFT["list_field"](metadata, 3) == [b"ticks"]
        assert set(THRIFT["list_field"](metadata, 2)) == {0, 3} and 11 not in metadata
        start, stop = MIXED["column_extent"](metadata)
        assert start == metadata[9][1] == column.data_page_offset
        assert stop - start == column.total_compressed_size
        frames = list(FRAMES(wire, start, stop))
        cursor, flags = 0, []
        for ordinal, (_, header, _, body) in enumerate(frames):
            assert header[1][1] == 3 and header[2][1] == header[3][1] == len(body)
            assert (4 in header) == checksum
            if checksum:
                assert header[4][1] % 2**32 == zlib.crc32(body)
            info = header[8][1]
            count, nulls, rows, tag, definition_size, rep = (info[i][1] for i in range(1, 7))
            slots = expected[cursor:cursor + count]
            cursor += count
            assert len(slots) == count == rows and tag == rep == 0 and slots.count(None) == nulls
            flag = info[7][1] if 7 in info else None
            expected_flag = changed_flag[2] if changed_flag is not None and (index, ordinal) == changed_flag[:2] else False
            assert flag is expected_flag
            assert definition_size <= len(body)
            definitions, suffix = body[:definition_size], body[definition_size:]
            if field.nullable:
                assert HYBRID(definitions, 1, count) == [int(slot is not None) for slot in slots]
            else:
                assert definition_size == 0
            assert len(suffix) == 8 * (count - nulls)
            assert [word for word, in struct.iter_unpack("<q", suffix)] == [slot for slot in slots if slot is not None]
            flags.append(flag)
        assert cursor == len(expected) and READ(parquet, index) == expected
        print(f"{field.type} group {index}: {len(frames)} original PLAIN V2 pages, storage flags {flags}")
        all_frames.append(frames)
    return all_frames


def remove_last_flag(wire, frame, group_index):
    offset, header, body_start, stored = frame
    footer_size, = struct.unpack_from("<I", wire, len(wire) - 8)
    assert body_start + len(stored) == len(wire) - 8 - footer_size
    edited = deepcopy(header)
    assert edited[8][1].pop(7) == (TType.BOOL, False)
    encoded = THRIFT["encode"](edited)
    delta = len(encoded) - (body_start - offset)
    assert delta == -1

    def resize_footer(footer):
        group = THRIFT["list_field"](footer, 4)[group_index]
        column = THRIFT["column_metadata"](footer, group_index, 1)
        for fields, keys in ((column, (6, 7)), (group, (2, 6))):
            for key in keys:
                if key in fields:
                    kind, size = fields[key]
                    assert kind == TType.I64
                    fields[key] = kind, size + delta

    repaired = THRIFT["rewrite_footer"](wire, resize_footer)
    return repaired[:offset] + encoded + repaired[body_start:]


def fixtures():
    utc = pa.field("ticks", pa.timestamp("ns", "UTC"))
    local = pa.field("ticks", pa.timestamp("us"), nullable=False)
    rows = DICT["GROUPS"]
    required = [[0 if slot is None else slot for slot in group] for group in rows]
    cases = {"native_utc": (utc, rows, True), "native_local": (local, required, False)}
    files = {name: produce(field, groups, checksum=checksum) for name, (field, groups, checksum) in cases.items()}
    captures = {name: inspect(files[name], *case) for name, case in cases.items()}
    good = files["native_utc"]
    late = captures["native_utc"][2]
    last = late[-1]
    files["mutated_true_flag"] = GZIP["rewrite_header"](good, last, lambda header:
        header[8][1].update({7: (TType.BOOL, True)}))
    files["mutated_absent_flag"] = remove_last_flag(good, last, 2)
    for name, flag in (("mutated_true_flag", True), ("mutated_absent_flag", None)):
        cases[name] = cases["native_utc"]
        inspect(files[name], *cases[name], (2, len(late) - 1, flag))

    level_page, scalar_page = late[:2]
    assert level_page[1][8][1][5][1] > 0
    assert scalar_page[1][8][1][5][1] < len(scalar_page[3])
    files["mutated_level_crc"], levels = DICT["CRC"](good, level_page)
    offset, header, body_start, body = scalar_page
    scalar_start = body_start + header[8][1][5][1]
    bad_suffix = good[:scalar_start] + bytes([good[scalar_start] ^ 1]) + good[scalar_start + 1:]
    scalar = [offset, header[4][1] % 2**32, zlib.crc32(bad_suffix[body_start:body_start + len(body)])]
    assert scalar[1] != scalar[2]
    files["mutated_suffix_crc"] = bad_suffix
    for name in ("mutated_level_crc", "mutated_suffix_crc"):
        BAD(files[name], rows, 2, "CRC")
    files["mutated_declared_size"] = GZIP["rewrite_header"](good, scalar_page, lambda header:
        header.update({2: (TType.I32, header[2][1] + 1)}))
    def unequal_true(header):
        header[2] = TType.I32, header[2][1] + 1
        header[8][1][7] = TType.BOOL, True

    files["mutated_true_size"] = GZIP["rewrite_header"](good, scalar_page, unequal_true)
    files["mutated_page_encoding"] = GZIP["retag"](good, scalar_page, 5)
    files["mutated_row_count"] = GZIP["rewrite_header"](good, level_page, lambda header:
        header[8][1].update({key: (TType.I32, header[8][1][key][1] + 1) for key in (1, 3)}))
    for name in ("mutated_declared_size", "mutated_true_size", "mutated_page_encoding", "mutated_row_count"):
        assert [READ(OPEN(files[name]), index) for index in range(2)] == rows[:2]

    v1 = produce(local, required[2:], checksum=False, pages="1.0")
    base = files["native_local"]
    files["assembled_late_v1"] = ASSEMBLE([(base, 0), (base, 1), (v1, 0)])
    assert [READ(OPEN(files["assembled_late_v1"]), i) for i in range(3)] == required
    files["dictionary"] = produce(utc, rows, checksum=True, dictionary=True)
    files["wrong_codec"] = produce(utc, rows, checksum=True, codec="SNAPPY")
    first = captures["native_utc"][0][0]
    return files, cases, [*levels, *scalar, first[0], first[1][3][1], len(rows[2])]


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, cases, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-uncompressed-v2-") as temporary:
        output = Path(temporary)
        for name, wire in files.items():
            (output / f"{name}.parquet").write_bytes(wire)
        for name, (_, rows, _) in cases.items():
            lines = [",".join("null" if value is None else str(value) for value in group) for group in rows]
            (output / f"{name}.txt").write_text("\n".join(lines))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in output.glob("*.arrows")} == set(cases)
        for name, (field, rows, _) in cases.items():
            VERIFY_IPC((output / f"{name}.arrows").read_bytes(), field, rows)


if __name__ == "__main__":
    main()
