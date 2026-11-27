"""Check native and unchanged-chunk assembled GZIP V2 TIMESTAMP profiles."""

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

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
FALLBACK = runpy.run_path(str(HERE.parent / "parquet-timestamp-gzip-fallback-v2-oracle/check.py"))
MIXED = runpy.run_path(str(HERE.parent / "parquet-timestamp-mixed-groups-oracle/check.py"))
GZIP, THRIFT = FALLBACK["GZIP"], FALLBACK["THRIFT"]
BATCH = FALLBACK["BATCH"]
MIN, MAX = -(2**63), 2**63 - 1


def produce(field, rows, *, dictionary, checksum, page_version="2.0", codec="GZIP"):
    schema = pa.schema([pa.field("decoy", pa.int32(), nullable=False), field])
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=page_version, compression=codec,
                          use_dictionary=["ticks"] if dictionary else False, write_statistics=False,
                          store_schema=False, write_page_checksum=checksum, dictionary_pagesize_limit=16,
                          write_batch_size=BATCH, data_page_size=24) as writer:
        for group in rows:
            ticks = pa.array(group, type=pa.int64()).view(field.type)
            writer.write_table(pa.Table.from_arrays([pa.array(range(len(group)), type=pa.int32()), ticks],
                                                    schema=schema))
    return sink.getvalue().to_pybytes()


def assemble(sources):
    """Copy all original column chunks; update only footer file positions and group list."""
    output = bytearray(b"PAR1")
    groups = []
    base = None
    for ordinal, (wire, index) in enumerate(sources):
        metadata = MIXED["metadata"](wire)
        if base is None:
            base = metadata
        else:
            assert metadata[2] == base[2]
        group = THRIFT["list_field"](metadata, 4)[index]
        first = len(output)
        for chunk in THRIFT["list_field"](group, 1):
            column = chunk[3][1]
            assert not (set(chunk) & {1, 4, 5, 6, 7}) and not (set(column) & {10, 14, 15})
            start, stop = MIXED["column_extent"](column)
            offset = len(output) - start
            output.extend(wire[start:stop])
            MIXED["relocate_offset"](column, 9, offset)
            if 11 in column:
                MIXED["relocate_offset"](column, 11, offset)
            if chunk[2][1]:
                MIXED["relocate_offset"](chunk, 2, offset)
            new_start, new_stop = MIXED["column_extent"](column)
            assert output[new_start:new_stop] == wire[start:stop]
        if 5 in group:
            group[5] = TType.I64, first
        if 7 in group:
            group[7] = TType.I16, ordinal
        groups.append(group)
    base[3] = TType.I64, sum(group[3][1] for group in groups)
    base[4] = TType.LIST, (TType.STRUCT, groups)
    base[6] = TType.STRING, b"Unchanged PyArrow 26.0.1 column chunks with assembled footer"
    footer = THRIFT["encode"](base)
    return bytes(output) + footer + struct.pack("<I", len(footer)) + b"PAR1"


def frames(wire, start, stop):
    cursor = TMemoryBuffer(wire[start:stop])
    protocol = TCompactProtocol(cursor)
    while cursor.cstringio_buf.tell() < stop - start:
        offset = start + cursor.cstringio_buf.tell()
        header = THRIFT["read_struct"](protocol)
        body = start + cursor.cstringio_buf.tell()
        yield offset, header, body, cursor.readAll(header[3][1])
    assert start + cursor.cstringio_buf.tell() == stop


def inspect(wire, field, groups, checksum, expected_profiles):
    footer = MIXED["metadata"](wire)
    _, _, leaf = THRIFT["list_field"](footer, 2)
    assert leaf[1] == (TType.I32, 2) and leaf[3] == (TType.I32, int(field.nullable))
    assert leaf[4] == (TType.STRING, b"ticks")
    logical = leaf[10][1][8][1]
    assert logical[1] == (TType.BOOL, field.type.tz == "UTC")
    unit = {"us": 2, "ns": 3}[field.type.unit]
    assert logical[2][1] == {unit: (TType.STRUCT, {})}
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.schema_arrow.field(1).equals(field) and parquet.num_row_groups == len(groups)
    observed, captures = [], []
    for index, (rows, profile) in enumerate(zip(groups, expected_profiles, strict=True)):
        column = parquet.metadata.row_group(index).column(1)
        metadata = THRIFT["column_metadata"](footer, index, 1)
        assert metadata[1] == (TType.I32, 2) and metadata[4] == (TType.I32, 2)
        assert THRIFT["list_field"](metadata, 3) == [b"ticks"] and metadata[5][1] == len(rows)
        assert set(THRIFT["list_field"](metadata, 2)) == ({0, 3} if profile == "plain" else {0, 3, 8})
        start, stop = MIXED["column_extent"](metadata)
        assert (metadata[11][1] if 11 in metadata else None) == column.dictionary_page_offset
        assert metadata[9][1] == column.data_page_offset and stop - start == column.total_compressed_size
        assert GZIP["read_group"](parquet, index) == rows
        original = list(frames(wire, start, stop))
        entries, dictionary = [], None
        if profile != "plain":
            dictionary, *original = original
            assert dictionary[0] == start == column.dictionary_page_offset
            assert dictionary[1][1][1] == 2 and dictionary[1][7][1][2] == (TType.I32, 0)
            entries = [word for word, in struct.iter_unpack("<q", GZIP["member"](dictionary, checksum))]
            assert len(entries) == dictionary[1][7][1][1][1]
        assert original[0][0] == column.data_page_offset
        cursor, tags, flags, referenced = 0, [], [], []
        for frame in original:
            info, definitions, values, compressed = FALLBACK["suffix"](frame, checksum)
            count, nulls, row_count, tag = (info[i][1] for i in (1, 2, 3, 4))
            slots = rows[cursor:cursor + count]
            assert row_count == count == len(slots) and slots.count(None) == nulls
            cursor += count
            mask = [int(value is not None) for value in slots]
            if field.nullable:
                assert FALLBACK["ORACLE"]["hybrid"](definitions, 1, count) == mask
            else:
                assert not definitions and all(mask)
            present = [value for value in slots if value is not None]
            if tag == 8:
                refs = FALLBACK["ORACLE"]["hybrid"](values[1:], values[0], sum(mask))
                assert [entries[ref] for ref in refs] == present
                referenced.extend(present)
            else:
                assert tag == 0 and [word for word, in struct.iter_unpack("<q", values)] == present
            tags.append(tag)
            flags.append(compressed)
        assert cursor == len(rows) and entries == list(dict.fromkeys(referenced))
        assert tags == sorted(tags, reverse=True)
        assert set(tags) == {"plain": {0}, "references": {8}, "fallback": {0, 8}}[profile]
        print(f"{field.type} group {index}: {profile}, page tags {tags}, storage flags {flags}")
        captures.append((dictionary, original))
        observed.append(flags)
    return captures, observed


def positives():
    native = [[MIN, None] * 384, FALLBACK["DENSE"],
              FALLBACK["SPARSE"] + FALLBACK["LATER"][BATCH:], [MAX, None] * BATCH]
    plain = [[-1, MIN, None, MAX] * 192, FALLBACK["DENSE"]]
    cases, captures, files = {}, {}, {}
    for label, field, checksum in (
        ("utc", pa.field("ticks", pa.timestamp("ns", "UTC")), True),
        ("local", pa.field("ticks", pa.timestamp("us"), nullable=False), False),
    ):
        native_rows, plain_rows = native, plain
        if not field.nullable:
            native_rows = [[value if value is not None else fill for value in group]
                           for fill, group in zip([MIN, 0, 0, MAX], native, strict=True)]
            plain_rows = [[value if value is not None else MIN for value in group] for group in plain]
        native_wire = produce(field, native_rows, dictionary=True, checksum=checksum)
        plain_wire = produce(field, plain_rows, dictionary=False, checksum=checksum)
        parts = [(native_wire, 0), (plain_wire, 0), (native_wire, 1), (plain_wire, 1),
                 (native_wire, 2), (native_wire, 3)]
        cases[f"native_{label}"] = (field, native_rows, checksum, ["references", "fallback", "fallback", "references"])
        files[f"native_{label}"] = native_wire
        cases[f"assembled_{label}"] = (field, [native_rows[0], plain_rows[0], native_rows[1],
                                               plain_rows[1], native_rows[2], native_rows[3]], checksum,
                                       ["references", "plain", "fallback", "plain", "fallback", "references"])
        files[f"assembled_{label}"] = assemble(parts)
        files[f"plain_{label}_producer"] = plain_wire
    for label, settings in cases.items():
        captures[label], flags = inspect(files[label], *settings)
        if label == "assembled_utc":
            assert flags[1] == [True, True, True] and False in flags[3]
    return files, cases, captures


def fixtures():
    files, cases, captures = positives()
    wire = files["assembled_utc"]
    dictionary_groups = captures["assembled_utc"]
    _, leading_plain = dictionary_groups[1]
    _, fallback = dictionary_groups[2]
    dictionary, references = dictionary_groups[5]
    first_plain, fallback_plain, tail_reference = leading_plain[0], fallback[1], references[-1]
    files["bad_plain_outer"], plain_crc = GZIP["corrupt_frame_crc"](wire, first_plain)
    later_plain = leading_plain[1]
    files["bad_plain_inner"] = FALLBACK["V2"]["corrupt_member_suffix"](wire, later_plain)
    files["bad_fallback_inner"] = FALLBACK["V2"]["corrupt_member_suffix"](wire, fallback_plain)
    files["bad_reference_outer"], reference_crc = GZIP["corrupt_frame_crc"](wire, tail_reference)
    files["bad_dictionary_inner"] = GZIP["corrupt_member_crc"](wire, dictionary)
    files["two_bad_groups"], _ = GZIP["corrupt_frame_crc"](files["bad_fallback_inner"], first_plain)
    files["bad_fallback_reentry"] = FALLBACK["retag"](wire, fallback[-1], 8)
    files["bad_tag_before_reentry"] = FALLBACK["retag"](files["bad_fallback_reentry"], fallback[0], 5)
    field, groups, _, _ = cases["assembled_utc"]
    for label, index, reason in (
        ("bad_plain_outer", 1, "CRC"), ("bad_plain_inner", 1, "gzip"),
        ("bad_fallback_inner", 2, "gzip"), ("bad_reference_outer", 5, "CRC"),
        ("bad_dictionary_inner", 5, "gzip"), ("two_bad_groups", 1, "CRC"),
    ):
        parquet = pq.ParquetFile(pa.BufferReader(files[label]), page_checksum_verification=True)
        assert [GZIP["read_group"](parquet, i) for i in range(index)] == groups[:index]
        try:
            GZIP["read_group"](parquet, index)
        except (pa.ArrowException, OSError) as error:
            assert reason.lower() in str(error).lower(), str(error)
        else:
            raise AssertionError("PyArrow admitted original group with damaged integrity bytes")
    files["plain_v1"] = produce(field, groups[1:2], dictionary=False, checksum=True, page_version="1.0")
    files["snappy"] = produce(field, groups[1:2], dictionary=False, checksum=True, codec="SNAPPY")
    plain_v1 = pq.ParquetFile(pa.BufferReader(files["plain_v1"]))
    evidence = [*plain_crc, *reference_crc, dictionary[0], fallback[0][0], fallback_plain[0], fallback[-1][0],
                captures["assembled_utc"][0][0][0], later_plain[0],
                plain_v1.metadata.row_group(0).column(1).data_page_offset]
    return files, cases, evidence


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, cases, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-gzip-dispatch-v2-") as temporary:
        output = Path(temporary)
        for name, wire in files.items():
            (output / (name + ".parquet")).write_bytes(wire)
        for name, (_, groups, _, profiles) in cases.items():
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
