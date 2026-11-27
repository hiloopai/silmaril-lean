"""Pin genuine PyArrow GZIP V2 fallback and compare actual Lean Arrow IPC."""

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
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
V1 = runpy.run_path(str(HERE.parent / "parquet-timestamp-gzip-fallback-v1-oracle/check.py"))
V2 = runpy.run_path(str(HERE.parent / "parquet-timestamp-gzip-dictionary-v2-oracle/check.py"))
GZIP, ORACLE, THRIFT = V1["GZIP"], V1["ORACLE"], V1["THRIFT"]
DENSE, LATER = V1["GROUPS"]
BATCH = V1["BATCH"]
SPARSE = [None] * BATCH
SPARSE[2], SPARSE[173] = -(2**63), 2**63 - 1
UTC_GROUPS = [DENSE, SPARSE + LATER[BATCH:], LATER]


def suffix(frame, checksum):
    _, header, _, stored = frame
    assert header[1][1] == 3 and header[3][1] == len(stored)
    assert (4 in header) == checksum
    if checksum:
        assert header[4][1] % 2**32 == zlib.crc32(stored)
    info = header[8][1]
    assert info[6] == (TType.I32, 0)
    extent, compressed = info[5][1], info[7][1]
    assert 0 <= extent <= min(header[2][1], header[3][1])
    definitions, values = stored[:extent], stored[extent:]
    if compressed:
        decoder = zlib.decompressobj(wbits=31)
        decoded = decoder.decompress(values) + decoder.flush()
        assert decoder.eof and not decoder.unused_data and not decoder.unconsumed_tail
        assert struct.unpack("<II", values[-8:]) == (zlib.crc32(decoded), len(decoded))
    else:
        decoded = values
    assert len(decoded) == header[2][1] - extent
    return info, definitions, decoded, compressed


def inspect(wire, field, rows, checksum):
    footer_size, = struct.unpack_from("<I", wire, len(wire) - 8)
    footer_start = len(wire) - 8 - footer_size
    memory = TMemoryBuffer(wire[footer_start:-8])
    footer = THRIFT["read_struct"](TCompactProtocol(memory))
    assert memory.cstringio_buf.tell() == footer_size
    _, _, leaf = THRIFT["list_field"](footer, 2)
    assert leaf[1] == (TType.I32, 2) and leaf[3] == (TType.I32, int(field.nullable))
    assert leaf[4] == (TType.STRING, b"ticks")
    stamp = leaf[10][1][8][1]
    assert stamp[1] == (TType.BOOL, field.type.tz == "UTC")
    unit = {"ms": 1, "us": 2, "ns": 3}[field.type.unit]
    assert stamp[2][1] == {unit: (TType.STRUCT, {})}
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.schema_arrow.field(1).equals(field) and parquet.metadata.num_row_groups == len(rows)
    captures, dictionaries, flags = [], [], []
    for group, expected in enumerate(rows):
        column = parquet.metadata.row_group(group).column(1)
        metadata = THRIFT["column_metadata"](footer, group, 1)
        assert metadata[1] == (TType.I32, 2) and metadata[4] == (TType.I32, 2)
        assert THRIFT["list_field"](metadata, 3) == [b"ticks"]
        assert set(THRIFT["list_field"](metadata, 2)) == {0, 3, 8}
        assert metadata[5][1] == column.num_values == len(expected)
        assert metadata[11][1] == column.dictionary_page_offset
        assert metadata[9][1] == column.data_page_offset
        assert metadata[7][1] == column.total_compressed_size
        assert 4 <= metadata[11][1] < metadata[9][1] < metadata[11][1] + metadata[7][1] <= footer_start
        assert GZIP["read_group"](parquet, group) == expected
        dictionary, *pages = ORACLE["raw_frames"](wire, column)
        assert dictionary[0] == column.dictionary_page_offset and pages[0][0] == column.data_page_offset
        assert dictionary[1][1][1] == 2 and dictionary[1][7][1][2] == (TType.I32, 0)
        entries = [word for word, in struct.iter_unpack("<q", GZIP["member"](dictionary, checksum))]
        assert len(entries) == dictionary[1][7][1][1][1]
        dictionaries.append(tuple(entries))
        tags, referenced, cursor = [], [], 0
        for frame in pages:
            info, definitions, values, compressed = suffix(frame, checksum)
            count, nulls, row_count, tag = [info[i][1] for i in (1, 2, 3, 4)]
            assert count == row_count
            flags.append((tag, compressed))
            slots = expected[cursor:cursor + count]
            assert len(slots) == count
            cursor += count
            assert slots.count(None) == nulls
            mask = [int(value is not None) for value in slots]
            if field.nullable:
                assert ORACLE["hybrid"](definitions, 1, count) == mask
            else:
                assert not definitions and all(mask)
            present = [value for value in slots if value is not None]
            if tag == 8:
                refs = ORACLE["hybrid"](values[1:], values[0], sum(mask))
                assert [entries[i] for i in refs] == present
                referenced.extend(present)
            else:
                assert tag == 0
                assert [word for word, in struct.iter_unpack("<q", values)] == present
            tags.append(tag)
        assert cursor == len(expected) and tags == [8, 0, 0]
        assert entries == list(dict.fromkeys(referenced))
        captures.append((dictionary, pages))
        print(f"{field.type} group {group}: dictionary {dictionary[0]}, pages {tags}, transition {pages[1][0]}")
    assert len(set(dictionaries)) == len(rows)
    if field.type.tz == "UTC":
        assert set(flags) == {(8, True), (8, False), (0, True), (0, False)}
    return captures


def check_bad(wire, group, reason):
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert [GZIP["read_group"](parquet, i) for i in range(group)] == UTC_GROUPS[:group]
    try:
        GZIP["read_group"](parquet, group)
    except (pa.ArrowException, OSError) as error:
        assert reason.lower() in str(error).lower(), str(error)
    else:
        raise AssertionError("PyArrow accepted a damaged group")


def rewrite_header(wire, frame, edit):
    offset, header, body, _ = frame
    edited = deepcopy(header)
    edit(edited)
    encoded = THRIFT["encode"](edited)
    assert len(encoded) == body - offset
    return wire[:offset] + encoded + wire[body:]


def retag(wire, frame, tag):
    return rewrite_header(wire, frame, lambda header: header[8][1].update({4: (TType.I32, tag)}))


def fixtures():
    required = [[0 if value is None else value for value in group] for group in (DENSE, LATER)]
    positives = {
        "utc_nanos": (pa.field("ticks", pa.timestamp("ns", "UTC"), nullable=True), UTC_GROUPS, True),
        "local_micros": (pa.field("ticks", pa.timestamp("us"), nullable=False), required, False),
    }
    files, captures = {}, {}
    for name, (field, rows, checksum) in positives.items():
        files[name] = V1["produce"](field, rows, checksum=checksum, page_version="2.0")
        captures[name] = inspect(files[name], field, rows, checksum)

    good = files["utc_nanos"]
    (first_dict, first_pages), (dictionary, pages), (_, tail) = captures["utc_nanos"]
    reference, first_plain, last_plain = pages
    assert [frame[1][8][1][7][1] for frame in pages] == [False, False, True]
    assert all(frame[1][8][1][5][1] > 0 for frame in pages)
    files["bad_reference_outer_crc"], ref_crc = GZIP["corrupt_frame_crc"](good, reference)
    files["bad_plain_outer_crc"], plain_crc = GZIP["corrupt_frame_crc"](good, first_plain)
    files["bad_dictionary_member"] = GZIP["corrupt_member_crc"](good, dictionary)
    files["bad_reference_member"] = V2["corrupt_member_suffix"](good, tail[0])
    files["bad_plain_member"] = V2["corrupt_member_suffix"](good, last_plain)
    files["bad_raw_reference"] = V2["corrupt_raw_suffix"](good, reference)
    files["bad_raw_plain_extent"] = rewrite_header(good, first_plain, lambda header:
        header.update({2: (TType.I32, header[2][1] + 1)}))
    files["two_page_faults"] = V2["corrupt_raw_suffix"](files["bad_plain_member"], reference)
    files["two_group_faults"] = V2["corrupt_raw_suffix"](files["bad_reference_member"], reference)
    for name, group, reason in (
        ("bad_reference_outer_crc", 1, "CRC"), ("bad_plain_outer_crc", 1, "CRC"),
        ("bad_dictionary_member", 1, "gzip"), ("bad_reference_member", 2, "gzip"),
        ("bad_plain_member", 1, "gzip"), ("bad_raw_reference", 1, "bit_width 33"),
        ("two_page_faults", 1, "bit_width 33"), ("two_group_faults", 1, "bit_width 33"),
    ):
        check_bad(files[name], group, reason)

    files["reentry"] = retag(files["bad_plain_outer_crc"], last_plain, 8)
    files["starts_plain"] = retag(good, reference, 0)
    files["no_suffix"] = retag(retag(good, first_plain, 8), last_plain, 8)

    field = positives["utc_nanos"][0]
    files["dictionary_only"] = V2["produce"](field, V2["GROUPS"])
    files["v1"] = V1["produce"](field, UTC_GROUPS)
    v1 = pq.ParquetFile(pa.BufferReader(files["v1"]))
    v1_offset = v1.metadata.row_group(0).column(1).data_page_offset
    return files, positives, [*ref_crc, *plain_crc, dictionary[0], tail[0][0], last_plain[0],
                              first_pages[0][0], first_pages[1][0], first_dict[0], v1_offset]


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, positives, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-gzip-fallback-v2-") as temporary:
        output = Path(temporary)
        for name, wire in files.items():
            (output / (name + ".parquet")).write_bytes(wire)
        for index, group in enumerate(UTC_GROUPS[:2]):
            (output / f"rows-{index}.txt").write_text("\n".join("null" if v is None else str(v) for v in group))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in output.glob("*.arrows")} == set(positives)
        for name, (field, rows, _) in positives.items():
            GZIP["verify_ipc"]((output / (name + ".arrows")).read_bytes(), field, rows)


if __name__ == "__main__":
    main()
