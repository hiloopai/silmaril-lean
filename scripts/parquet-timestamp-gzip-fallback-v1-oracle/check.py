"""Pin genuine PyArrow GZIP V1 fallback and compare actual Lean Arrow IPC."""

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

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
GZIP = runpy.run_path(str(HERE.parent / "parquet-timestamp-gzip-dictionary-v1-oracle/check.py"))
FALLBACK = runpy.run_path(str(HERE.parent / "parquet-timestamp-snappy-fallback-oracle/check.py"))
ORACLE, THRIFT = GZIP["ORACLE"], GZIP["THRIFT"]
GROUPS, BATCH = FALLBACK["groups"](), FALLBACK["BATCH"]


def produce(field, groups, *, checksum=True, page_version="1.0"):
    schema = pa.schema([pa.field("decoy", pa.int32(), nullable=False), field])
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=page_version, compression="GZIP",
                          use_dictionary=["ticks"], write_statistics=False, store_schema=False,
                          write_page_checksum=checksum, dictionary_pagesize_limit=8, write_batch_size=BATCH,
                          data_page_size=24) as writer:
        for group in groups:
            ticks = pa.array(group, type=pa.int64()).view(field.type)
            writer.write_table(pa.Table.from_arrays([pa.array(range(len(group)), type=pa.int32()), ticks],
                                                    schema=schema))
    return sink.getvalue().to_pybytes()


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
    captures, dictionaries = [], []
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
            _, header, _, _ = frame
            assert header[1][1] == 0 and [header[5][1][key][1] for key in (3, 4)] == [3, 3]
            count, tag = [header[5][1][i][1] for i in (1, 2)]
            slots = expected[cursor:cursor + count]
            assert len(slots) == count
            cursor += count
            expanded = GZIP["member"](frame, checksum)
            mask = [int(value is not None) for value in slots]
            prefix = 0
            if field.nullable:
                length, = struct.unpack_from("<I", expanded)
                prefix = 4 + length
                assert 4 < prefix < len(expanded)
                assert ORACLE["hybrid"](expanded[4:prefix], 1, count) == mask
            else:
                assert all(mask)
            suffix = expanded[prefix:]
            present = [value for value in slots if value is not None]
            if tag == 8:
                refs = ORACLE["hybrid"](suffix[1:], suffix[0], sum(mask))
                assert [entries[i] for i in refs] == present
                referenced.extend(present)
            else:
                assert tag == 0
                assert [word for word, in struct.iter_unpack("<q", suffix)] == present
            tags.append(tag)
        assert cursor == len(expected) and tags == [8, 0, 0]
        assert entries == list(dict.fromkeys(referenced))
        captures.append((dictionary, pages))
        print(f"{field.type} group {group}: dictionary {dictionary[0]}, pages {tags}, transition {pages[1][0]}")
    assert len(set(dictionaries)) == len(rows)
    return captures


def check_bad(wire, reason):
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert GZIP["read_group"](parquet, 0) == GROUPS[0]
    try:
        GZIP["read_group"](parquet, 1)
    except (pa.ArrowException, OSError) as error:
        assert reason.lower() in str(error).lower(), str(error)
    else:
        raise AssertionError("PyArrow accepted a damaged late group")


def retag(wire, frame, tag):
    offset, header, body, _ = frame
    edited = deepcopy(header)
    edited[5][1][2] = (TType.I32, tag)
    encoded = THRIFT["encode"](edited)
    assert len(encoded) == body - offset
    return wire[:offset] + encoded + wire[body:]


def fixtures():
    required = [[value if value is not None else 0 for value in group] for group in GROUPS]
    positives = {
        "utc_nanos": (pa.field("ticks", pa.timestamp("ns", "UTC"), nullable=True), GROUPS, True),
        "local_micros": (pa.field("ticks", pa.timestamp("us"), nullable=True), GROUPS, True),
        "local_millis_raw_crc_absent": (pa.field("ticks", pa.timestamp("ms"), nullable=False), required, False),
    }
    files, captures = {}, {}
    for name, (field, rows, checksum) in positives.items():
        files[name] = produce(field, rows, checksum=checksum)
        captures[name] = inspect(files[name], field, rows, checksum)

    good = files["utc_nanos"]
    (first_dict, first_pages), (dictionary, pages) = captures["utc_nanos"]
    reference, first_plain, last_plain = pages
    files["bad_outer_crc"], outer = GZIP["corrupt_frame_crc"](good, first_plain)
    for name, frame in (("bad_dict_member", dictionary), ("bad_reference_member", reference),
                        ("bad_plain_member", last_plain)):
        files[name] = GZIP["corrupt_member_crc"](good, frame)
        check_bad(files[name], "gzip")
    files["double_fault"], _ = GZIP["corrupt_frame_crc"](files["bad_plain_member"], first_plain)
    for name in ("bad_outer_crc", "double_fault"):
        check_bad(files[name], "CRC")

    files["reentry"] = retag(files["bad_outer_crc"], last_plain, 8)
    files["starts_plain"] = retag(good, reference, 0)
    files["no_suffix"] = retag(retag(good, first_plain, 8), last_plain, 8)

    field = positives["utc_nanos"][0]
    files["dictionary_only"] = GZIP["produce"](field, GZIP["GROUPS"])
    files["v2"] = produce(field, GROUPS, page_version="2.0")
    v2 = pq.ParquetFile(pa.BufferReader(files["v2"]))
    offset_v2 = v2.metadata.row_group(0).column(1).data_page_offset
    return files, positives, [*outer, dictionary[0], reference[0], last_plain[0], first_pages[1][0],
                              first_dict[0], offset_v2]


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, positives, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-gzip-fallback-") as temporary:
        output = Path(temporary)
        for name, wire in files.items():
            (output / (name + ".parquet")).write_bytes(wire)
        (output / "expected.txt").write_text("\n".join("null" if value is None else str(value) for value in GROUPS[0]))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in output.glob("*.arrows")} == set(positives)
        for name, (field, rows, _) in positives.items():
            GZIP["verify_ipc"]((output / (name + ".arrows")).read_bytes(), field, rows)


if __name__ == "__main__":
    main()
