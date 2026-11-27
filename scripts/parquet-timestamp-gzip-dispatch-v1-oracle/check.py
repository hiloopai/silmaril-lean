"""Check genuine mixed GZIP V1 TIMESTAMP groups and native Arrow IPC."""

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
FALLBACK = runpy.run_path(str(HERE.parent / "parquet-timestamp-gzip-fallback-v1-oracle/check.py"))
GZIP, THRIFT, ORACLE = FALLBACK["GZIP"], FALLBACK["THRIFT"], FALLBACK["ORACLE"]
MIN, MAX = -(2**63), 2**63 - 1


def rows(nullable):
    return [
        [MIN, None if nullable else MIN, MIN, MIN] * 128,
        [value if value is not None or nullable else 0 for value in FALLBACK["GROUPS"][0]],
        [None if nullable else MAX, MAX, MAX, MAX] * 128,
    ]


def produce(field, groups, *, checksum, page_version="1.0"):
    schema = pa.schema([pa.field("decoy", pa.int32(), nullable=False), field])
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=page_version, compression="GZIP",
                          use_dictionary=["ticks"], write_statistics=False, store_schema=False,
                          write_page_checksum=checksum, dictionary_pagesize_limit=16,
                          write_batch_size=256, data_page_size=24) as writer:
        for group in groups:
            ticks = pa.array(group, type=pa.int64()).view(field.type)
            decoy = pa.array(range(len(group)), type=pa.int32())
            writer.write_table(pa.Table.from_arrays([decoy, ticks], schema=schema))
    return sink.getvalue().to_pybytes()


def inspect(wire, field, groups, checksum):
    footer_size, = struct.unpack_from("<I", wire, len(wire) - 8)
    footer_start = len(wire) - 8 - footer_size
    memory = TMemoryBuffer(wire[footer_start:-8])
    footer = THRIFT["read_struct"](TCompactProtocol(memory))
    assert memory.cstringio_buf.tell() == footer_size
    _, _, leaf = THRIFT["list_field"](footer, 2)
    assert leaf[1] == (TType.I32, 2) and leaf[3] == (TType.I32, int(field.nullable))
    stamp = leaf[10][1][8][1]
    assert stamp[1] == (TType.BOOL, field.type.tz == "UTC")
    assert stamp[2][1] == {{"us": 2, "ns": 3}[field.type.unit]: (TType.STRUCT, {})}

    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.schema_arrow.field(1).equals(field) and parquet.metadata.num_row_groups == len(groups)
    captures, dictionaries = [], []
    for group, expected in enumerate(groups):
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
            assert header[1][1] == 0 and [header[5][1][i][1] for i in (3, 4)] == [3, 3]
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
            suffix, present = expanded[prefix:], [value for value in slots if value is not None]
            if tag == 8:
                indices = ORACLE["hybrid"](suffix[1:], suffix[0], sum(mask))
                assert [entries[i] for i in indices] == present
                referenced.extend(present)
            else:
                assert tag == 0
                assert [word for word, in struct.iter_unpack("<q", suffix)] == present
            tags.append(tag)
        assert cursor == len(expected) and tags == ([8, 0, 0] if group == 1 else [8, 8])
        assert entries == list(dict.fromkeys(referenced))
        captures.append((dictionary, pages))
        print(f"{field.type} group {group}: tags {tags}, data offsets {[frame[0] for frame in pages]}")
    assert len(set(dictionaries)) == len(groups)
    return captures


def check_bad(wire, group, message):
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert [GZIP["read_group"](parquet, index) for index in range(group)] == rows(True)[:group]
    try:
        GZIP["read_group"](parquet, group)
    except (pa.ArrowException, OSError) as error:
        assert message.lower() in str(error).lower(), str(error)
    else:
        raise AssertionError("PyArrow accepted a damaged group")


def fixtures():
    admitted = {
        "utc_nanos": (pa.field("ticks", pa.timestamp("ns", "UTC"), nullable=True), True),
        "local_micros": (pa.field("ticks", pa.timestamp("us"), nullable=False), False),
    }
    files, frames = {}, {}
    for name, (field, checksum) in admitted.items():
        groups = rows(field.nullable)
        files[name] = produce(field, groups, checksum=checksum)
        frames[name] = inspect(files[name], field, groups, checksum)

    good = files["utc_nanos"]
    (_, _), (_, fallback), (dictionary, last) = frames["utc_nanos"]
    first_ref, first_plain, final_plain = fallback
    files["mutated_fallback_outer"], outer = GZIP["corrupt_frame_crc"](good, first_plain)
    for name, frame, group in (
        ("mutated_fallback_member", final_plain, 1),
        ("mutated_dictionary_member", dictionary, 2),
        ("mutated_reference_member", last[-1], 2),
    ):
        files[name] = GZIP["corrupt_member_crc"](good, frame)
        check_bad(files[name], group, "gzip")
    files["mutated_two_failures"], _ = GZIP["corrupt_frame_crc"](files["mutated_dictionary_member"], first_plain)
    for name in ("mutated_fallback_outer", "mutated_two_failures"):
        check_bad(files[name], 1, "CRC")
    files["mutated_reentry"] = FALLBACK["retag"](files["mutated_fallback_outer"], final_plain, 8)
    files["mutated_missing_prefix"] = FALLBACK["retag"](good, first_ref, 0)

    def update_offset(footer):
        column = THRIFT["column_metadata"](footer, 2, 1)
        column[9] = (TType.I64, last[0][0] + 1)

    files["mutated_data_offset"] = THRIFT["rewrite_footer"](good, update_offset)
    field = admitted["utc_nanos"][0]
    files["v2"] = produce(field, rows(True), checksum=True, page_version="2.0")
    v2 = pq.ParquetFile(pa.BufferReader(files["v2"]))
    v2_offset = v2.metadata.row_group(0).column(1).data_page_offset
    return files, admitted, [*outer, final_plain[0], dictionary[0], last[-1][0], first_ref[0], last[0][0], v2_offset]


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, admitted, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-gzip-dispatch-") as temporary:
        output = Path(temporary)
        for name, wire in files.items():
            (output / (name + ".parquet")).write_bytes(wire)
        for index, group in enumerate(rows(True)):
            (output / f"expected-{index}.txt").write_text(
                "\n".join("null" if value is None else str(value) for value in group))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in output.glob("*.arrows")} == set(admitted)
        for name, (field, _) in admitted.items():
            GZIP["verify_ipc"]((output / (name + ".arrows")).read_bytes(), field, rows(field.nullable))


if __name__ == "__main__":
    main()
