"""Pin genuine PyArrow GZIP V1 dictionaries and compare native TIMESTAMP IPC."""

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
ORACLE = runpy.run_path(str(HERE.parent / "parquet-timestamp-snappy-dictionary-oracle/check.py"))
THRIFT = ORACLE["THRIFT"]
MIN, MAX = -(2**63), 2**63 - 1
GROUPS = [[MIN, None, -1, MIN, MAX, -1, 0] * 8,
          [0, -7, None, 0, 8, None] * 4,
          [-2, None, -4, -2, -6, None] * 8]


def produce(field, rows, *, checksum=True, codec="GZIP", page_version="1.0", fallback=False):
    schema = pa.schema([pa.field("decoy", pa.int32(), nullable=False), field])
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=page_version, compression=codec,
                          use_dictionary=["ticks"], write_statistics=False, store_schema=False,
                          write_page_checksum=checksum, write_batch_size=32 if fallback else 16,
                          dictionary_pagesize_limit=8 if fallback else 1024 * 1024,
                          data_page_size=64) as writer:
        for group in rows:
            words = pa.array(group, type=pa.int64()).view(field.type)
            decoy = pa.array(range(len(group)), type=pa.int32())
            writer.write_table(pa.Table.from_arrays([decoy, words], schema=schema))
    return sink.getvalue().to_pybytes()


def read_group(parquet, index):
    return parquet.read_row_group(index, columns=["ticks"], use_threads=False).column(0).cast(pa.int64()).to_pylist()


def member(frame, checksum):
    _, header, _, stored = frame
    assert len(stored) == header[3][1] and stored[:3] == b"\x1f\x8b\x08"
    assert (4 in header) == checksum
    if checksum:
        assert header[4][1] % 2**32 == zlib.crc32(stored)
    decoder = zlib.decompressobj(wbits=31)
    expanded = decoder.decompress(stored) + decoder.flush()
    assert decoder.eof and not decoder.unused_data and not decoder.unconsumed_tail
    assert len(expanded) == header[2][1]
    assert struct.unpack("<II", stored[-8:]) == (zlib.crc32(expanded), len(expanded) % 2**32)
    return expanded


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
    assert parquet.schema_arrow.field(1).equals(field)
    assert parquet.metadata.num_row_groups == len(rows)
    captures, dictionaries = [], []
    for group, expected in enumerate(rows):
        column = parquet.metadata.row_group(group).column(1)
        compact = THRIFT["column_metadata"](footer, group, 1)
        assert compact[1] == (TType.I32, 2) and compact[4] == (TType.I32, 2)
        assert THRIFT["list_field"](compact, 3) == [b"ticks"]
        assert set(THRIFT["list_field"](compact, 2)) == {0, 3, 8}
        assert compact[5][1] == column.num_values == len(expected)
        assert compact[11][1] == column.dictionary_page_offset
        assert compact[9][1] == column.data_page_offset
        assert compact[7][1] == column.total_compressed_size
        assert 4 <= compact[11][1] < compact[9][1] < compact[11][1] + compact[7][1] <= footer_start
        assert read_group(parquet, group) == expected
        dictionary, *pages = ORACLE["raw_frames"](wire, column)
        assert dictionary[0] == column.dictionary_page_offset and pages[0][0] == column.data_page_offset
        assert dictionary[1][1][1] == 2 and dictionary[1][7][1][2] == (TType.I32, 0)
        entries = [value for value, in struct.iter_unpack("<q", member(dictionary, checksum))]
        assert len(entries) == dictionary[1][7][1][1][1]
        assert entries == list(dict.fromkeys(value for value in expected if value is not None))
        dictionaries.append(tuple(entries))
        consumed = 0
        for frame in pages:
            _, header, _, _ = frame
            assert header[1][1] == 0
            assert [header[5][1][i][1] for i in (2, 3, 4)] == [8, 3, 3]
            count = header[5][1][1][1]
            slots = expected[consumed:consumed + count]
            assert len(slots) == count
            expanded = member(frame, checksum)
            mask = [int(value is not None) for value in slots]
            prefix = 0
            if field.nullable:
                length, = struct.unpack_from("<I", expanded)
                prefix = 4 + length
                assert 4 < prefix < len(expanded)
                assert ORACLE["hybrid"](expanded[4:prefix], 1, count) == mask
            else:
                assert all(mask)
            references = expanded[prefix:]
            indices = ORACLE["hybrid"](references[1:], references[0], sum(mask))
            assert [entries[i] for i in indices] == [value for value in slots if value is not None]
            consumed += count
        assert consumed == len(expected)
        captures.append((dictionary, pages))
        print(f"{field.type} group {group}: dictionary at {dictionary[0]}, data frames {[p[0] for p in pages]}")
    assert len(set(dictionaries)) == len(rows)
    return captures


def check_late(wire, message):
    reader = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert [read_group(reader, group) for group in (0, 1)] == GROUPS[:2]
    try:
        read_group(reader, 2)
    except (pa.ArrowException, OSError) as error:
        assert message.lower() in str(error).lower(), str(error)
    else:
        raise AssertionError("PyArrow accepted a damaged GZIP page")


def corrupt_frame_crc(wire, frame):
    offset, header, body, stored = frame
    changed = wire[:body] + bytes([stored[0] ^ 1]) + wire[body + 1:]
    declared, computed = header[4][1] % 2**32, zlib.crc32(changed[body:body + len(stored)])
    assert declared != computed
    return changed, [offset, declared, computed]


def corrupt_member_crc(wire, frame):
    offset, header, body, stored = frame
    changed = stored[:-8] + bytes([stored[-8] ^ 1]) + stored[-7:]
    try:
        zlib.decompress(changed, wbits=31)
    except zlib.error as error:
        assert "incorrect data check" in str(error), str(error)
    else:
        raise AssertionError("zlib accepted the damaged member CRC")
    header = deepcopy(header)
    crc = zlib.crc32(changed)
    header[4] = (TType.I32, (crc + 2**31) % 2**32 - 2**31)
    encoded = THRIFT["encode"](header)
    assert len(encoded) == body - offset
    return wire[:offset] + encoded + changed + wire[body + len(stored):]


def fixtures():
    required = [[v if v is not None else 0 for v in group] for group in GROUPS]
    positives = {
        "utc_nanos": (pa.field("ticks", pa.timestamp("ns", "UTC"), nullable=True), GROUPS, True),
        "local_micros": (pa.field("ticks", pa.timestamp("us"), nullable=False), required, True),
        "outer_crc_absent": (pa.field("ticks", pa.timestamp("ms", "UTC"), nullable=True), GROUPS, False),
    }
    files, captures = {}, {}
    for name, (field, groups, checksum) in positives.items():
        files[name] = produce(field, groups, checksum=checksum)
        captures[name] = inspect(files[name], field, groups, checksum)

    good = files["utc_nanos"]
    dictionary, pages = captures["utc_nanos"][2]
    assert len(pages) >= 2
    early, late = pages[-2:]
    files["bad_page_crc"], evidence = corrupt_frame_crc(good, early)
    files["bad_data_member"] = corrupt_member_crc(good, late)
    files["bad_dict_member"] = corrupt_member_crc(good, dictionary)
    files["double_fault"], _ = corrupt_frame_crc(files["bad_data_member"], early)
    for name in ("bad_page_crc", "double_fault"):
        check_late(files[name], "CRC")
    for name in ("bad_data_member", "bad_dict_member"):
        check_late(files[name], "gzip")

    field = positives["utc_nanos"][0]
    files["v2"] = produce(field, GROUPS, page_version="2.0")
    v2 = pq.ParquetFile(pa.BufferReader(files["v2"]))
    v2_offset = v2.metadata.row_group(0).column(1).data_page_offset
    files["snappy"] = produce(field, GROUPS, codec="SNAPPY")
    fallback = [[MIN, None, MAX, MIN] * 24 + list(range(100))]
    files["fallback"] = produce(field, fallback, fallback=True)
    parquet = pq.ParquetFile(pa.BufferReader(files["fallback"]), page_checksum_verification=True)
    assert read_group(parquet, 0) == fallback[0]
    _, *data = ORACLE["raw_frames"](files["fallback"], parquet.metadata.row_group(0).column(1))
    tags = [frame[1][5][1][2][1] for frame in data]
    assert tags[0] == 8 and 0 in tags
    first_plain = tags.index(0)
    return files, positives, [len(pages) - 1, *evidence, len(pages), late[0], dictionary[0],
                              first_plain + 1, data[first_plain][0], v2_offset]


def verify_ipc(wire, field, rows):
    source = pa.BufferReader(wire)
    with pa.ipc.open_stream(source) as stream:
        assert stream.schema.equals(pa.schema([field]), check_metadata=True)
        assert [batch.column(0).cast(pa.int64()).to_pylist() for batch in stream] == rows
    assert source.tell() == len(wire) and wire.endswith(struct.pack("<II", 0xFFFFFFFF, 0))
    messages = list(pa.ipc.MessageReader.open_stream(wire))
    assert [msg.type for msg in messages] == ["schema"] + ["record batch"] * len(rows)
    assert all(msg.metadata_version == pa.ipc.MetadataVersion.V5 for msg in messages)
    print(f"{field}: batches {[len(batch) for batch in rows]}, IPC SHA-256 {sha256(wire).hexdigest()}")


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, positives, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-gzip-dictionary-v1-") as temporary:
        output = Path(temporary)
        for name, wire in files.items():
            (output / (name + ".parquet")).write_bytes(wire)
        for index, group in enumerate(GROUPS[:2]):
            (output / f"rows-{index}.txt").write_text("\n".join("null" if v is None else str(v) for v in group))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in output.glob("*.arrows")} == set(positives)
        for name, (field, rows, _) in positives.items():
            verify_ipc((output / (name + ".arrows")).read_bytes(), field, rows)


if __name__ == "__main__":
    main()
