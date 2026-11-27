"""Verify genuine parquet-java Snappy V1 fallback and exact native IPC."""

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
THRIFT, SNAPPY = ORACLE["THRIFT"], ORACLE["SNAPPY"]
MIN, MAX = -(2**63), 2**63 - 1
ROWS = 384
FIELDS = (pa.field("local_ticks", pa.timestamp("us"), nullable=True),
          pa.field("utc_ticks", pa.timestamp("ns", "UTC"), nullable=False))


def counts(group, column):
    rows = []
    for slot in range(ROWS):
        value = (-1_000_000 * (group + 1) + 113 * slot if 224 <= slot < 320
                 else [MIN, -1001, 0, MAX][slot % 4] ^ group)
        if column:
            rows.append(~value)
        elif (slot + group) % 13 == 5:
            rows.append(None)
        else:
            rows.append(value)
    return rows


def read_group(parquet, group, column):
    field = FIELDS[column].name
    return parquet.read_row_group(group, columns=[field]).column(0).cast(pa.int64()).to_pylist()


def inspect(wire):
    footer_bytes, = struct.unpack_from("<I", wire, len(wire) - 8)
    footer_start = len(wire) - 8 - footer_bytes
    transport = TMemoryBuffer(wire[footer_start:-8])
    footer = THRIFT["read_struct"](TCompactProtocol(transport))
    assert transport.cstringio_buf.tell() == footer_bytes
    _, *leaves = THRIFT["list_field"](footer, 2)
    for column, (leaf, field) in enumerate(zip(leaves, FIELDS, strict=True)):
        assert leaf[1] == (TType.I32, 2) and leaf[3] == (TType.I32, int(field.nullable))
        timestamp = leaf[10][1][8][1]
        assert timestamp[1] == (TType.BOOL, bool(column))
        assert timestamp[2][1] == {2 + column: (TType.STRUCT, {})}

    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.metadata.created_by == "parquet-mr version 1.16.0 (build 402c3810c372d29603e181771acebfecc71bef61)"
    assert parquet.metadata.num_row_groups == 2
    assert list(parquet.schema_arrow) == list(FIELDS)
    captures = {}
    for group in range(2):
        for column, field in enumerate(FIELDS):
            rows = counts(group, column)
            assert read_group(parquet, group, column) == rows
            metadata = parquet.metadata.row_group(group).column(column)
            compact = THRIFT["column_metadata"](footer, group, column)
            assert compact[1] == (TType.I32, 2) and compact[4] == (TType.I32, 1)
            assert THRIFT["list_field"](compact, 3) == [field.name.encode()]
            assert set(THRIFT["list_field"](compact, 2)) == ({0, 2, 3, 4} if field.nullable else {0, 2, 4})
            assert compact[5][1] == metadata.num_values == len(rows)
            assert compact[11][1] == metadata.dictionary_page_offset
            assert compact[9][1] == metadata.data_page_offset
            assert compact[7][1] == metadata.total_compressed_size
            assert 4 <= compact[11][1] < compact[9][1] < compact[11][1] + compact[7][1] <= footer_start

            dictionary, *pages = ORACLE["raw_frames"](wire, metadata)
            for _, header, _, stored in (dictionary, *pages):
                assert header[3][1] == len(stored) and header[4][1] % 2**32 == zlib.crc32(stored)
            assert dictionary[0] == metadata.dictionary_page_offset and pages[0][0] == metadata.data_page_offset
            _, header, _, stored = dictionary
            assert header[1][1] == 2 and header[7][1][2] == (TType.I32, 2)
            entries = [word for word, in struct.iter_unpack("<q", SNAPPY.decompress(stored, header[2][1]))]
            assert len(entries) == header[7][1][1][1]

            tagged, tags, observed_dictionary, cursor = [], [], [], 0
            for ordinal, frame in enumerate(pages, 1):
                offset, header, _, stored = frame
                assert header[1][1] == 0
                info = header[5][1]
                count, tag = info[1][1], info[2][1]
                assert [info[3][1], info[4][1]] == [3 if field.nullable else 4, 4]
                raw = SNAPPY.decompress(stored, header[2][1]).to_pybytes()
                slots = rows[cursor:cursor + count]
                assert len(raw) == header[2][1] and len(slots) == count
                cursor += count
                mask = [int(v is not None) for v in slots]
                prefix = 0
                if field.nullable:
                    definition_bytes, = struct.unpack_from("<I", raw)
                    prefix = 4 + definition_bytes
                    assert 4 < prefix < len(raw)
                    assert ORACLE["hybrid"](raw[4:prefix], 1, count) == mask
                suffix = raw[prefix:]
                present = [v for v in slots if v is not None]
                if tag == 2:
                    indices = ORACLE["hybrid"](suffix[1:], suffix[0], sum(mask))
                    assert [entries[i] for i in indices] == present
                    observed_dictionary.extend(present)
                else:
                    assert tag == 0
                    assert list(struct.iter_unpack("<q", suffix)) == [(v,) for v in present]
                tagged.append((ordinal, frame))
                tags.append(tag)
            assert cursor == len(rows) and tags == [2] * 5 + [0] * 5
            assert entries == list(dict.fromkeys(observed_dictionary))
            captures[group, column] = (dictionary, tagged)
            print(f"group {group} {field.name}: frames {tags}, transition at {tagged[5][1][0]}")
    return captures


def bad_crc(wire, frame):
    offset, header, body, stored = frame
    changed = wire[:body] + bytes([stored[0] ^ 1]) + wire[body + 1:]
    declared, actual = header[4][1] % 2**32, zlib.crc32(changed[body:body + len(stored)])
    assert declared != actual
    parquet = pq.ParquetFile(pa.BufferReader(changed), page_checksum_verification=True)
    assert read_group(parquet, 0, 0) == counts(0, 0)
    assert read_group(parquet, 1, 1) == counts(1, 1)
    try:
        read_group(parquet, 1, 0)
    except (pa.ArrowException, OSError) as error:
        assert "CRC" in str(error), str(error)
    else:
        raise AssertionError("PyArrow accepted a damaged stored payload")
    return changed, [offset, declared, actual]


def retag(wire, frame, tag):
    offset, header, body, _ = frame
    edited = deepcopy(header)
    edited[5][1][2] = (TType.I32, tag)
    encoded = THRIFT["encode"](edited)
    assert len(encoded) == body - offset
    return wire[:offset] + encoded + wire[body:]


def fixtures():
    good = (HERE / "fixtures/fallback.parquet").read_bytes()
    dictionary, pages = inspect(good)[1, 0]
    reference_pages, plain_pages = pages[:5], pages[5:]
    plain_ordinal, plain = plain_pages[0]
    bad_plain, plain_evidence = bad_crc(good, plain)
    bad_dictionary, dictionary_evidence = bad_crc(good, dictionary)
    reentry_ordinal, reentry = plain_pages[1]
    # Leave the bad CRC in the first PLAIN page to test phase admission precedence.
    reentered = retag(bad_plain, reentry, 2)
    no_fallback = good
    for _, frame in plain_pages:
        no_fallback = retag(no_fallback, frame, 2)
    _, first = reference_pages[0]
    starts_plain = retag(good, first, 0)
    return {"fallback": good, "bad_plain": bad_plain, "bad_dictionary": bad_dictionary,
            "reentered": reentered, "no_fallback": no_fallback, "starts_plain": starts_plain}, [
        plain_ordinal, *plain_evidence, *dictionary_evidence, reentry_ordinal, reentry[0], first[0],
    ]


def verify_ipc(wire, column):
    source = pa.BufferReader(wire)
    with pa.ipc.open_stream(source) as stream:
        assert stream.schema.equals(pa.schema([FIELDS[column]]), check_metadata=True)
        assert [batch.column(0).cast(pa.int64()).to_pylist() for batch in stream] == [
            counts(0, column), counts(1, column)]
    assert source.tell() == len(wire) and wire.endswith(struct.pack("<II", 0xFFFFFFFF, 0))
    messages = list(pa.ipc.MessageReader.open_stream(wire))
    assert [msg.type for msg in messages] == ["schema", "record batch", "record batch"]
    assert all(msg.metadata_version == pa.ipc.MetadataVersion.V5 for msg in messages)
    print(f"{FIELDS[column]}: batches [384, 384], IPC SHA-256 {sha256(wire).hexdigest()}")


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-snappy-legacy-fallback-") as temporary:
        output = Path(temporary)
        for name, wire in files.items():
            (output / (name + ".parquet")).write_bytes(wire)
        (output / "prefix.txt").write_text("\n".join("null" if v is None else str(v) for v in counts(0, 0)))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output),
                        *map(str, evidence)], cwd=ROOT, check=True)
        for column, field in enumerate(FIELDS):
            verify_ipc((output / (field.name + ".arrows")).read_bytes(), column)


if __name__ == "__main__":
    main()
