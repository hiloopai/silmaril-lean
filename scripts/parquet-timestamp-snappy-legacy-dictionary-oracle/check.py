"""Check original parquet-java Snappy TIMESTAMP fixtures and native Lean IPC."""

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
DATA = HERE / "fixtures"
SNAPPY_ORACLE = runpy.run_path(str(HERE.parent / "parquet-timestamp-snappy-dictionary-oracle/check.py"))
THRIFT, SNAPPY = SNAPPY_ORACLE["THRIFT"], SNAPPY_ORACLE["SNAPPY"]
MIN, MAX = -(2**63), 2**63 - 1
JAVA = "parquet-mr version 1.16.0 (build 402c3810c372d29603e181771acebfecc71bef61)"


def input_rows(optional):
    pattern = [MIN, -1001, 0, -1001, 0] if optional else [MIN, -1001, 0, MAX, -1001]
    return [None if optional and i % 7 == 0 else pattern[i % len(pattern)] for i in range(4096)]


def read_group(parquet, index):
    return parquet.read_row_group(index).column(0).cast(pa.int64()).to_pylist()


def inspect(wire, optional, field):
    footer_size, = struct.unpack_from("<I", wire, len(wire) - 8)
    footer_start = len(wire) - 8 - footer_size
    memory = TMemoryBuffer(wire[footer_start:-8])
    footer = THRIFT["read_struct"](TCompactProtocol(memory))
    assert memory.cstringio_buf.tell() == footer_size
    _, leaf = THRIFT["list_field"](footer, 2)
    assert leaf[1] == (TType.I32, 2) and leaf[3] == (TType.I32, int(optional))
    timestamp = leaf[10][1][8][1]
    assert timestamp[1] == (TType.BOOL, not optional)
    unit_tag = 2 if optional else 3
    assert timestamp[2][1] == {unit_tag: (TType.STRUCT, {})}
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.metadata.created_by == JAVA
    assert parquet.schema_arrow.field(0).equals(field)
    assert parquet.metadata.num_row_groups > 1
    rows = input_rows(optional)
    groups, captures, start_row = [], [], 0
    for index in range(parquet.metadata.num_row_groups):
        column = parquet.metadata.row_group(index).column(0)
        chunk = THRIFT["column_metadata"](footer, index, 0)
        assert chunk[4] == (TType.I32, 1) and chunk[1] == (TType.I32, 2)
        assert THRIFT["list_field"](chunk, 3) == [b"ticks"]
        assert set(THRIFT["list_field"](chunk, 2)) == ({2, 3, 4} if optional else {2, 4})
        assert chunk[11][1] == column.dictionary_page_offset
        assert chunk[9][1] == column.data_page_offset
        assert chunk[5][1] == column.num_values and chunk[7][1] == column.total_compressed_size
        assert 4 <= chunk[11][1] < chunk[9][1] < chunk[11][1] + chunk[7][1] <= footer_start
        group_rows = rows[start_row:start_row + column.num_values]
        start_row += column.num_values
        assert read_group(parquet, index) == group_rows

        dictionary, *data = SNAPPY_ORACLE["raw_frames"](wire, column)
        assert data and dictionary[0] == column.dictionary_page_offset and data[0][0] == column.data_page_offset
        _, header, _, stored = dictionary
        assert header[1][1] == 2 and header[7][1][2] == (TType.I32, 2)
        entries = list(dict.fromkeys(v for v in group_rows if v is not None))
        assert len(entries) == header[7][1][1][1]
        expanded = SNAPPY.decompress(stored, header[2][1]).to_pybytes()
        assert list(struct.iter_unpack("<q", expanded)) == [(entry,) for entry in entries]
        for _, header, _, stored in (dictionary, *data):
            assert header[3][1] == len(stored)
            assert header[4][1] % 2**32 == zlib.crc32(stored)

        consumed, decoded = 0, []
        for frame in data:
            _, header, _, stored = frame
            assert header[1][1] == 0
            assert [header[5][1][key][1] for key in (2, 3, 4)] == [2, 3 if optional else 4, 4]
            count = header[5][1][1][1]
            expanded = SNAPPY.decompress(stored, header[2][1]).to_pybytes()
            page_rows = group_rows[consumed:consumed + count]
            assert len(page_rows) == count
            mask = [int(value is not None) for value in page_rows]
            prefix = 0
            if optional:
                level_bytes, = struct.unpack_from("<I", expanded)
                prefix = 4 + level_bytes
                assert 4 < prefix < len(expanded)
                assert SNAPPY_ORACLE["hybrid"](expanded[4:prefix], 1, count) == mask
            suffix = expanded[prefix:]
            indices = SNAPPY_ORACLE["hybrid"](suffix[1:], suffix[0], sum(mask))
            assert [entries[i] for i in indices] == [value for value in page_rows if value is not None]
            decoded.append((frame, expanded, prefix, page_rows))
            consumed += count
        assert consumed == len(group_rows)
        groups.append(group_rows)
        captures.append((dictionary, decoded))
    assert start_row == len(rows)
    return groups, captures


def check_late(wire, earlier, message):
    reader = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert [read_group(reader, index) for index in range(len(earlier))] == earlier
    try:
        read_group(reader, len(earlier))
    except (pa.ArrowException, OSError) as error:
        assert message in str(error), str(error)
    else:
        raise AssertionError("PyArrow accepted a damaged later group")


def controls(wire, groups, frames):
    _, late = frames[-1]
    assert len(groups) == 3 and len(late) == 2
    (offset1, header, body1, stored), _, _, _ = late[0]
    bad_crc = wire[:body1] + bytes([stored[0] ^ 1]) + wire[body1 + 1:]
    declared = header[4][1] % 2**32
    changed = zlib.crc32(bad_crc[body1:body1 + len(stored)])
    assert changed != declared
    check_late(bad_crc, groups[:-1], "CRC")

    (offset2, header, body2, stored), expanded, prefix, page_rows = late[1]
    assert page_rows[0] is None and page_rows[1] is not None
    assert expanded[prefix] == 2 and expanded[prefix + 1] == 7
    references = SNAPPY_ORACLE["hybrid"](expanded[prefix + 1:], 2, sum(v is not None for v in page_rows))
    at = prefix + 2
    changed_body = expanded[:at] + bytes([expanded[at] | 3]) + expanded[at + 1:]
    changed_refs = SNAPPY_ORACLE["hybrid"](
        changed_body[prefix + 1:], 2, sum(v is not None for v in page_rows))
    assert changed_refs == [3, *references[1:]] and references[0] < 3
    recompressed = SNAPPY.compress(changed_body).to_pybytes()
    assert len(recompressed) == len(stored)
    rewritten = deepcopy(header)
    crc = zlib.crc32(recompressed)
    rewritten[4] = (TType.I32, (crc + 2**31) % 2**32 - 2**31)
    encoded = THRIFT["encode"](rewritten)
    assert len(encoded) == body2 - offset2
    bad_ref = wire[:offset2] + encoded + recompressed + wire[body2 + len(stored):]
    check_late(bad_ref, groups[:-1], "Unexpected end of stream")

    wrong_level = deepcopy(header)
    wrong_level[5][1][3] = (TType.I32, 4)
    encoded = THRIFT["encode"](wrong_level)
    assert len(encoded) == body2 - offset2
    wrong_level = wire[:offset2] + encoded + wire[body2:]
    return {"bad_crc": bad_crc, "bad_ref": bad_ref, "bad_level_tag": wrong_level}, [
        offset1, declared, changed, offset2,
    ]


def verify_ipc(wire, field, rows):
    source = pa.BufferReader(wire)
    with pa.ipc.open_stream(source) as stream:
        assert stream.schema.equals(pa.schema([field]), check_metadata=True)
        assert [batch.column(0).cast(pa.int64()).to_pylist() for batch in stream] == rows
    assert source.tell() == len(wire) and wire.endswith(struct.pack("<II", 0xFFFFFFFF, 0))
    assert all(msg.metadata_version == pa.ipc.MetadataVersion.V5
               for msg in pa.ipc.MessageReader.open_stream(wire))
    print(f"{field.type}: batches {[len(batch) for batch in rows]}, IPC SHA-256 {sha256(wire).hexdigest()}")


def fixtures():
    positives = {"local_micros": pa.field("ticks", pa.timestamp("us"), nullable=True),
                 "utc_nanos": pa.field("ticks", pa.timestamp("ns", "UTC"), nullable=False)}
    files, observations = {}, {}
    for name, field in positives.items():
        files[name] = (DATA / (name + ".parquet")).read_bytes()
        rows, frames = inspect(files[name], field.nullable, field)
        observations[name] = rows
        if field.nullable:
            damaged, evidence = controls(files[name], rows, frames)
            files.update(damaged)
    return files, positives, observations, evidence


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, positives, observations, evidence = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-snappy-legacy-timestamp-") as temporary:
        output = Path(temporary)
        for name, wire in files.items():
            (output / (name + ".parquet")).write_bytes(wire)
        for index, group in enumerate(observations["local_micros"][:-1]):
            (output / f"prefix-{index}.txt").write_text("\n".join("null" if v is None else str(v) for v in group))
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(output),
                        *map(str, evidence)], cwd=ROOT, check=True)
        assert {file.stem for file in output.glob("*.arrows")} == set(positives)
        for name, field in positives.items():
            verify_ipc((output / (name + ".arrows")).read_bytes(), field, observations[name])


if __name__ == "__main__":
    main()
