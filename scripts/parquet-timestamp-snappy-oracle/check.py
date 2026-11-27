"""Read actual Snappy TIMESTAMP pages and native Arrow IPC with pinned PyArrow."""

from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
import platform
import random
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
THRIFT = runpy.run_path(str(ROOT / "tests/formats/parquet-timestamp-leaf/check-fixtures.py"))
SNAPPY = pa.Codec("snappy")
EOS = struct.pack("<II", 0xFFFFFFFF, 0)
MIN, MAX = -(2**63), 2**63 - 1


def groups():
    random_bits = random.Random(1729)
    first = [None if i % 7 == 2 else random_bits.getrandbits(64) + MIN for i in range(32)]
    first[:2] = MIN, MAX
    return [first, [None] * 32, [-1001, None, 0, -1001] * 8]


def produce(unit, zone, page_version, rows, *, checksum=False, nullable=True, codec="SNAPPY"):
    typ = pa.timestamp(unit, zone)
    schema = pa.schema([pa.field("event_time", typ, nullable=nullable)])
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=page_version,
                          compression=codec, column_encoding="PLAIN", use_dictionary=False,
                          store_schema=False, write_statistics=False, write_page_checksum=checksum,
                          write_batch_size=16, data_page_size=1) as writer:
        for group in rows:
            values = pa.array(group, type=pa.int64()).view(typ)
            writer.write_table(pa.Table.from_arrays([values], schema=schema))
    return sink.getvalue().to_pybytes()


def footer_start(wire):
    size, = struct.unpack_from("<I", wire, len(wire) - 8)
    return len(wire) - 8 - size


def converted_micros(wire):
    def edit(metadata):
        leaf = THRIFT["list_field"](metadata, 2)[1]
        assert leaf[1] == (TType.I32, 2) and leaf[6] == (TType.I32, 10)
        assert leaf[10][1][8][1][1] == (TType.BOOL, True)
        del leaf[10]

    converted = THRIFT["rewrite_footer"](wire, edit)
    assert converted[:footer_start(converted)] == wire[:footer_start(wire)]
    return converted


def inspect_frames(wire, page_version, expected):
    parquet = pq.ParquetFile(pa.BufferReader(wire))
    assert parquet.metadata.num_row_groups == len(expected)
    flags, damaged = set(), None
    for group_index, rows in enumerate(expected):
        column = parquet.metadata.row_group(group_index).column(0)
        assert column.compression == "SNAPPY" and not column.has_dictionary_page
        assert column.num_values == len(rows)
        cursor = column.data_page_offset
        stop = cursor + column.total_compressed_size
        assert 4 <= cursor < stop <= footer_start(wire)
        row, page_index = 0, 0
        while cursor < stop:
            memory = TMemoryBuffer(wire[cursor:stop])
            header = THRIFT["read_struct"](TCompactProtocol(memory))
            body = cursor + memory.cstringio_buf.tell()
            expanded, compressed = header[2][1], header[3][1]
            end = body + compressed
            assert cursor < body <= end <= stop and 4 not in header
            if page_version == "1.0":
                assert header[1][1] == 0
                page = header[5][1]
                assert [page[i][1] for i in (2, 3, 4)] == [0, 3, 3]
                is_compressed, start, target = True, body, expanded
                raw = SNAPPY.decompress(wire[start:end], target).to_pybytes()
                level_size, = struct.unpack_from("<I", raw)
                assert level_size > 0
                plain = raw[4 + level_size:]
            else:
                assert header[1][1] == 3
                page = header[8][1]
                assert page[3][1] == page[1][1] and page[4][1] == page[6][1] == 0
                is_compressed = page.get(7, (TType.BOOL, True))[1]
                level_size = page[5][1]
                assert 0 < level_size <= min(compressed, expanded)
                start, target = body + level_size, expanded - level_size
                if is_compressed:
                    plain = SNAPPY.decompress(wire[start:end], target).to_pybytes()
                else:
                    assert end - start == target
                    plain = wire[start:end]
            slots = page[1][1]
            logical = rows[row:row + slots]
            assert len(logical) == slots
            present = [slot for slot in logical if slot is not None]
            assert list(struct.iter_unpack("<q", plain)) == [(slot,) for slot in present]
            if page_version == "2.0":
                assert page[2][1] == slots - len(present)
            if group_index == 2 and page_index == 1:
                assert is_compressed and 0 < target < 126 and wire[start] == target
                damaged = start
            flags.add(is_compressed)
            row += slots
            cursor = end
            page_index += 1
        assert cursor == stop and row == len(rows)
    assert flags == ({True} if page_version == "1.0" else {False, True})
    assert damaged is not None
    return damaged


def corrupt(wire, offset, expected):
    changed = bytearray(wire)
    changed[offset] += 1
    changed = bytes(changed)
    parquet = pq.ParquetFile(pa.BufferReader(changed))
    assert [read_group(parquet, index) for index in (0, 1)] == expected[:2]
    try:
        read_group(parquet, 2)
    except (OSError, pa.ArrowInvalid) as error:
        assert "Output buffer size" in str(error)
    else:
        raise AssertionError("PyArrow accepted the late overdeclared Snappy size")
    return changed


def fixtures():
    rows = groups()
    v1 = produce("ms", "UTC", "1.0", rows)
    v2 = produce("us", None, "2.0", rows)
    legacy = converted_micros(produce("us", "UTC", "2.0", rows))
    bad_v1 = corrupt(v1, inspect_frames(v1, "1.0", rows), rows)
    inspect_frames(v2, "2.0", rows)
    bad_v2 = corrupt(legacy, inspect_frames(legacy, "2.0", rows), rows)
    return {"modern_v1": v1, "modern_v2": v2, "legacy_v2": legacy,
            "bad_v1": bad_v1, "bad_v2": bad_v2}, rows


def read_group(parquet, index):
    return parquet.read_row_group(index).column(0).cast(pa.int64()).to_pylist()


def verify_ipc(name, parquet_wire, output, rows, typ, *, nullable=True):
    parquet = pq.ParquetFile(pa.BufferReader(parquet_wire))
    field = pa.field("event_time", typ, nullable=nullable)
    assert parquet.schema.column(0).physical_type == "INT64"
    assert parquet.schema_arrow.field(0).equals(field)
    assert [read_group(parquet, i) for i in range(parquet.metadata.num_row_groups)] == rows
    source = pa.BufferReader(output)
    with pa.ipc.open_stream(source) as stream:
        assert stream.schema.equals(pa.schema([field]), check_metadata=True)
        assert [batch.column(0).cast(pa.int64()).to_pylist() for batch in stream] == rows
    assert source.tell() == len(output) and output.endswith(EOS)
    messages = list(pa.ipc.MessageReader.open_stream(output))
    assert [message.type for message in messages] == ["schema"] + ["record batch"] * len(rows)
    assert all(message.metadata_version == pa.ipc.MetadataVersion.V5 for message in messages)
    print(f"{name}: exact {typ}, rows {[len(group) for group in rows]}, SHA-256 {sha256(output).hexdigest()}")


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, rows = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-snappy-") as temporary:
        directory = Path(temporary)
        for name, wire in files.items():
            (directory / (name + ".parquet")).write_bytes(wire)
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(directory)],
                       cwd=ROOT, check=True)
        admitted = {"modern_v1": pa.timestamp("ms", "UTC"), "modern_v2": pa.timestamp("us"),
                    "legacy_v2": pa.timestamp("us", "UTC")}
        assert {file.stem for file in directory.glob("*.arrows")} == set(admitted)
        for name, typ in admitted.items():
            verify_ipc(name, files[name], (directory / (name + ".arrows")).read_bytes(), rows, typ)


if __name__ == "__main__":
    main()
