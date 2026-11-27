"""Pin PyArrow INT64 TIMESTAMP dictionaries and verify the actual Lean IPC."""

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
THRIFT = runpy.run_path(str(ROOT / "tests/formats/parquet-timestamp-leaf/check-fixtures.py"))
MIN, MAX = -(2**63), 2**63 - 1
GROUPS = [[MIN, None, -1, MIN, MAX, -1], [0, -7, None, 0, 8, None], [-2, None, -4, -2, -6, None]]
EOS = struct.pack("<II", 0xFFFFFFFF, 0)


def produce(unit, zone, page_version, *, codec="NONE", fallback=False, groups=None,
            checksum=False, fallback_batch_size=4):
    tick_type = pa.timestamp(unit, zone)
    schema = pa.schema([pa.field("decoy", pa.int32(), nullable=False), pa.field("ticks", tick_type)])
    sink = pa.BufferOutputStream()
    fallback_options = {}
    if fallback:
        fallback_options = dict(dictionary_pagesize_limit=8, write_batch_size=fallback_batch_size, data_page_size=24)
    with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=page_version, compression=codec,
                          use_dictionary=["ticks"], write_statistics=False, store_schema=False, write_page_checksum=checksum,
                          **fallback_options) as writer:
        if groups is None:
            groups = [list(range(24))] if fallback else GROUPS
        for group in groups:
            values = pa.array(group, type=pa.int64()).view(tick_type)
            writer.write_table(pa.Table.from_arrays([pa.array(range(len(group)), type=pa.int32()), values],
                                                    schema=schema))
    return sink.getvalue().to_pybytes()


def frames(wire, column):
    start = column.dictionary_page_offset
    memory = TMemoryBuffer(wire[start:start + column.total_compressed_size])
    protocol = TCompactProtocol(memory)
    while memory.cstringio_buf.tell() < column.total_compressed_size:
        header_start = start + memory.cstringio_buf.tell()
        header = THRIFT["read_struct"](protocol)
        body_start = start + memory.cstringio_buf.tell()
        assert header[2][1] == header[3][1] and 4 not in header
        yield header_start, header, body_start, memory.readAll(header[3][1])
    assert memory.cstringio_buf.tell() == column.total_compressed_size


def read_group(parquet, index):
    return parquet.read_row_group(index, columns=["ticks"], use_threads=False).column(0).cast(pa.int64()).to_pylist()


def inspect(wire, page_version):
    parquet = pq.ParquetFile(pa.BufferReader(wire))
    assert parquet.schema.column(0).physical_type == "INT32"
    assert parquet.schema.column(1).physical_type == "INT64"
    assert [read_group(parquet, i) for i in range(parquet.metadata.num_row_groups)] == GROUPS
    pages = []
    dictionaries = set()
    for index, rows in enumerate(GROUPS):
        column = parquet.metadata.row_group(index).column(1)
        assert column.compression == "UNCOMPRESSED" and column.encodings == ("PLAIN", "RLE", "RLE_DICTIONARY")
        dictionary, data = list(frames(wire, column))
        start, header, _, body = dictionary
        words = list(dict.fromkeys(value for value in rows if value is not None))
        assert start == column.dictionary_page_offset and header[1][1] == 2
        assert [header[7][1][i][1] for i in (1, 2)] == [len(words), 0]
        assert list(struct.iter_unpack("<q", body)) == [(word,) for word in words]
        dictionaries.add(tuple(words))

        data_start, header, body_start, body = data
        assert data_start == column.data_page_offset
        if page_version == "1.0":
            assert header[1][1] == 0
            assert [header[5][1][i][1] for i in (1, 2, 3, 4)] == [len(rows), 8, 3, 3]
            level_start, level_stop = 4, 4 + struct.unpack_from("<I", body)[0]
        else:
            assert header[1][1] == 3
            info = header[8][1]
            assert [info[i][1] for i in (1, 2, 3, 4, 6)] == [len(rows), rows.count(None), len(rows), 8, 0]
            assert info[7] == (TType.BOOL, False)
            level_start, level_stop = 0, info[5][1]
        levels = body[level_start:level_stop]
        assert len(levels) == 2 and levels[0] == 3
        assert [(levels[1] >> slot) & 1 for slot in range(len(rows))] == [int(x is not None) for x in rows]
        indices = body[level_stop:]
        assert len(indices) == 4 and indices[:2] == b"\x02\x03"
        packed = int.from_bytes(indices[2:], "little")
        assert [(packed >> (2 * i)) & 3 for i in range(sum(x is not None for x in rows))] == [
            words.index(x) for x in rows if x is not None
        ]
        pages.append((data_start, body_start + level_stop + 2))
    assert len(dictionaries) == len(GROUPS)
    return pages


def legacy_micros(wire):
    def edit(metadata):
        leaf = THRIFT["list_field"](metadata, 2)[2]
        assert leaf[6] == (TType.I32, 10) and leaf[10][1][8][1][1] == (TType.BOOL, True)
        del leaf[10]

    converted = THRIFT["rewrite_footer"](wire, edit)
    original_payload = len(wire) - 8 - struct.unpack_from("<I", wire, len(wire) - 8)[0]
    assert converted[:original_payload] == wire[:original_payload]
    return converted


def fixtures():
    v1 = produce("ns", "UTC", "1.0")
    v2 = produce("us", None, "2.0")
    legacy = legacy_micros(produce("us", "UTC", "2.0"))
    inspect(v1, "1.0")
    inspect(v2, "2.0")
    bad_header, bad_indices = inspect(legacy, "2.0")[2]
    # The first reference is zero. Turn it into the first absent dictionary index.
    assert legacy[bad_indices] & 3 == 0
    bad = legacy[:bad_indices] + bytes([legacy[bad_indices] | 3]) + legacy[bad_indices + 1:]
    broken = pq.ParquetFile(pa.BufferReader(bad))
    assert [read_group(broken, i) for i in (0, 1)] == GROUPS[:2]
    try:
        read_group(broken, 2)
    except (pa.ArrowException, OSError):
        pass
    else:
        raise AssertionError("PyArrow admitted an out-of-range dictionary reference")

    fallback = produce("us", None, "2.0", fallback=True)
    column = pq.ParquetFile(pa.BufferReader(fallback)).metadata.row_group(0).column(1)
    fallback_pages = list(frames(fallback, column))
    assert fallback_pages[0][1][1][1] == 2
    first_plain = next((i, page[0]) for i, page in enumerate(fallback_pages[1:], 1)
                       if page[1][8][1][4][1] == 0)
    snappy = produce("us", None, "2.0", codec="SNAPPY")
    return {"v1": v1, "v2": v2, "legacy": legacy, "bad": bad,
            "fallback": fallback, "snappy": snappy}, [bad_header, *first_plain]


def verify_ipc(name, parquet_wire, output, unit, zone):
    expected = pa.field("ticks", pa.timestamp(unit, zone), nullable=True)
    assert pq.ParquetFile(pa.BufferReader(parquet_wire)).schema_arrow.field(1).equals(expected)
    source = pa.BufferReader(output)
    with pa.ipc.open_stream(source) as stream:
        assert stream.schema.equals(pa.schema([expected]), check_metadata=True)
        assert [batch.column(0).cast(pa.int64()).to_pylist() for batch in stream] == GROUPS
    assert source.tell() == len(output) and output.endswith(EOS)
    messages = list(pa.ipc.MessageReader.open_stream(output))
    assert [message.type for message in messages] == ["schema"] + ["record batch"] * len(GROUPS)
    assert all(message.metadata_version == pa.ipc.MetadataVersion.V5 for message in messages)
    print(f"{name}: exact {expected.type}, {len(GROUPS)} batches, IPC SHA-256 {sha256(output).hexdigest()}")


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, offsets = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    print(f"Corrupt frame offset {offsets[0]}, fallback frame index and offset {offsets[1:]}", flush=True)
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-dictionary-") as temporary:
        directory = Path(temporary)
        for name, wire in files.items():
            (directory / (name + ".parquet")).write_bytes(wire)
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(directory),
                        *map(str, offsets)], cwd=ROOT, check=True)
        assert {file.stem for file in directory.glob("*.arrows")} == {"v1", "v2", "legacy"}
        for name, unit, zone in (("v1", "ns", "UTC"), ("v2", "us", None), ("legacy", "us", "UTC")):
            verify_ipc(name, files[name], (directory / (name + ".arrows")).read_bytes(), unit, zone)


if __name__ == "__main__":
    main()
