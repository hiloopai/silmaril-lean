"""Pin PyArrow opaque Snappy dictionaries and compare native BinaryView IPC."""

from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
from runpy import run_path
from struct import unpack_from
import subprocess
import sys
from typing import NamedTuple
from zlib import crc32

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

assert (version("pyarrow"), version("thrift")) == ("26.0.1", "0.25.0")
here = Path(__file__).resolve().parent
root = here.parents[1]
out = Path(sys.argv[1]).resolve()
out.mkdir(parents=True, exist_ok=True)
thrift = run_path(str(root / "tests/formats/parquet-timestamp-leaf/check-fixtures.py"))
codec = pa.Codec("snappy")
entries = [[b"", b"\xff\x00", b"\xed\xa0\x80", b"0123456789abc" * length, b"\xfe\x80unused"]
           for length in (2, 5)]
slots = [[None if 16 <= index < 32 else index % 4 for index in range(rows)] for rows in (257, 129)]
expected = [[dictionary[i] if i is not None else None for i in group] for dictionary, group in zip(entries, slots)]


class Frame(NamedTuple):
    offset: int
    body: int
    end: int
    compressed_size: int
    expanded_size: int
    suffix: int
    compressed: bool


def produce(page_version, crc):
    schema = pa.schema([pa.field("ordinal", pa.int32(), nullable=False),
                        pa.field("blob", pa.dictionary(pa.int8(), pa.binary()))])
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", compression="SNAPPY", data_page_version=page_version,
                          use_dictionary=["blob"], write_batch_size=128,
                          data_page_size=1, write_statistics=False, store_schema=False, write_page_checksum=crc) as writer:
        for values, group in zip(entries, slots):
            array = pa.DictionaryArray.from_arrays(pa.array(group, pa.int8()), pa.array(values, pa.binary()))
            writer.write_table(pa.Table.from_arrays([pa.array(range(len(group)), pa.int32()), array], schema=schema))
    return sink.getvalue().to_pybytes()


def hybrid(data, width, count):
    """Read the producer's RLE and packed runs, checking final padding and extent."""
    at = 0
    result = []
    while len(result) < count:
        run = 0
        for shift in range(0, 35, 7):
            byte = data[at]
            at += 1
            run |= (byte & 127) << shift
            if byte < 128:
                break
        length = run >> 1
        assert length > 0
        if run & 1:
            size = length * width
            bits = int.from_bytes(data[at:at + size], "little")
            result.extend((bits >> (i * width)) & ((1 << width) - 1) for i in range(length * 8))
        else:
            size = (width + 7) // 8
            value = int.from_bytes(data[at:at + size], "little")
            assert value < (1 << width) and len(result) + length <= count
            result.extend([value] * length)
        at += size
    assert at == len(data) and len(result) - count < 8 and not any(result[count:])
    return result[:count]


def inspect(wire, kind, has_crc):
    footer_size, = unpack_from("<I", wire, len(wire) - 8)
    footer_start = len(wire) - 8 - footer_size
    footer = thrift["read_struct"](TCompactProtocol(TMemoryBuffer(wire[footer_start:-8])))
    leaf = thrift["list_field"](footer, 2)[2]
    assert leaf[1] == (TType.I32, 6) and leaf[3] == (TType.I32, 1)
    assert 6 not in leaf and 10 not in leaf
    flags = set()
    geometry = []
    with pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True) as file:
        assert file.schema_arrow.field("blob") == pa.field("blob", pa.binary(), nullable=True)
        assert [file.metadata.row_group(i).num_rows for i in range(file.num_row_groups)] == [257, 129]
        for group, indices in enumerate(slots):
            assert file.read_row_group(group, columns=["blob"]).column(0).to_pylist() == expected[group]
            chunk = file.metadata.row_group(group).column(1)
            assert chunk.compression == "SNAPPY" and chunk.path_in_schema == "blob"
            assert set(chunk.encodings) == {"PLAIN", "RLE", "RLE_DICTIONARY"}
            start = chunk.dictionary_page_offset
            end = start + chunk.total_compressed_size
            assert 4 <= start < chunk.data_page_offset < end <= footer_start
            transport = TMemoryBuffer(wire[start:end])
            protocol = TCompactProtocol(transport)
            frames = []
            expanded_total = 0
            parts = [indices[i:i + 128] for i in range(0, len(indices), 128)]
            for part in [None] + parts:
                offset = start + transport.cstringio_buf.tell()
                header = thrift["read_struct"](protocol)
                body = start + transport.cstringio_buf.tell()
                stored, size = header[3][1], header[2][1]
                payload = transport.readAll(stored)
                stop = body + stored
                assert has_crc == (4 in header) and stop <= end
                if has_crc:
                    assert header[4][1] % 2**32 == crc32(payload)
                expanded_total += body - offset + size
                suffix = body
                compressed = True
                if part is None:
                    assert header[1] == (TType.I32, 2) and stop == chunk.data_page_offset
                    assert [header[7][1][i][1] for i in (1, 2)] == [5, 0]
                    expanded = codec.decompress(payload, size).to_pybytes()
                    at = 0
                    for entry in entries[group]:
                        assert unpack_from("<I", expanded, at)[0] == len(entry)
                        assert expanded[at + 4:at + 4 + len(entry)] == entry
                        at += 4 + len(entry)
                    assert at == len(expanded)
                else:
                    assert header[1] == (TType.I32, kind)
                    if kind == 0:
                        assert [header[5][1][i][1] for i in (1, 2, 3, 4)] == [len(part), 8, 3, 3]
                        expanded = codec.decompress(payload, size).to_pybytes()
                        levels, = unpack_from("<I", expanded)
                        definitions, encoded = expanded[4:4 + levels], expanded[4 + levels:]
                    else:
                        fields = header[8][1]
                        assert [fields[i][1] for i in (1, 2, 3, 4, 6)] == [len(part), part.count(None), len(part), 8, 0]
                        levels = fields[5][1]
                        assert levels <= min(stored, size)
                        definitions, encoded = payload[:levels], payload[levels:]
                        suffix += levels
                        compressed = fields.get(7, (TType.BOOL, True))[1]
                        if compressed:
                            encoded = codec.decompress(encoded, size - levels).to_pybytes()
                        else:
                            assert len(encoded) == size - levels
                    flags.add(compressed)
                    assert hybrid(definitions, 1, len(part)) == [int(index is not None) for index in part]
                    indices = [i for i in part if i is not None]
                    assert hybrid(encoded[1:], encoded[0], len(indices)) == indices
                frames.append(Frame(offset, body, stop, stored, size, suffix, compressed))
            assert frames[-1].end == end and expanded_total == chunk.total_uncompressed_size
            geometry.append((frames, chunk.total_compressed_size, expanded_total))
    assert flags == ({True} if kind == 0 else {False, True})
    return geometry


cases = {}
geometry = {}
for name, version_number, kind in (("v1", "1.0", 0), ("v2", "2.0", 3)):
    for crc in (False, True):
        label = f"{name}-{'crc' if crc else 'absent'}"
        cases[label] = produce(version_number, crc)
        geometry[label] = inspect(cases[label], kind, crc)
        print(f"{label}: original tag-0 dictionary and tag-8 pages, CRC={crc}, totals {[g[1:] for g in geometry[label]]}")

def damage_index(wire, frame):
    assert not frame.compressed and wire[frame.suffix:frame.end] == bytes([3, 2, 0])
    return wire[:frame.end - 1] + b"\x07" + wire[frame.end:]


late = geometry["v2-absent"][1][0]
late_crc = geometry["v2-crc"][1][0]
cases["bad-index"] = damage_index(cases["v2-absent"], late[-1])
cases["bad-crc"] = damage_index(cases["v2-crc"], late_crc[-1])
for name in ("bad-index", "bad-crc"):
    with pq.ParquetFile(pa.BufferReader(cases[name]), page_checksum_verification=True) as file:
        assert file.read_row_group(0, columns=["blob"]).column(0).to_pylist() == expected[0]
        try:
            file.read_row_group(1, columns=["blob"]).validate(full=True)
        except (OSError, ValueError):
            pass
        else:
            raise AssertionError(f"PyArrow accepted {name}")


def produce_mixed(page_version):
    groups = [
        [None if i % 9 == 5 else [b"", b"\xff\x00", b"\xed\xa0\x80", b"0123456789ab"][i % 4]
         if group == 0 or i < 32 else b"\x80\xff\x00" + f"{group}-{i:02d}-".encode() + b"\xfeabc" * 4
         for i in range(64)] for group in range(2)
    ]
    schema = pa.schema([pa.field("ordinal", pa.int32(), nullable=False), pa.field("blob", pa.binary())])
    table = pa.Table.from_arrays([pa.array(range(128), pa.int32()), pa.array(sum(groups, []), pa.binary())], schema=schema)
    sink = pa.BufferOutputStream()
    pq.write_table(table, sink, version="2.6", compression="SNAPPY", data_page_version=f"{page_version}.0",
                   use_dictionary=["blob"], data_page_size=16, dictionary_pagesize_limit=64, write_batch_size=8,
                   row_group_size=64, write_statistics=False, store_schema=False, write_page_checksum=True)
    wire = sink.getvalue().to_pybytes()
    with pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True) as file:
        assert file.schema_arrow == schema and file.num_row_groups == 2
        for group, rows in enumerate(groups):
            assert file.read_row_group(group, columns=["blob"]).column(0).to_pylist() == rows
            column = file.metadata.row_group(group).column(1)
            assert column.compression == "SNAPPY"
            offset = column.dictionary_page_offset
            transport = TMemoryBuffer(wire[offset:offset + column.total_compressed_size])
            protocol = TCompactProtocol(transport)
            header = thrift["read_struct"](protocol)
            assert header[1][1] == 2 and header[7][1][2][1] == 0
            stored = transport.readAll(header[3][1])
            assert header[4][1] % 2**32 == crc32(stored)
            assert offset + transport.cstringio_buf.tell() == column.data_page_offset
            tags = []
            starts = []
            while transport.cstringio_buf.tell() < column.total_compressed_size:
                starts.append(offset + transport.cstringio_buf.tell())
                header = thrift["read_struct"](protocol)
                assert header[1][1] == (0 if page_version == 1 else 3)
                key, tag_field = (5, 2) if page_version == 1 else (8, 4)
                tags.append(header[key][1][tag_field][1])
                stored = transport.readAll(header[3][1])
                assert header[4][1] % 2**32 == crc32(stored)
            assert transport.cstringio_buf.tell() == column.total_compressed_size
            assert tags == ([8] * 8 if group == 0 else [8] * 5 + [0] * 3)
            print(f"mixed V{page_version} group {group}: actual data tags {tags}", flush=True)
    return wire, starts[5]


mixed_v1, v1_header = produce_mixed(1)
mixed_v2, v2_header = produce_mixed(2)
cases["mixed-v1"] = mixed_v1
cases["mixed-v2"] = mixed_v2
sink = pa.BufferOutputStream()
pq.write_table(pa.table({"ordinal": pa.array([1], pa.int32()), "blob": pa.array(["雪"], pa.string())}),
               sink, compression="SNAPPY", store_schema=False)
cases["annotated-string"] = sink.getvalue().to_pybytes()
for name, wire in cases.items():
    (out / f"{name}.parquet").write_bytes(wire)
last = late_crc[-1]
crc = crc32(cases["v2-crc"][last.body:last.end])
wrong_crc = crc32(cases["bad-crc"][last.body:last.end])
coords = [len(late) - 1, late[-1].offset, last.offset, crc, wrong_crc, v1_header, v2_header]
print(f"Original late index, CRC and PLAIN refusal coordinates {coords}", flush=True)
subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                "--run", str(here / "Emit.lean"), str(out), *map(str, coords)], cwd=root, check=True)
for name in geometry:
    wire = (out / f"{name}.arrows").read_bytes()
    carrier = pa.BufferReader(wire)
    assert wire.endswith(b"\xff\xff\xff\xff\x00\x00\x00\x00")
    with pq.ParquetFile(out / f"{name}.parquet") as parquet, pa.ipc.open_stream(carrier) as reader:
        assert reader.schema == pa.schema([pa.field("blob", pa.binary_view(), nullable=True)])
        for group, batch in zip(range(2), reader, strict=True):
            values = parquet.read_row_group(group, columns=["blob"]).column(0).to_pylist()
            assert batch.num_rows == len(values) and batch.column(0).to_pylist() == values
        assert carrier.tell() == len(wire)
assert sorted(path.stem for path in out.glob("*.arrows")) == sorted(geometry)
artifacts = [out / f"{name}.parquet" for name in cases] + [out / f"{name}.arrows" for name in geometry]
pins = {path.name: sha256(path.read_bytes()).hexdigest() for path in artifacts}
assert pins == json.loads((here / "fixtures.json").read_text(encoding="utf-8")), pins
print(json.dumps(pins, indent=2))
