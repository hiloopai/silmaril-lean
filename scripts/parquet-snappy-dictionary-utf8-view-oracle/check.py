"""Pin PyArrow Snappy STRING dictionaries and compare native Utf8View IPC."""

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
entries = [["", "é", "e\u0301", "雪" * length, "unused!"] for length in (6, 20)]
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


def produce(page_version, crc, compression="SNAPPY", dictionary=True):
    schema = pa.schema([pa.field("ordinal", pa.int32(), nullable=False),
                        pa.field("label", pa.dictionary(pa.int8(), pa.string()))])
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", compression=compression, data_page_version=page_version,
                          use_dictionary=["label"] if dictionary else False, write_batch_size=128,
                          data_page_size=1, write_statistics=False, store_schema=False, write_page_checksum=crc) as writer:
        for values, group in zip(entries, slots):
            array = pa.DictionaryArray.from_arrays(pa.array(group, pa.int8()), pa.array(values, pa.string()))
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
    assert leaf[6] == (TType.I32, 0) and leaf[10] == (TType.STRUCT, {1: (TType.STRUCT, {})})
    flags = set()
    geometry = []
    with pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True) as file:
        assert file.schema_arrow.field("label") == pa.field("label", pa.string(), nullable=True)
        assert [file.metadata.row_group(i).num_rows for i in range(file.num_row_groups)] == [257, 129]
        for group, indices in enumerate(slots):
            assert file.read_row_group(group, columns=["label"]).column(0).to_pylist() == expected[group]
            chunk = file.metadata.row_group(group).column(1)
            assert chunk.compression == "SNAPPY" and chunk.path_in_schema == "label"
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
                        entry = entry.encode()
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


def damage_unused(wire, frame):
    stored = wire[frame.body:frame.end]
    assert stored.count(b"unused!") == 1
    offset = frame.body + stored.index(b"unused!")
    edited = wire[:offset] + b"\xff" + wire[offset + 1:]
    raw = codec.decompress(stored, frame.expanded_size).to_pybytes()
    assert codec.decompress(edited[frame.body:frame.end], frame.expanded_size).to_pybytes() == raw[:-7] + b"\xffnused!"
    return edited


def damage_index(wire, frame):
    assert not frame.compressed and wire[frame.suffix:frame.end] == bytes([3, 2, 0])
    return wire[:frame.end - 1] + b"\x07" + wire[frame.end:]


absent, checked = cases["v2-absent"], cases["v2-crc"]
late = geometry["v2-absent"][1][0]
late_crc = geometry["v2-crc"][1][0]
cases["bad-unused"] = damage_unused(absent, late[0])
cases["bad-index"] = damage_index(absent, late[-1])
cases["bad-dictionary-crc"] = damage_unused(checked, late_crc[0])
cases["bad-data-crc"] = damage_index(checked, late_crc[-1])
for name in ("bad-unused", "bad-index", "bad-dictionary-crc", "bad-data-crc"):
    with pq.ParquetFile(pa.BufferReader(cases[name]), page_checksum_verification=True) as file:
        assert file.read_row_group(0, columns=["label"]).column(0).to_pylist() == expected[0]
        if name == "bad-unused":
            assert file.read_row_group(1, columns=["label"]).column(0).to_pylist() == expected[1]
        else:
            try:
                file.read_row_group(1, columns=["label"]).validate(full=True)
            except (OSError, ValueError):
                pass
            else:
                raise AssertionError(f"PyArrow admitted {name}")


def lie_expanded(metadata):
    column = thrift["column_metadata"](metadata, group=1, column=1)
    tag, expanded = column[6]
    assert tag == TType.I64 and expanded == geometry["v2-crc"][1][2]
    column[6] = (tag, expanded - 1)


cases["bad-expanded-count"] = thrift["rewrite_footer"](checked, lie_expanded)
cases["uncompressed"] = produce("2.0", False, compression="NONE")
cases["plain"] = produce("2.0", False, dictionary=False)
for name, wire in cases.items():
    (out / f"{name}.parquet").write_bytes(wire)
first, stored_chunk, expanded_chunk = geometry["v2-crc"][0]
expanded_page = max(frame.expanded_size for frame in first)
assert expanded_page < late_crc[0].expanded_size
coords = [late[0].offset, late[-1].offset, len(late) - 1, late_crc[0].offset, late_crc[-1].offset,
          first[0].offset, stored_chunk - 1, expanded_chunk - 1, first[0].compressed_size - 1, expanded_page]
for name, frame in (("bad-dictionary-crc", late_crc[0]), ("bad-data-crc", late_crc[-1])):
    coords += [crc32(checked[frame.body:frame.end]), crc32(cases[name][frame.body:frame.end])]
print(f"Checked original coordinates and caps {coords}", flush=True)
subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                "--run", str(here / "Emit.lean"), str(out), *map(str, coords)], cwd=root, check=True)
for name in geometry:
    wire = (out / f"{name}.arrows").read_bytes()
    carrier = pa.BufferReader(wire)
    assert wire.endswith(b"\xff\xff\xff\xff\x00\x00\x00\x00")
    with pq.ParquetFile(out / f"{name}.parquet") as parquet, pa.ipc.open_stream(carrier) as reader:
        assert reader.schema == pa.schema([pa.field("label", pa.string_view(), nullable=True)])
        for group, batch in zip(range(2), reader, strict=True):
            values = parquet.read_row_group(group, columns=["label"]).column(0).to_pylist()
            assert batch.num_rows == len(values) and batch.column(0).to_pylist() == values
        assert carrier.tell() == len(wire)
assert sorted(path.stem for path in out.glob("*.arrows")) == sorted(geometry)
artifacts = [out / f"{name}.parquet" for name in cases] + [out / f"{name}.arrows" for name in geometry]
pins = {path.name: sha256(path.read_bytes()).hexdigest() for path in artifacts}
assert pins == json.loads((here / "fixtures.json").read_text(encoding="utf-8")), pins
print(json.dumps(pins, indent=2))
