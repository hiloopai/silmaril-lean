"""Compare native Utf8View IPC to pinned producer dictionary pages."""

from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
from runpy import run_path
from struct import unpack_from
import subprocess
import sys

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
read_struct = run_path(str(root / "tests/formats/parquet-timestamp-leaf/check-fixtures.py"))["read_struct"]
entries = [["é", "e\u0301", "雪", "", "unused!"], ["雪", "e\u0301", "é", "", "unused?"]]
slots = [0, None, 1, 0, 3, 2, 0, 1, None]
rows = [[None if slot is None else dictionary[slot] for slot in slots] for dictionary in entries]


def produce(page_version, dictionary=True, annotated=True):
    value_type = pa.string() if annotated else pa.binary()
    field_type = pa.dictionary(pa.int8(), value_type) if dictionary else value_type
    schema = pa.schema([pa.field("id", pa.int32(), nullable=False), pa.field("label", field_type)])
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", compression="NONE",
                          data_page_version=page_version, use_dictionary=["label"] if dictionary else False,
                          write_statistics=False, write_batch_size=4, data_page_size=1,
                          write_page_checksum=False, store_schema=False) as writer:
        for group, values in enumerate(entries):
            if not annotated:
                values = [value.encode() for value in values]
            array = (pa.DictionaryArray.from_arrays(pa.array(slots, pa.int8()), pa.array(values, value_type))
                     if dictionary else pa.array(rows[group], value_type))
            writer.write_table(pa.Table.from_arrays([pa.array(range(len(slots)), pa.int32()), array], schema=schema))
    return sink.getvalue().to_pybytes()


def hybrid(data, width, expected):
    """Independently read exact width-specific RLE/packed runs, including padding."""
    values = []
    offset = 0
    while len(values) < expected:
        control = 0
        for shift in range(0, 35, 7):
            byte = data[offset]
            offset += 1
            control |= (byte & 127) << shift
            if byte < 128:
                break
        number = control >> 1
        assert number > 0
        if control & 1:
            nbytes = number * width
            packed = int.from_bytes(data[offset:offset + nbytes], "little")
            offset += nbytes
            values.extend((packed >> (i * width)) & ((1 << width) - 1) for i in range(number * 8))
        else:
            nbytes = (width + 7) // 8
            value = int.from_bytes(data[offset:offset + nbytes], "little")
            offset += nbytes
            assert value < 1 << width and len(values) + number <= expected
            values.extend([value] * number)
    assert offset == len(data) and len(values) - expected < 8
    assert not any(values[expected:])
    return values[:expected]


def inspect(wire, kind):
    footer_size, = unpack_from("<I", wire, len(wire) - 8)
    footer_start = len(wire) - 8 - footer_size
    footer = read_struct(TCompactProtocol(TMemoryBuffer(wire[footer_start:-8])))
    _, leaves = footer[2][1]
    leaf = leaves[2]
    assert leaf[1] == (TType.I32, 6) and leaf[3] == (TType.I32, 1)
    assert leaf[6] == (TType.I32, 0) and leaf[10] == (TType.STRUCT, {1: (TType.STRUCT, {})})
    dictionaries = []
    data_pages = []
    with pq.ParquetFile(pa.BufferReader(wire)) as file:
        assert file.schema_arrow.field("label") == pa.field("label", pa.string(), nullable=True)
        assert [file.metadata.row_group(i).num_rows for i in range(file.num_row_groups)] == [9, 9]
        for group, expected in enumerate(rows):
            assert file.read_row_group(group, columns=["label"]).column(0).to_pylist() == expected
            chunk = file.metadata.row_group(group).column(1)
            assert chunk.path_in_schema == "label" and chunk.compression == "UNCOMPRESSED"
            assert set(chunk.encodings) == {"PLAIN", "RLE", "RLE_DICTIONARY"}
            start = chunk.dictionary_page_offset
            stop = start + chunk.total_compressed_size
            assert 4 <= start < chunk.data_page_offset < stop <= footer_start

            def frame(offset):
                stream = TMemoryBuffer(wire[offset:stop])
                header = read_struct(TCompactProtocol(stream))
                body = offset + stream.cstringio_buf.tell()
                end = body + header[3][1]
                assert end <= stop and header[2] == header[3] and 4 not in header
                return header, body, end

            header, body, end = frame(start)
            assert header[1] == (TType.I32, 2)
            assert [header[7][1][i][1] for i in (1, 2)] == [len(entries[group]), 0]
            offsets = []
            for value in entries[group]:
                encoded = value.encode()
                assert unpack_from("<I", wire, body)[0] == len(encoded)
                offsets.append(body + 4)
                body += 4 + len(encoded)
                assert wire[offsets[-1]:body] == encoded
            assert body == end == chunk.data_page_offset
            dictionaries.append((start, offsets))

            start = end
            for page, row in enumerate(range(0, len(expected), 4), start=1):
                indices = slots[row:row + 4]
                header, body, end = frame(start)
                assert header[1] == (TType.I32, kind)
                if kind == 0:
                    assert [header[5][1][i][1] for i in (1, 2, 3, 4)] == [len(indices), 8, 3, 3]
                    levels, = unpack_from("<I", wire, body)
                    body += 4
                else:
                    fields = header[8][1]
                    assert [fields[i][1] for i in (1, 2, 3, 4, 6, 7)] == [len(indices), indices.count(None),
                                                                       len(indices), 8, 0, False]
                    levels = fields[5][1]
                assert hybrid(wire[body:body + levels], 1, len(indices)) == [int(i is not None) for i in indices]
                width = wire[body + levels]
                index_runs = body + levels + 1
                assert hybrid(wire[index_runs:end], width, len(indices) - indices.count(None)) == [
                    index for index in indices if index is not None]
                data_pages.append((group, page, start, index_runs, width))
                start = end
            assert start == stop
    return dictionaries, data_pages


cases = {"v1": produce("1.0"), "v2": produce("2.0")}
inspect(cases["v1"], 0)
dictionaries, pages = inspect(cases["v2"], 3)
late_dictionary, late_entries = dictionaries[1]
wire = cases["v2"]
for name, ordinal in (("bad-used-text", 0), ("bad-unused-text", 4)):
    offset = late_entries[ordinal]
    cases[name] = wire[:offset] + b"\xff" + wire[offset + 1:]
late_index = next((header, start, width) for group, page, header, start, width in pages if (group, page) == (1, 2))
header, start, width = late_index
assert width == 3 and wire[start] == 3  # One packed group, first value in low bits.
changed = wire[start + 1] | ((1 << width) - 1)
cases["bad-index"] = wire[:start + 1] + bytes([changed]) + wire[start + 2:]
for name in ("bad-used-text", "bad-unused-text", "bad-index"):
    with pq.ParquetFile(pa.BufferReader(cases[name])) as file:
        assert file.read_row_group(0, columns=["label"]).column(0).to_pylist() == rows[0]
        if name == "bad-unused-text":
            actual = file.read_row_group(1, columns=["label"])
            actual.validate(full=True)
            assert actual.column(0).to_pylist() == rows[1]
        else:
            try:
                file.read_row_group(1, columns=["label"]).validate(full=True)
            except (ValueError, OSError):
                pass
            else:
                raise AssertionError(f"PyArrow admitted {name}")
cases["plain"] = produce("2.0", dictionary=False)
cases["opaque"] = produce("2.0", annotated=False)
for name, wire in cases.items():
    (out / f"{name}.parquet").write_bytes(wire)
print(f"Thrift verified original tag 0 dictionary and tag 8 pages. Late dictionary at {late_dictionary}, index page at {header}", flush=True)
subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                "--run", str(here / "Emit.lean"), str(out), str(late_dictionary), str(header)], cwd=root, check=True)
for name in ("v1", "v2"):
    wire = (out / f"{name}.arrows").read_bytes()
    carrier = pa.BufferReader(wire)
    assert wire.endswith(b"\xff\xff\xff\xff\x00\x00\x00\x00")
    with pq.ParquetFile(out / f"{name}.parquet") as source, pa.ipc.open_stream(carrier) as reader:
        assert reader.schema == pa.schema([pa.field("label", pa.string_view(), nullable=True)])
        for group, batch in zip(range(source.num_row_groups), reader, strict=True):
            expected = source.read_row_group(group, columns=["label"]).column(0).to_pylist()
            assert batch.num_rows == len(expected) and batch.column(0).to_pylist() == expected
        assert carrier.tell() == len(wire)
assert sorted(path.stem for path in out.glob("*.arrows")) == ["v1", "v2"]
artifacts = [out / f"{name}.parquet" for name in cases] + [out / f"{name}.arrows" for name in ("v1", "v2")]
pins = {path.name: sha256(path.read_bytes()).hexdigest() for path in artifacts}
assert pins == json.loads((here / "fixtures.json").read_text(encoding="utf-8")), pins
print(json.dumps(pins, indent=2))
