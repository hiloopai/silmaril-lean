"""Pin genuine PyArrow opaque Snappy BYTE_ARRAY fallback and its BinaryView IPC."""

from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
from runpy import run_path
from struct import pack, unpack_from
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
schema = pa.schema([pa.field("ordinal", pa.int32(), nullable=False), pa.field("blob", pa.binary())])
group_size = 66
page_rows = 8
rows = [
    [None if row % 9 == 5 else [b"", b"\xff\x00", b"\xed\xa0\x80", b"0123456789ab"][row % 4] if row < 32 else
     b"\x80\xff\x00" + f"{group}-{row:02d}-".encode() + b"\xfeabc" * (12 if group == 1 and row >= 56 else 4)
     for row in range(64)] + [None, b"\x80\x00\xff"] for group in range(2)
]


class Frame(NamedTuple):
    start: int
    body: int
    end: int
    fields: dict


def produce(page_version, crc):
    table = pa.Table.from_arrays([pa.array(range(2 * group_size), pa.int32()),
                                  pa.array(sum(rows, []), pa.binary())], schema=schema)
    sink = pa.BufferOutputStream()
    pq.write_table(table, sink, version="2.6", data_page_version=f"{page_version}.0", compression="SNAPPY",
                   use_dictionary=["blob"], dictionary_pagesize_limit=64,
                   data_page_size=16, write_batch_size=page_rows, row_group_size=group_size,
                   write_statistics=False, write_page_checksum=crc, store_schema=False)
    return sink.getvalue().to_pybytes()


def frames(wire, group, has_crc):
    with pq.ParquetFile(pa.BufferReader(wire)) as file:
        chunk = file.metadata.row_group(group).column(1)
        assert chunk.path_in_schema == "blob" and chunk.compression == "SNAPPY"
        assert set(chunk.encodings) == {"PLAIN", "RLE", "RLE_DICTIONARY"}
    start = chunk.dictionary_page_offset
    stop = start + chunk.total_compressed_size
    transport = TMemoryBuffer(wire[start:stop])
    protocol = TCompactProtocol(transport)
    result = []
    expanded = 0
    while (offset := start + transport.cstringio_buf.tell()) < stop:
        fields = thrift["read_struct"](protocol)
        body = start + transport.cstringio_buf.tell()
        end = body + fields[3][1]
        payload = transport.readAll(fields[3][1])
        assert end <= stop and (4 in fields) == has_crc
        if has_crc:
            assert fields[4][1] % 2**32 == crc32(payload)
        expanded += body - offset + fields[2][1]
        result.append(Frame(offset, body, end, fields))
    assert result[-1].end == stop and result[1].start == chunk.data_page_offset
    assert expanded == chunk.total_uncompressed_size
    return result, expanded


def plain_values(data, count):
    result = []
    start = 0
    for _ in range(count):
        width, = unpack_from("<I", data, start)
        start += 4
        assert start + width <= len(data)
        result.append((start, data[start:start + width]))
        start += width
    assert start == len(data)
    return result


def packed_indices(data, count):
    """The producer's fallback prefix uses one packed group per page."""
    width, control = data[:2]
    assert control == 3 and 0 < width <= 8 and len(data) == 2 + width
    bits = int.from_bytes(data[2:], "little")
    assert bits >> (width * count) == 0
    return width, [(bits >> (width * i)) & ((1 << width) - 1) for i in range(count)]


def scalar_body(frame, wire, page_version, expected):
    stored = wire[frame.body:frame.end]
    size = frame.fields[2][1]
    if page_version == 1:
        assert frame.fields[1][1] == 0
        fields = frame.fields[5][1]
        assert [fields[i][1] for i in (1, 3, 4)] == [len(expected), 3, 3]
        expanded = codec.decompress(stored, size).to_pybytes()
        levels, = unpack_from("<I", expanded)
        return fields[2][1], expanded[4 + levels:], None
    assert frame.fields[1][1] == 3
    fields = frame.fields[8][1]
    assert [fields[i][1] for i in (1, 2, 3, 6)] == [len(expected), expected.count(None), len(expected), 0]
    levels = fields[5][1]
    assert levels <= min(len(stored), size)
    tag, encoded = fields[4][1], stored[levels:]
    if fields.get(7, (TType.BOOL, True))[1]:
        return tag, codec.decompress(encoded, size - levels).to_pybytes(), None
    assert len(encoded) == size - levels
    return tag, encoded, frame.body + levels


def inspect(wire, page_version, group, expected, tags, has_crc):
    original, expanded_total = frames(wire, group, has_crc)
    dictionary = original[0]
    assert dictionary.fields[1] == (TType.I32, 2)
    count, tag = (dictionary.fields[7][1][i][1] for i in (1, 2))
    assert tag == 0
    body = codec.decompress(wire[dictionary.body:dictionary.end], dictionary.fields[2][1]).to_pybytes()
    values = plain_values(body, count)
    index_pages = {}
    raw_plain = {}
    observed = []
    flags = []
    for ordinal, frame in enumerate(original[1:], start=1):
        part = expected[(ordinal - 1) * page_rows:ordinal * page_rows]
        expected_present = [value for value in part if value is not None]
        tag, scalar, raw_start = scalar_body(frame, wire, page_version, part)
        observed.append(tag)
        flags.append(raw_start is None)
        if tag == 8:
            width, indices = packed_indices(scalar, len(expected_present))
            assert [values[i][1] for i in indices] == expected_present
            index_pages[ordinal] = (raw_start, width, indices)
        elif tag == 0:
            present = plain_values(scalar, len(expected_present))
            assert [value for _, value in present] == expected_present
            if raw_start is not None:
                raw_plain[ordinal] = [raw_start + at for at, _ in present]
        else:
            raise AssertionError(f"unexpected data tag {tag}")
    assert observed == tags
    with pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True) as file:
        assert file.schema_arrow == schema and file.num_row_groups == 2
        assert file.read_row_group(group, columns=["blob"]).column(0).to_pylist() == expected
    print(f"V{page_version} group {group}: tags {observed}, compressed value suffixes {flags}, expanded {expanded_total}", flush=True)
    return original, values, index_pages, raw_plain, flags


clean_tags = [8] * 5 + [0] * 4
cases = {}
geometry = {}
for number in (1, 2):
    for crc in (False, True):
        name = f"v{number}-{'crc' if crc else 'absent'}"
        source = cases[name] = produce(number, crc)
        footer_size, = unpack_from("<I", source, len(source) - 8)
        metadata = thrift["read_struct"](TCompactProtocol(TMemoryBuffer(source[-8 - footer_size:-8])))
        leaf = thrift["list_field"](metadata, 2)[2]
        assert leaf[1] == (TType.I32, 6) and leaf[3] == (TType.I32, 1)
        assert 6 not in leaf and 10 not in leaf
        geometry[name] = [inspect(source, number, group, expected, clean_tags, crc) for group, expected in enumerate(rows)]
        assert all(info[-1] == ([True] * 9 if number == 1 else [False] * 5 + [True] * 3 + [False])
                   for info in geometry[name])

source = cases["v2-absent"]
original, dictionary, indices, raw_plain, _ = geometry["v2-absent"][1]
last = len(original) - 1
[at] = raw_plain[last]
assert source[at:original[-1].end] == b"\x80\x00\xff"
assert unpack_from("<I", source, at - 4)[0] == 3
cases["bad-plain-length"] = source[:at - 4] + pack("<I", 2**31) + source[at:]

start, width, values = indices[5]
assert start is not None and len(dictionary) < 2**width - 1
bad_index = 2**width - 1
packed = int.from_bytes(source[start + 2:original[5].end], "little")
packed |= bad_index
cases["bad-index"] = source[:start + 2] + packed.to_bytes(width, "little") + source[original[5].end:]
assert packed_indices(cases["bad-index"][start:original[5].end], len(values))[1] == [bad_index] + values[1:]

source_crc = cases["v2-crc"]
original_crc, _, _, raw_crc, _ = geometry["v2-crc"][1]
[crc_at] = raw_crc[last]
cases["bad-late-crc"] = source_crc[:crc_at] + b"\x81" + source_crc[crc_at + 1:]
for name in ("bad-plain-length", "bad-index", "bad-late-crc"):
    with pq.ParquetFile(pa.BufferReader(cases[name]), page_checksum_verification=True) as file:
        assert file.read_row_group(0, columns=["blob"]).column(0).to_pylist() == rows[0]
        try:
            file.read_row_group(1, columns=["blob"]).validate(full=True)
        except (ValueError, OSError):
            pass
        else:
            raise AssertionError(f"PyArrow accepted {name}")

# Independently assemble a return to dictionary encoding from two intact
# producer frames. Both CRCs and extent totals remain valid.
last_dictionary, first_plain = original_crc[5:7]
assert last_dictionary.end == first_plain.start
swapped = (source_crc[:last_dictionary.start] + source_crc[first_plain.start:first_plain.end] +
           source_crc[last_dictionary.start:last_dictionary.end] + source_crc[first_plain.end:])
reordered = rows[1][:32] + rows[1][40:48] + rows[1][32:40] + rows[1][48:]
reordered_frames, *_ = inspect(swapped, 2, 1, reordered, [8] * 4 + [0, 8, 0, 0, 0], True)
cases["dictionary-after-plain"] = swapped


def lie_expanded(metadata):
    column = thrift["column_metadata"](metadata, group=1, column=1)
    tag, expanded = column[6]
    assert tag == TType.I64
    column[6] = (tag, expanded - 1)


cases["bad-expanded-total"] = thrift["rewrite_footer"](source_crc, lie_expanded)
# An external STRING producer writes both annotations. The edited control
# keeps only the converted UTF8 field to exercise its independent refusal.
sink = pa.BufferOutputStream()
pq.write_table(pa.table({"ordinal": pa.array([1], pa.int32()), "blob": pa.array(["雪"], pa.string())}),
               sink, compression="SNAPPY", store_schema=False)
cases["annotated-string"] = sink.getvalue().to_pybytes()


def remove_modern(metadata):
    leaf = thrift["list_field"](metadata, 2)[2]
    assert leaf[6] == (TType.I32, 0)
    assert leaf.pop(10) == (TType.STRUCT, {1: (TType.STRUCT, {})})


cases["annotated-converted"] = thrift["rewrite_footer"](cases["annotated-string"], remove_modern)
for name in ("annotated-string", "annotated-converted"):
    with pq.ParquetFile(pa.BufferReader(cases[name])) as file:
        assert file.schema_arrow.field("blob").type == pa.string()
        assert file.read(columns=["blob"]).column(0).to_pylist() == ["雪"]
for name, wire in cases.items():
    (out / f"{name}.parquet").write_bytes(wire)
last_crc = original_crc[-1]
cap = max(frame.fields[2][1] for frame in geometry["v2-crc"][0][0])
cap_page = next(i for i, frame in enumerate(original_crc) if frame.fields[2][1] > cap)
assert cap_page == 8
coords = [last, original[-1].start, original[5].start, bad_index, last_crc.start, reordered_frames[6].start,
          cap, cap_page, original_crc[cap_page].start, crc32(source_crc[last_crc.body:last_crc.end]),
          crc32(cases["bad-late-crc"][last_crc.body:last_crc.end])]
print(f"Original or edited coordinates and caps {coords}", flush=True)
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
