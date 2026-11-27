"""Pin PyArrow-produced STRING dictionary fallback and targeted edited controls."""

from collections import Counter
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
schema = pa.schema([pa.field("ordinal", pa.int32(), nullable=False), pa.field("label", pa.string())])
group_size = 64
page_rows = 8
rows = [
    [None if row % 9 == 5 else ["", "é", "e\u0301", "雪"][row % 4] if row < 32 else
     f"雪{group}-{row:02d}-" + "éabc" * 4 for row in range(group_size)]
    for group in range(2)
]


class Frame(NamedTuple):
    start: int
    body: int
    end: int
    fields: dict


def produce(page_version, dictionary=True, dictionary_limit=64):
    table = pa.Table.from_arrays([pa.array(range(2 * group_size), pa.int32()),
                                  pa.array(sum(rows, []), pa.string())], schema=schema)
    sink = pa.BufferOutputStream()
    options = {} if dictionary else {"column_encoding": "PLAIN"}
    pq.write_table(table, sink, version="2.6", data_page_version=f"{page_version}.0", compression="NONE",
                   use_dictionary=["label"] if dictionary else False, dictionary_pagesize_limit=dictionary_limit,
                   data_page_size=16, write_batch_size=page_rows, row_group_size=group_size,
                   write_statistics=False, write_page_checksum=False, store_schema=False, **options)
    return sink.getvalue().to_pybytes()


def frames(wire, group):
    with pq.ParquetFile(pa.BufferReader(wire)) as file:
        chunk = file.metadata.row_group(group).column(1)
        assert chunk.path_in_schema == "label" and chunk.compression == "UNCOMPRESSED"
        assert set(chunk.encodings) == {"PLAIN", "RLE", "RLE_DICTIONARY"}
    start = chunk.dictionary_page_offset
    end = start + chunk.total_compressed_size
    transport = TMemoryBuffer(wire[start:end])
    protocol = TCompactProtocol(transport)
    result = []
    while (header := start + transport.cstringio_buf.tell()) < end:
        fields = thrift["read_struct"](protocol)
        body = start + transport.cstringio_buf.tell()
        stop = body + fields[3][1]
        assert fields[2] == fields[3] and 4 not in fields and stop <= end
        result.append(Frame(header, body, stop, fields))
        transport.readAll(fields[3][1])
    assert result[-1].end == end and result[1].start == chunk.data_page_offset
    return result


def plain_values(wire, start, stop, count):
    """Read exact little-endian length-prefixed bytes and their offsets."""
    result = []
    for _ in range(count):
        size, = unpack_from("<I", wire, start)
        start += 4
        assert start + size <= stop
        result.append((start, wire[start:start + size]))
        start += size
    assert start == stop
    return result


def scalar_bounds(frame, wire, page_version, expected):
    if page_version == 1:
        assert frame.fields[1][1] == 0
        fields = frame.fields[5][1]
        assert [fields[i][1] for i in (1, 3, 4)] == [len(expected), 3, 3]
        levels, = unpack_from("<I", wire, frame.body)
        return fields[2][1], frame.body + 4 + levels
    assert frame.fields[1][1] == 3
    fields = frame.fields[8][1]
    assert [fields[i][1] for i in (1, 2, 3, 6, 7)] == [len(expected), expected.count(None), len(expected), 0, False]
    return fields[4][1], frame.body + fields[5][1]


def packed_indices(wire, start, stop, count):
    """These producer pages use one packed group with zero padding."""
    width, control = wire[start:start + 2]
    assert control == 3 and 0 < width <= 8 and stop - start == 2 + width
    bits = int.from_bytes(wire[start + 2:stop], "little")
    assert bits >> (width * count) == 0
    return width, [(bits >> (width * i)) & ((1 << width) - 1) for i in range(count)]


def inspect(wire, version_number, group, expected, expected_tags):
    original = frames(wire, group)
    dictionary = original[0]
    assert dictionary.fields[1] == (TType.I32, 2)
    entries, encoding = (dictionary.fields[7][1][i][1] for i in (1, 2))
    assert encoding == 0
    values = plain_values(wire, dictionary.body, dictionary.end, entries)
    index_pages = {}
    plain_pages = {}
    tags = []
    for ordinal, frame in enumerate(original[1:], start=1):
        expected_page = expected[(ordinal - 1) * page_rows:ordinal * page_rows]
        expected_present = [value.encode() for value in expected_page if value is not None]
        tag, start = scalar_bounds(frame, wire, version_number, expected_page)
        tags.append(tag)
        if tag == 8:
            width, indices = packed_indices(wire, start, frame.end, len(expected_present))
            assert [values[i][1] for i in indices] == expected_present
            index_pages[ordinal] = (start, width, indices)
        elif tag == 0:
            present = plain_values(wire, start, frame.end, len(expected_present))
            assert [value for _, value in present] == expected_present
            plain_pages[ordinal] = present
        else:
            raise AssertionError(f"unexpected data tag {tag}")
    assert tags == expected_tags
    with pq.ParquetFile(pa.BufferReader(wire)) as file:
        assert file.schema_arrow == schema
        assert [file.metadata.row_group(i).num_rows for i in range(file.num_row_groups)] == [64, 64]
        assert file.read_row_group(group, columns=["label"]).column(0).to_pylist() == expected
    print(f"V{version_number} group {group}: original dictionary tag 0, data tags {tags}", flush=True)
    return original, values, index_pages, plain_pages


clean_tags = [8] * 5 + [0] * 3
cases = {"v1": produce(1), "v2": produce(2)}
for number in (1, 2):
    source = cases[f"v{number}"]
    footer_size, = unpack_from("<I", source, len(source) - 8)
    metadata = thrift["read_struct"](TCompactProtocol(TMemoryBuffer(source[-8 - footer_size:-8])))
    leaf = thrift["list_field"](metadata, 2)[2]
    assert leaf[1] == (TType.I32, 6) and leaf[3] == (TType.I32, 1)
    assert leaf[6] == (TType.I32, 0) and leaf[10] == (TType.STRUCT, {1: (TType.STRUCT, {})})
    for group, expected in enumerate(rows):
        original, entries, index_pages, plain_pages = inspect(source, number, group, expected, clean_tags)

# Turn one dictionary entry into an unused entry by changing its sole reference,
# then damage its first octet. All offsets, counts and tags stay original.
source = cases["v2"]
counts = Counter(i for _, _, indices in index_pages.values() for i in indices)
start, width, indices = index_pages[5]
position, unused = next((position, i) for position, i in enumerate(indices) if counts[i] == 1 and i != 0)
mask = ((1 << width) - 1) << (width * position)
payload = int.from_bytes(source[start + 2:original[5].end], "little")
put = bytearray(source)
put[start + 2:original[5].end] = (payload & ~mask).to_bytes(width, "little")
offset, old = entries[unused]
assert old
put[offset] = 0xff
cases["bad-unused-text"] = bytes(put)
_, remaining = packed_indices(put, start, original[5].end, len(indices))
assert remaining == indices[:position] + [0] + indices[position + 1:] and unused not in remaining
expected = rows[1].copy()
selected_row = [i for i in range(32, 40) if expected[i] is not None][position]
expected[selected_row] = entries[0][1].decode()
with pq.ParquetFile(pa.BufferReader(put)) as reference:
    table = reference.read_row_group(1, columns=["label"])
    table.validate(full=True)
    assert table.column(0).to_pylist() == expected

# Keep the last PLAIN frame's lengths intact and corrupt one present value.
last = len(original) - 1
last_slots = rows[1][-page_rows:]
slot = last_slots.index(None) + 1
assert last_slots[slot] is not None
present_slot = sum(value is not None for value in last_slots[:slot])
offset, old = plain_pages[last][present_slot]
assert old and old[0] != 0xff
cases["bad-plain-text"] = source[:offset] + b"\xff" + source[offset + 1:]
with pq.ParquetFile(pa.BufferReader(cases["bad-plain-text"])) as reference:
    assert reference.read_row_group(0, columns=["label"]).column(0).to_pylist() == rows[0]
    try:
        reference.read_row_group(1, columns=["label"]).validate(full=True)
    except (OSError, ValueError):
        pass
    else:
        raise AssertionError("PyArrow accepted invalid PLAIN UTF-8")

# Swap two whole frames of the same row count and keep both bodies valid.
# This independently assembled negative control returns to tag 8 after tag 0.
last_dictionary, first_plain = original[5:7]
assert last_dictionary.end == first_plain.start
swapped = (source[:last_dictionary.start] + source[first_plain.start:first_plain.end] +
           source[last_dictionary.start:last_dictionary.end] + source[first_plain.end:])
reordered = rows[1][:32] + rows[1][40:48] + rows[1][32:40] + rows[1][48:]
reordered_frames, _, _, _ = inspect(swapped, 2, 1, reordered, [8] * 4 + [0, 8, 0, 0])
cases["dictionary-after-plain"] = swapped
cases["plain-only"] = produce(2, dictionary=False)
cases["dictionary-only"] = produce(2, dictionary_limit=1 << 20)
for name, wire in cases.items():
    (out / f"{name}.parquet").write_bytes(wire)
coordinates = [original[0].start, unused, last, original[last].start, slot, reordered_frames[6].start]
print(f"Original/edited control coordinates {coordinates}", flush=True)
subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                "--run", str(here / "Emit.lean"), str(out), *map(str, coordinates)], cwd=root, check=True)
for name in ("v1", "v2"):
    wire = (out / f"{name}.arrows").read_bytes()
    carrier = pa.BufferReader(wire)
    assert wire.endswith(b"\xff\xff\xff\xff\x00\x00\x00\x00")
    with pq.ParquetFile(out / f"{name}.parquet") as parquet, pa.ipc.open_stream(carrier) as ipc:
        assert ipc.schema == pa.schema([pa.field("label", pa.string_view(), nullable=True)])
        for group, batch in zip(range(2), ipc, strict=True):
            expected = parquet.read_row_group(group, columns=["label"]).column(0).to_pylist()
            assert batch.num_rows == len(expected) and batch.column(0).to_pylist() == expected
        assert carrier.tell() == len(wire)
assert sorted(path.stem for path in out.glob("*.arrows")) == ["v1", "v2"]
artifacts = [out / f"{name}.parquet" for name in cases] + [out / f"{name}.arrows" for name in ("v1", "v2")]
pins = {path.name: sha256(path.read_bytes()).hexdigest() for path in artifacts}
assert pins == json.loads((here / "fixtures.json").read_text(encoding="utf-8")), pins
print(json.dumps(pins, indent=2))
