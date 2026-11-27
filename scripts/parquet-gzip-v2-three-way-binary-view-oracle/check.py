"""Pin three native GZIP V2 profiles and a labeled unchanged-chunk assembly."""

from copy import deepcopy
from hashlib import sha256
import json
import os
from pathlib import Path
from runpy import run_path
from struct import pack, unpack_from
import subprocess
import sys
from zlib import crc32

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUT = Path(sys.argv[1]).resolve()
OUT.mkdir(parents=True, exist_ok=True)
PHYSICAL = run_path(str(HERE.parent / "parquet-gzip-dictionary-binary-view-oracle/check.py"))
HYBRID = run_path(str(HERE.parent / "parquet-timestamp-snappy-dictionary-oracle/check.py"))["hybrid"]
THRIFT = PHYSICAL["THRIFT"]
SCHEMA = pa.schema([pa.field("ordinal", pa.int32(), nullable=False), pa.field("blob", pa.binary())])
ROWS = {
    "plain": [None if index % 7 == 3 else b"\xff\x00" + b"payload" * 6 for index in range(64)] + [b""],
    "dictionary": [b"", None, b"\xff\x00", b"\xed\xa0\x80"] * 10,
    "fallback": [b"", None, b"\xff\x00", b"\xed\xa0\x80"] * 8
    + [None if index % 13 == 0 else b"\x80\x00" + bytes([index]) + b"long" * 5 for index in range(32)],
}
TAGS = {"plain": [0, 0, 0], "dictionary": [8] * 5, "fallback": [8] * 5 + [0] * 3}
FLAGS = {"plain": [True, True, False], "dictionary": [False] * 5, "fallback": [False] * 5 + [True] * 3}
ORDER = ("dictionary", "plain", "fallback", "dictionary")


def produce(profile):
    rows = ROWS[profile]
    options = ({"use_dictionary": False, "column_encoding": "PLAIN", "write_batch_size": 32}
               if profile == "plain" else {"use_dictionary": ["blob"], "write_batch_size": 8})
    sink = pa.BufferOutputStream()
    pq.write_table(pa.Table.from_arrays([pa.array(range(len(rows)), pa.int32()), pa.array(rows, pa.binary())], schema=SCHEMA),
                   sink, version="2.6", compression="GZIP", data_page_version="2.0", data_page_size=1,
                   dictionary_pagesize_limit=64, write_statistics=False, store_schema=False,
                   write_page_checksum=True, **options)
    return sink.getvalue().to_pybytes()


def assemble(parents):
    """Copy complete row-group byte spans and relocate only Thrift metadata."""
    origin = {name: PHYSICAL["read_footer"](wire) for name, wire in parents.items()}
    base = deepcopy(origin["plain"][1])
    assert all(footer[2] == base[2] and footer[7] == base[7] for _, footer in origin.values())
    body = bytearray(b"PAR1")
    groups = []
    for name in ORDER:
        footer_at, footer = origin[name]
        group, = deepcopy(THRIFT["list_field"](footer, 4))
        delta = len(body) - 4
        assert group[5][1] == 4 and group[6][1] == footer_at - 4 and 7 not in group
        group[5] = TType.I64, len(body)
        cursor = 4
        for chunk in THRIFT["list_field"](group, 1):
            metadata = chunk[3][1]
            assert set(chunk) == {2, 3} and chunk[2][1] == 0
            assert not set(metadata) & {10, 14, 15}
            assert metadata.get(11, metadata[9])[1] == cursor
            cursor += metadata[7][1]
            for key in (9, 11):
                if key in metadata:
                    assert metadata[key][0] == TType.I64 and metadata[key][1] >= 4
                    metadata[key] = TType.I64, metadata[key][1] + delta
        assert cursor == footer_at
        body.extend(parents[name][4:footer_at])
        groups.append(group)
    base[3] = TType.I64, sum(group[3][1] for group in groups)
    base[4] = TType.LIST, (TType.STRUCT, groups)
    base[6] = TType.STRING, b"Fixture assembly from unchanged PyArrow 26.0.1 GZIP V2 chunks"
    encoded = THRIFT["encode"](base)
    return bytes(body) + encoded + pack("<I", len(encoded)) + b"PAR1"


def chunks(wire, row_group):
    for index in range(row_group.num_columns):
        chunk = row_group.column(index)
        start = chunk.dictionary_page_offset if chunk.has_dictionary_page else chunk.data_page_offset
        yield wire[start:start + chunk.total_compressed_size]


def plain_values(data, count):
    values, offset = [], 0
    for _ in range(count):
        size, = unpack_from("<i", data, offset)
        start = offset + 4
        assert 0 <= size <= len(data) - start
        offset = start + size
        values.append(data[start:offset])
    assert offset == len(data)
    return values


def inspect(label, wire, profiles, original=None):
    footer_at, footer = PHYSICAL["read_footer"](wire)
    leaf = THRIFT["list_field"](footer, 2)[2]
    assert leaf[1][1] == 6 and leaf[3][1] == 1 and 6 not in leaf and 10 not in leaf
    geometry = []
    with pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True) as file:
        assert file.num_row_groups == len(profiles) and file.schema_arrow == SCHEMA
        for index, profile in enumerate(profiles):
            rows = ROWS[profile]
            assert file.read_row_group(index).to_pydict() == {"ordinal": list(range(len(rows))), "blob": rows}
            group = file.metadata.row_group(index)
            if original is not None:
                assert list(chunks(wire, group)) == original[profile]
            chunk = group.column(1)
            assert chunk.compression == "GZIP" and chunk.path_in_schema == "blob"
            assert chunk.has_dictionary_page == (profile != "plain")
            frames = PHYSICAL["frames"](wire, chunk, True)
            assert frames[-1].stop <= footer_at
            entries, data = [], frames
            if chunk.has_dictionary_page:
                dictionary, *data = frames
                assert dictionary.fields[1][1] == 2 and dictionary.fields[7][1][2][1] == 0
                expanded = PHYSICAL["expand"](wire[dictionary.body:dictionary.stop])
                assert len(expanded) == dictionary.fields[2][1]
                entries = plain_values(expanded, dictionary.fields[7][1][1][1])
            tags, flags, cursor = [], [], 0
            for frame in data:
                assert frame.fields[1][1] == 3
                fields = frame.fields[8][1]
                count, nulls, row_count, tag, levels, repetitions, flag = [fields[i][1] for i in range(1, 8)]
                part = rows[cursor:cursor + count]
                cursor += count
                assert len(part) == count == row_count and part.count(None) == nulls and repetitions == 0
                assert 0 < levels <= min(frame.fields[2][1], frame.fields[3][1])
                split = frame.body + levels
                assert HYBRID(wire[frame.body:split], 1, count) == [int(value is not None) for value in part]
                suffix = wire[split:frame.stop]
                decoded = PHYSICAL["expand"](suffix) if flag else suffix
                assert len(decoded) == frame.fields[2][1] - levels
                present = [value for value in part if value is not None]
                if tag == 8:
                    indices = HYBRID(decoded[1:], decoded[0], len(present))
                    assert [entries[i] for i in indices] == present
                else:
                    assert tag == 0 and plain_values(decoded, len(present)) == present
                tags.append(tag)
                flags.append(flag)
            assert cursor == len(rows) and tags == TAGS[profile] and flags == FLAGS[profile]
            geometry.append(frames)
            print(f"{label} group {index}: {profile}, {len(rows)} rows, tags {tags}, flags {flags}", flush=True)
    return geometry


def bad_crc(wire, frame):
    changed = wire[:frame.body] + bytes([wire[frame.body] ^ 1]) + wire[frame.body + 1:]
    assert crc32(changed[frame.body:frame.stop]) != frame.fields[4][1] % 2**32
    return changed


parents = {name: produce(name) for name in ROWS}
cases = {}
original = {}
for name, wire in parents.items():
    cases[f"native-{name}"] = wire
    inspect(f"native-{name}", wire, (name,))
    with pq.ParquetFile(pa.BufferReader(wire)) as file:
        original[name] = list(chunks(wire, file.metadata.row_group(0)))

mixed = cases["assembled-mixed"] = assemble(parents)
frames = inspect("assembled-mixed (unchanged chunks)", mixed, ORDER, original)
plain_page, dictionary_page = frames[1][0], frames[3][-1]
cases["assembled-bad-plain-crc"] = bad_crc(mixed, plain_page)
cases["assembled-bad-dictionary-crc"] = bad_crc(mixed, dictionary_page)
cases["assembled-double-crc"] = bad_crc(cases["assembled-bad-plain-crc"], dictionary_page)
last_dictionary, first_plain = frames[2][5:7]
assert last_dictionary.stop == first_plain.header
dictionary_frame = mixed[last_dictionary.header:last_dictionary.stop]
plain_frame = mixed[first_plain.header:first_plain.stop]
reentry_offset = last_dictionary.header + len(plain_frame)
cases["assembled-reentry"] = mixed[:last_dictionary.header] + plain_frame + dictionary_frame + mixed[first_plain.stop:]

failures = {"assembled-bad-plain-crc": 1, "assembled-bad-dictionary-crc": 3,
            "assembled-double-crc": 1, "assembled-reentry": 2}
for name, failed in failures.items():
    with pq.ParquetFile(pa.BufferReader(cases[name]), page_checksum_verification=True) as file:
        assert [file.read_row_group(i, columns=["blob"]).column(0).to_pylist() for i in range(failed)] == [
            ROWS[profile] for profile in ORDER[:failed]]
        if name == "assembled-reentry":
            reordered = PHYSICAL["frames"](cases[name], file.metadata.row_group(failed).column(1), True)
            assert [frame.fields[8][1][4][1] for frame in reordered[1:]] == [8] * 4 + [0, 8, 0, 0]
            assert reordered[6].header == reentry_offset
        else:
            try:
                file.read_row_group(failed, columns=["blob"])
            except OSError:
                pass
            else:
                raise AssertionError("PyArrow admitted a changed stored CRC")

for name, wire in cases.items():
    (OUT / f"{name}.parquet").write_bytes(wire)

offsets = [plain_page.header, dictionary_page.header, reentry_offset]
subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                "--run", str(HERE / "Emit.lean"), str(OUT), *map(str, offsets)], cwd=ROOT, check=True)

outputs = ["native-plain", "native-dictionary", "native-fallback", "assembled-mixed"]
for name in outputs:
    with pq.ParquetFile(OUT / f"{name}.parquet", page_checksum_verification=True) as source, \
            pa.ipc.open_stream(OUT / f"{name}.arrows") as reader:
        assert reader.schema == pa.schema([pa.field("blob", pa.binary_view())])
        assert [batch.column(0).to_pylist() for batch in reader] == [
            source.read_row_group(i, columns=["blob"]).column(0).to_pylist() for i in range(source.num_row_groups)]

artifacts = [OUT / f"{name}.parquet" for name in cases] + [OUT / f"{name}.arrows" for name in outputs]
pins = {path.name: sha256(path.read_bytes()).hexdigest() for path in artifacts}
print(json.dumps(pins, indent=2), flush=True)
assert pins == json.loads((HERE / "fixtures.json").read_text())
print("PyArrow/Thrift: three native profiles, unchanged assembled chunks, and exact BinaryView pin replay")
