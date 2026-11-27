"""Pin real GZIP V2 fallback with both flags on both encodings."""

from hashlib import sha256
import json
import os
from pathlib import Path
from runpy import run_path
from struct import pack, unpack_from
import subprocess
import sys
from zlib import crc32, decompressobj

import pyarrow as pa
import pyarrow.parquet as pq


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUT = Path(sys.argv[1]).resolve()
OUT.mkdir(parents=True, exist_ok=True)
PHYSICAL = run_path(str(HERE.parent / "parquet-gzip-dictionary-binary-view-oracle/check.py"))
HYBRID = run_path(str(HERE.parent / "parquet-timestamp-snappy-dictionary-oracle/check.py"))["hybrid"]
BATCH = 256
ROWS = [
    [b"", None, b"\xff\x00", b"\xed\xa0\x80"] * (BATCH // 4)
    + [None] * BATCH
    + [bytes([index]) + b"long" * 5 + bytes([group]) for index in range(BATCH)]
    + [None if index % 13 == 0 else bytes([group, index]) + b"plain" * 5 for index in range(BATCH)]
    + ([b"\xff"] if group == 0 else [b"", b"\xfe\x00"])
    for group in range(2)
]
COMPRESSED_TAIL = [ROWS[0], ROWS[1][:4 * BATCH]]


def produce(groups, crc, version="2.0"):
    schema = pa.schema([pa.field("ordinal", pa.int32(), nullable=False), pa.field("blob", pa.binary())])
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", compression="GZIP", data_page_version=version,
                          use_dictionary=["blob"], data_page_size=16, dictionary_pagesize_limit=64,
                          write_batch_size=BATCH, write_statistics=False, store_schema=False,
                          write_page_checksum=crc) as writer:
        for rows in groups:
            table = pa.Table.from_arrays([pa.array(range(len(rows)), pa.int32()), pa.array(rows, pa.binary())],
                                         schema=schema)
            writer.write_table(table)
    return sink.getvalue().to_pybytes()


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


def inspect(wire, groups, crc):
    footer_start, footer = PHYSICAL["read_footer"](wire)
    leaf = PHYSICAL["THRIFT"]["list_field"](footer, 2)[2]
    assert leaf[1][1] == 6 and leaf[3][1] == 1 and 6 not in leaf and 10 not in leaf
    geometry = []
    with pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True) as file:
        assert file.num_row_groups == len(groups) and file.schema_arrow.field("blob") == pa.field("blob", pa.binary())
        for group, rows in enumerate(groups):
            assert file.read_row_group(group, columns=["blob"]).column(0).to_pylist() == rows
            column = file.metadata.row_group(group).column(1)
            assert column.compression == "GZIP" and column.path_in_schema == "blob"
            assert set(column.encodings) == {"PLAIN", "RLE", "RLE_DICTIONARY"}
            dictionary, *data = PHYSICAL["frames"](wire, column, crc)
            assert data[-1].stop <= footer_start and dictionary.fields[1][1] == 2
            count = dictionary.fields[7][1][1][1]
            assert dictionary.fields[7][1][2][1] == 0
            expanded = PHYSICAL["expand"](wire[dictionary.body:dictionary.stop])
            assert len(expanded) == dictionary.fields[2][1]
            entries = plain_values(expanded, count)
            tags, flags = [], []
            parts = [rows[i:i + BATCH] for i in range(0, len(rows), BATCH)]
            for part, frame in zip(parts, data, strict=True):
                assert frame.fields[1][1] == 3
                fields = frame.fields[8][1]
                assert [fields[i][1] for i in (1, 2, 3, 6)] == [len(part), part.count(None), len(part), 0]
                level_bytes = fields[5][1]
                assert 0 < level_bytes <= min(frame.fields[2][1], frame.fields[3][1])
                split = frame.body + level_bytes
                assert HYBRID(wire[frame.body:split], 1, len(part)) == [int(value is not None) for value in part]
                flag, tag = fields[7][1], fields[4][1]
                flags.append(flag)
                tags.append(tag)
                suffix = wire[split:frame.stop]
                decoded = PHYSICAL["expand"](suffix) if flag else suffix
                assert len(decoded) == frame.fields[2][1] - level_bytes
                present = [value for value in part if value is not None]
                if tag == 8:
                    indices = HYBRID(decoded[1:], decoded[0], len(present))
                    assert [entries[index] for index in indices] == present
                else:
                    assert tag == 0 and plain_values(decoded, len(present)) == present
            assert tags == [8, 8, 8, 0, 0][:len(parts)]
            assert flags == [True, False, False, True, False][:len(parts)]
            geometry.append([dictionary, *data])
            print(f"V2 CRC={crc} group {group}: tags {tags}, flags {flags}, {len(rows)} rows", flush=True)
    return geometry


def bad_crc(wire, frame):
    changed = wire[:frame.body] + bytes([wire[frame.body] ^ 1]) + wire[frame.body + 1:]
    expected = frame.fields[4][1] % 2**32
    actual = crc32(changed[frame.body:frame.stop])
    assert actual != expected
    return changed, expected, actual


cases = {}
geometry = {}
for name, groups, crc in [("v2-crc", ROWS, True), ("v2-absent", ROWS, False),
                          ("compressed-tail", COMPRESSED_TAIL, False)]:
    cases[name] = produce(groups, crc)
    geometry[name] = inspect(cases[name], groups, crc)

crc_wire = cases["v2-crc"]
dict_page, plain_page = [geometry["v2-crc"][1][i] for i in (1, 4)]
cases["bad-dict-crc"], dict_expected, dict_actual = bad_crc(crc_wire, dict_page)
cases["bad-plain-crc"], plain_expected, plain_actual = bad_crc(crc_wire, plain_page)

raw_wire = cases["v2-absent"]
raw_page = geometry["v2-absent"][1][-1]
raw_offset = raw_page.body + raw_page.fields[8][1][5][1]
assert raw_page.fields[8][1][7][1] is False
assert plain_values(raw_wire[raw_offset:raw_page.stop], 2) == ROWS[1][-2:]
cases["bad-raw-length"] = raw_wire[:raw_offset] + pack("<I", 2**31) + raw_wire[raw_offset + 4:]

member_page = geometry["compressed-tail"][1][-1]
assert member_page.fields[8][1][7][1] and member_page.fields[8][1][4][1] == 0
cases["extra-member"] = PHYSICAL["add_member"](cases["compressed-tail"], member_page)
with pq.ParquetFile(pa.BufferReader(cases["extra-member"])) as file:
    frame = PHYSICAL["frames"](cases["extra-member"], file.metadata.row_group(1).column(1), False)[-1]
    levels = frame.fields[8][1][5][1]
    decoder = decompressobj(wbits=31)
    decoded = decoder.decompress(cases["extra-member"][frame.body + levels:frame.stop])
    assert decoder.eof and PHYSICAL["expand"](decoder.unused_data) == b""
    assert len(decoded) == frame.fields[2][1] - levels

last_dictionary, first_plain = geometry["v2-crc"][1][3:5]
assert last_dictionary.stop == first_plain.header
dictionary_body = crc_wire[last_dictionary.header:last_dictionary.stop]
plain_body = crc_wire[first_plain.header:first_plain.stop]
reentry_offset = last_dictionary.header + len(plain_body)
cases["reentry"] = crc_wire[:last_dictionary.header] + plain_body + dictionary_body + crc_wire[first_plain.stop:]

cases["v1"] = produce(ROWS, True, "1.0")
with pq.ParquetFile(pa.BufferReader(cases["v1"]), page_checksum_verification=True) as file:
    assert file.read_row_group(0, columns=["blob"]).column(0).to_pylist() == ROWS[0]
    v1_frames = PHYSICAL["frames"](cases["v1"], file.metadata.row_group(0).column(1), True)
    assert [frame.fields[5][1][2][1] for frame in v1_frames[1:]] == [8, 8, 8, 0, 0]

for name in ("bad-dict-crc", "bad-plain-crc", "bad-raw-length", "extra-member", "reentry"):
    with pq.ParquetFile(pa.BufferReader(cases[name]), page_checksum_verification=True) as file:
        assert file.read_row_group(0, columns=["blob"]).column(0).to_pylist() == ROWS[0]
        if name == "reentry":
            frames = PHYSICAL["frames"](cases[name], file.metadata.row_group(1).column(1), True)
            assert [frame.fields[8][1][4][1] for frame in frames[1:]] == [8, 8, 0, 8, 0]
            assert frames[4].header == reentry_offset
        elif name != "extra-member":
            try:
                file.read_row_group(1, columns=["blob"])
            except (OSError, ValueError):
                pass
            else:
                raise AssertionError(f"PyArrow accepted {name}")

for name, wire in cases.items():
    (OUT / f"{name}.parquet").write_bytes(wire)

offsets = [dict_page.header, plain_page.header, raw_page.header, member_page.header, reentry_offset,
           v1_frames[1].header, geometry["v2-crc"][0][1].header, geometry["v2-crc"][0][4].header,
           dict_expected, dict_actual, plain_expected, plain_actual]
subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                "--run", str(HERE / "Emit.lean"), str(OUT), *map(str, offsets)], cwd=ROOT, check=True)

outputs = ["v2-crc", "v2-absent", "compressed-tail"]
for name in outputs:
    with pq.ParquetFile(OUT / f"{name}.parquet", page_checksum_verification=True) as source, \
            pa.ipc.open_stream(OUT / f"{name}.arrows") as reader:
        assert reader.schema == pa.schema([pa.field("blob", pa.binary_view())])
        assert [batch.column(0).to_pylist() for batch in reader] == [
            source.read_row_group(group, columns=["blob"]).column(0).to_pylist()
            for group in range(source.num_row_groups)]

artifacts = [OUT / f"{name}.parquet" for name in cases] + [OUT / f"{name}.arrows" for name in outputs]
pins = {path.name: sha256(path.read_bytes()).hexdigest() for path in artifacts}
print(json.dumps(pins, indent=2), flush=True)
assert pins == json.loads((HERE / "fixtures.json").read_text())
print("PyArrow/Thrift: exact V2 levels, both suffix flags on both tags, BinaryView and pin replay")
