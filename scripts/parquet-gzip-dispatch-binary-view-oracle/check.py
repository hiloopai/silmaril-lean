"""Pin native mixed GZIP row groups and compare Lean BinaryView with PyArrow."""

from hashlib import sha256
import json
import os
from pathlib import Path
from runpy import run_path
import subprocess
import sys
from zlib import crc32

import pyarrow as pa
import pyarrow.parquet as pq


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUT = Path(sys.argv[1]).resolve()
OUT.mkdir(parents=True, exist_ok=True)
PHYSICAL = run_path(str(HERE.parent / "parquet-gzip-dictionary-binary-view-oracle/check.py"))
ROWS = [
    [b"", None, b"\xff\x00", b"\xed\xa0\x80"] * 10,
    [b"", None, b"\xff\x00", b"\xed\xa0\x80"] * 8
    + [None if index % 13 == 0 else b"\x80\x00" + bytes([index]) + b"long" * 5 for index in range(32)],
    [b"\xfe\x00", b"", None, b"opaque\xff"] * 12,
]
TAGS = [[8] * 5, [8] * 5 + [0] * 3, [8] * 6]


def produce(crc):
    schema = pa.schema([pa.field("ordinal", pa.int32(), nullable=False), pa.field("blob", pa.binary())])
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", compression="GZIP", data_page_version="1.0",
                          use_dictionary=["blob"], data_page_size=16, dictionary_pagesize_limit=64,
                          write_batch_size=8, write_statistics=False, store_schema=False,
                          write_page_checksum=crc) as writer:
        for rows in ROWS[:3 if crc else 2]:
            writer.write_table(pa.Table.from_arrays(
                [pa.array(range(len(rows)), pa.int32()), pa.array(rows, pa.binary())], schema=schema))
    return sink.getvalue().to_pybytes()


def inspect(wire, crc):
    footer_start, footer = PHYSICAL["read_footer"](wire)
    leaf = PHYSICAL["THRIFT"]["list_field"](footer, 2)[2]
    assert leaf[1][1] == 6 and leaf[3][1] == 1 and 6 not in leaf and 10 not in leaf
    geometry = []
    with pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True) as file:
        assert file.num_row_groups == (3 if crc else 2)
        assert file.schema_arrow.field("blob") == pa.field("blob", pa.binary())
        for group in range(file.num_row_groups):
            rows = ROWS[group]
            assert file.read_row_group(group, columns=["blob"]).column(0).to_pylist() == rows
            column = file.metadata.row_group(group).column(1)
            assert column.compression == "GZIP" and column.path_in_schema == "blob"
            assert set(column.encodings) == {"PLAIN", "RLE", "RLE_DICTIONARY"}
            dictionary, *data = PHYSICAL["frames"](wire, column, crc)
            assert dictionary.fields[1][1] == 2 and dictionary.fields[7][1][2][1] == 0
            assert data[-1].stop <= footer_start
            for frame in [dictionary, *data]:
                assert len(PHYSICAL["expand"](wire[frame.body:frame.stop])) == frame.fields[2][1]
            assert all(frame.fields[1][1] == 0 and frame.fields[5][1][3][1] == frame.fields[5][1][4][1] == 3
                       for frame in data)
            tags = [frame.fields[5][1][2][1] for frame in data]
            assert tags == TAGS[group] and sum(frame.fields[5][1][1][1] for frame in data) == len(rows)
            geometry.append([dictionary, *data])
            print(f"V1 CRC={crc} group {group}: original tags {tags}, {len(rows)} rows", flush=True)
    return geometry


def corrupt_crc(wire, frame):
    changed = wire[:frame.body] + bytes([wire[frame.body] ^ 1]) + wire[frame.body + 1:]
    assert crc32(changed[frame.body:frame.stop]) != frame.fields[4][1] % 2**32
    return changed


cases = {"mixed-crc": produce(True), "mixed-absent": produce(False)}
crc_wire = cases["mixed-crc"]
crc_frames = inspect(crc_wire, True)
member_wire = cases["mixed-absent"]
member_frames = inspect(member_wire, False)
dictionary_page, plain_page = crc_frames[2][-1], crc_frames[1][-1]
cases["late-dictionary-crc"] = corrupt_crc(crc_wire, dictionary_page)
cases["double-crc"] = corrupt_crc(cases["late-dictionary-crc"], plain_page)
member_page = member_frames[1][-1]
cases["late-fallback-member"] = PHYSICAL["add_member"](member_wire, member_page)

last_dictionary, first_plain = crc_frames[1][5:7]
assert last_dictionary.stop == first_plain.header
dictionary_frame = crc_wire[last_dictionary.header:last_dictionary.stop]
plain_frame = crc_wire[first_plain.header:first_plain.stop]
cases["reentry"] = (crc_wire[:last_dictionary.header] + plain_frame + dictionary_frame
                    + crc_wire[first_plain.stop:])
reentry_offset = last_dictionary.header + len(plain_frame)

for name in ("late-dictionary-crc", "double-crc", "late-fallback-member", "reentry"):
    with pq.ParquetFile(pa.BufferReader(cases[name]), page_checksum_verification=True) as file:
        prefix = 2 if name == "late-dictionary-crc" else 1
        assert [file.read_row_group(group, columns=["blob"]).column(0).to_pylist()
                for group in range(prefix)] == ROWS[:prefix]
        if name in ("late-dictionary-crc", "double-crc"):
            try:
                file.read_row_group(prefix, columns=["blob"])
            except OSError:
                pass
            else:
                raise AssertionError("PyArrow admitted a changed stored page CRC")
        if name == "reentry":
            frames = PHYSICAL["frames"](cases[name], file.metadata.row_group(1).column(1), True)
            assert [frame.fields[5][1][2][1] for frame in frames[1:]] == [8] * 4 + [0, 8, 0, 0]
            assert frames[6].header == reentry_offset

for name, wire in cases.items():
    (OUT / f"{name}.parquet").write_bytes(wire)

offsets = [dictionary_page.header, plain_page.header, member_page.header, reentry_offset,
           crc_frames[1][6].header]
subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                "--run", str(HERE / "Emit.lean"), str(OUT), *map(str, offsets)], cwd=ROOT, check=True)

outputs = ["mixed-crc", "mixed-absent"]
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
print("PyArrow/Thrift: mixed original groups, complete GZIP members, exact BinaryView and pin replay")
