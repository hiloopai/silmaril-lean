"""Pin real PyArrow GZIP fallback files and compare native Lean BinaryView IPC."""

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
    [b"", None, b"\xff\x00", b"\xed\xa0\x80"] * 8
    + [None if index % 13 == 0 else b"\x80\x00" + bytes([group, index]) + b"long" * 5
       for index in range(32 + 8 * group)]
    for group in range(2)
]


def produce(version, crc):
    schema = pa.schema([pa.field("ordinal", pa.int32(), nullable=False), pa.field("blob", pa.binary())])
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", compression="GZIP", data_page_version=version,
                          use_dictionary=["blob"], data_page_size=16, dictionary_pagesize_limit=64,
                          write_batch_size=8, write_statistics=False, store_schema=False,
                          write_page_checksum=crc) as writer:
        for rows in ROWS:
            writer.write_table(pa.Table.from_arrays(
                [pa.array(range(len(rows)), pa.int32()), pa.array(rows, pa.binary())], schema=schema))
    return sink.getvalue().to_pybytes()


def inspect(wire, version, crc):
    footer_start, footer = PHYSICAL["read_footer"](wire)
    thrift = PHYSICAL["THRIFT"]
    leaf = thrift["list_field"](footer, 2)[2]
    assert leaf[1][1] == 6 and leaf[3][1] == 1 and 6 not in leaf and 10 not in leaf
    geometry = []
    with pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True) as file:
        assert file.num_row_groups == len(ROWS) and file.schema_arrow.field("blob") == pa.field("blob", pa.binary())
        for group, rows in enumerate(ROWS):
            assert file.read_row_group(group, columns=["blob"]).column(0).to_pylist() == rows
            column = file.metadata.row_group(group).column(1)
            assert column.compression == "GZIP" and column.path_in_schema == "blob"
            assert set(column.encodings) == {"PLAIN", "RLE", "RLE_DICTIONARY"}
            dictionary, *data = PHYSICAL["frames"](wire, column, crc)
            assert data[-1].stop <= footer_start and dictionary.fields[1][1] == 2
            assert dictionary.fields[7][1][2][1] == 0
            assert len(PHYSICAL["expand"](wire[dictionary.body:dictionary.stop])) == dictionary.fields[2][1]
            page_type, details, count_field, tag_field = (0, 5, 1, 2) if version == "1.0" else (3, 8, 1, 4)
            tags = []
            count = 0
            for frame in data:
                fields = frame.fields[details][1]
                assert frame.fields[1][1] == page_type
                if version == "1.0":
                    assert fields[3][1] == fields[4][1] == 3
                    assert len(PHYSICAL["expand"](wire[frame.body:frame.stop])) == frame.fields[2][1]
                tags.append(fields[tag_field][1])
                count += fields[count_field][1]
            assert tags == [8] * 5 + [0] * (3 + group) and count == len(rows)
            print(f"V{version} CRC={crc} group {group}: data tags {tags}, {count} rows", flush=True)
            geometry.append([dictionary, *data])
    return geometry


def reenter(wire, last_dictionary, first_plain):
    assert last_dictionary.stop == first_plain.header
    dictionary = wire[last_dictionary.header:last_dictionary.stop]
    plain = wire[first_plain.header:first_plain.stop]
    return (wire[:last_dictionary.header] + plain + dictionary + wire[first_plain.stop:],
            last_dictionary.header + len(plain))


cases = {}
geometry = {}
for name, version, crc in [("v1-crc", "1.0", True), ("v1-absent", "1.0", False), ("v2", "2.0", True)]:
    cases[name] = produce(version, crc)
    geometry[name] = inspect(cases[name], version, crc)

cases["dictionary-only"] = PHYSICAL["produce"]("1.0", True)
PHYSICAL["inspect"](cases["dictionary-only"], "1.0", True)

crc_frame = geometry["v1-crc"][1][-1]
crc_wire = cases["v1-crc"]
cases["bad-crc"] = crc_wire[:crc_frame.body] + bytes([crc_wire[crc_frame.body] ^ 1]) + crc_wire[crc_frame.body + 1:]
expected_crc = crc_frame.fields[4][1] % 2**32
actual_crc = crc32(cases["bad-crc"][crc_frame.body:crc_frame.stop])
assert actual_crc != expected_crc
member_frame = geometry["v1-absent"][1][-1]
cases["extra-member"] = PHYSICAL["add_member"](cases["v1-absent"], member_frame)
cases["reentry"], reentry_offset = reenter(crc_wire, *geometry["v1-crc"][1][5:7])
for name in ("bad-crc", "extra-member", "reentry"):
    with pq.ParquetFile(pa.BufferReader(cases[name]), page_checksum_verification=True) as file:
        assert file.read_row_group(0, columns=["blob"]).column(0).to_pylist() == ROWS[0]
        if name == "reentry":
            # The moved frames keep their original payloads and valid CRCs.
            frames = PHYSICAL["frames"](cases[name], file.metadata.row_group(1).column(1), True)
            assert [frame.fields[5][1][2][1] for frame in frames[1:]] == [8] * 4 + [0, 8] + [0] * 3
            assert frames[6].header == reentry_offset

for name, wire in cases.items():
    (OUT / f"{name}.parquet").write_bytes(wire)

offsets = [crc_frame.header, member_frame.header, reentry_offset, geometry["v2"][0][1].header,
           geometry["v1-crc"][0][0].header, geometry["v1-crc"][0][6].header, expected_crc, actual_crc]
subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                "--run", str(HERE / "Emit.lean"), str(OUT), *map(str, offsets)], cwd=ROOT, check=True)
outputs = ["v1-crc", "v1-absent"]
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
print("PyArrow/Thrift: original fallback tags and complete GZIP members, exact BinaryView rows and pin replay")
