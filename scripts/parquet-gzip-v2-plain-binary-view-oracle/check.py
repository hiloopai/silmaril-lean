"""Pin native PLAIN-only GZIP V2 files and verify Lean BinaryView readback."""

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
ROWS = [
    [None if index % 7 == 3 else b"\xff\x00" + bytes([group]) + b"payload" * 6 for index in range(count)]
    + ([b""] if group == 0 else [b"\xfe"])
    for group, count in enumerate((64, 32))
]
COMPRESSED_TAIL = [ROWS[0], ROWS[1][:-1]]


def produce(groups, crc, version="2.0"):
    schema = pa.schema([pa.field("ordinal", pa.int32(), nullable=False), pa.field("blob", pa.binary())])
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", compression="GZIP", data_page_version=version,
                          use_dictionary=False, column_encoding="PLAIN", data_page_size=1, write_batch_size=32,
                          write_statistics=False, store_schema=False, write_page_checksum=crc) as writer:
        for rows in groups:
            table = pa.Table.from_arrays([pa.array(range(len(rows)), pa.int32()), pa.array(rows, pa.binary())],
                                         schema=schema)
            writer.write_table(table)
    return sink.getvalue().to_pybytes()


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
            assert set(column.encodings) == {"PLAIN", "RLE"}
            assert not column.has_dictionary_page and column.dictionary_page_offset is None
            frames = PHYSICAL["frames"](wire, column, crc)
            assert frames[-1].stop <= footer_start
            flags = []
            parts = [rows[index:index + 32] for index in range(0, len(rows), 32)]
            for frame, part in zip(frames, parts, strict=True):
                assert frame.fields[1][1] == 3
                fields = frame.fields[8][1]
                assert [fields[i][1] for i in (1, 2, 3, 4, 6)] == [len(part), part.count(None), len(part), 0, 0]
                levels = fields[5][1]
                assert 0 < levels <= min(frame.fields[2][1], frame.fields[3][1])
                split = frame.body + levels
                assert HYBRID(wire[frame.body:split], 1, len(part)) == [int(value is not None) for value in part]
                flag = fields[7][1]
                flags.append(flag)
                suffix = wire[split:frame.stop]
                decoded = PHYSICAL["expand"](suffix) if flag else suffix
                assert len(decoded) == frame.fields[2][1] - levels
                assert decoded == b"".join(pack("<I", len(value)) + value for value in part if value is not None)
            assert flags == [len(part) == 32 for part in parts]
            geometry.append(frames)
            print(f"PLAIN V2 CRC={crc} group {group}: flags {flags}, {len(rows)} rows, no dictionary", flush=True)
    return geometry


cases = {}
geometry = {}
for name, groups, crc in [("v2-crc", ROWS, True), ("v2-absent", ROWS, False),
                          ("compressed-tail", COMPRESSED_TAIL, False)]:
    cases[name] = produce(groups, crc)
    geometry[name] = inspect(cases[name], groups, crc)

crc_page = geometry["v2-crc"][1][0]
crc_wire = cases["v2-crc"]
cases["bad-level-crc"] = crc_wire[:crc_page.body] + bytes([crc_wire[crc_page.body] ^ 1]) + crc_wire[crc_page.body + 1:]
expected_crc = crc_page.fields[4][1] % 2**32
actual_crc = crc32(cases["bad-level-crc"][crc_page.body:crc_page.stop])
assert actual_crc != expected_crc

raw_page = geometry["v2-absent"][1][-1]
raw_wire = cases["v2-absent"]
raw_offset = raw_page.body + raw_page.fields[8][1][5][1]
assert raw_page.fields[8][1][7][1] is False and raw_wire[raw_offset:raw_page.stop] == pack("<I", 1) + b"\xfe"
cases["bad-raw-length"] = raw_wire[:raw_offset] + pack("<I", 2**31) + raw_wire[raw_offset + 4:]

member_page = geometry["compressed-tail"][1][-1]
assert member_page.fields[8][1][7][1]
cases["extra-member"] = PHYSICAL["add_member"](cases["compressed-tail"], member_page)
with pq.ParquetFile(pa.BufferReader(cases["extra-member"])) as file:
    frame = PHYSICAL["frames"](cases["extra-member"], file.metadata.row_group(1).column(1), False)[-1]
    levels = frame.fields[8][1][5][1]
    decoder = decompressobj(wbits=31)
    decoded = decoder.decompress(cases["extra-member"][frame.body + levels:frame.stop])
    assert decoder.eof and PHYSICAL["expand"](decoder.unused_data) == b""
    assert len(decoded) == frame.fields[2][1] - levels

cases["dictionary"] = PHYSICAL["produce"]("2.0", True)
dictionary_frames = PHYSICAL["inspect"](cases["dictionary"], "2.0", True)
cases["v1"] = produce(ROWS, True, "1.0")
with pq.ParquetFile(pa.BufferReader(cases["v1"]), page_checksum_verification=True) as file:
    assert file.read_row_group(0, columns=["blob"]).column(0).to_pylist() == ROWS[0]
    v1_frames = PHYSICAL["frames"](cases["v1"], file.metadata.row_group(0).column(1), True)
    assert all(frame.fields[1][1] == 0 and frame.fields[5][1][2][1] == 0 for frame in v1_frames)

for name in ("bad-level-crc", "bad-raw-length", "extra-member"):
    with pq.ParquetFile(pa.BufferReader(cases[name]), page_checksum_verification=True) as file:
        assert file.read_row_group(0, columns=["blob"]).column(0).to_pylist() == ROWS[0]
        if name != "extra-member":
            try:
                file.read_row_group(1, columns=["blob"])
            except (OSError, ValueError):
                pass
            else:
                raise AssertionError(f"PyArrow accepted {name}")

for name, wire in cases.items():
    (OUT / f"{name}.parquet").write_bytes(wire)

offsets = [crc_page.header, raw_page.header, member_page.header, v1_frames[0].header,
           dictionary_frames[0][0].header, geometry["v2-crc"][0][0].header, expected_crc, actual_crc]
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
print("PyArrow/Thrift: dictionary-free V2 frames, original raw levels and exact PLAIN suffixes, BinaryView pin replay")
