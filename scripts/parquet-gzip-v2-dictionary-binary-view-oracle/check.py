"""Pin PyArrow opaque GZIP V2 dictionaries and compare native Lean BinaryView."""

from hashlib import sha256
import json
import os
from pathlib import Path
from runpy import run_path
from struct import pack
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
ENTRIES = [[b"", b"\xff\x00", b"\xed\xa0\x80", bytes([0xfe, group]) * 12, b"\xfe\x80unused"]
           for group in range(3)]
GROUPS = [[None if count == 128 or 16 <= i < 32 else i % 4 for i in range(count)]
          for count in (257, 129, 128)]
COMPRESSED_TAIL = [GROUPS[0], GROUPS[1][:128]]


def rows(group, indices):
    return [ENTRIES[group][index] if index is not None else None for index in indices]


def produce(groups, crc):
    schema = pa.schema([pa.field("ordinal", pa.int32(), nullable=False),
                        pa.field("blob", pa.dictionary(pa.int8(), pa.binary()))])
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, version="2.6", compression="GZIP", data_page_version="2.0",
                          use_dictionary=["blob"], write_batch_size=128, data_page_size=1,
                          write_statistics=False, store_schema=False, write_page_checksum=crc) as writer:
        for group, indices in enumerate(groups):
            array = pa.DictionaryArray.from_arrays(pa.array(indices, pa.int8()), pa.array(ENTRIES[group], pa.binary()))
            table = pa.Table.from_arrays([pa.array(range(len(indices)), pa.int32()), array], schema=schema)
            writer.write_table(table)
    return sink.getvalue().to_pybytes()


def inspect(wire, groups, crc):
    footer_start, footer = PHYSICAL["read_footer"](wire)
    leaf = PHYSICAL["THRIFT"]["list_field"](footer, 2)[2]
    assert leaf[1][1] == 6 and leaf[3][1] == 1 and 6 not in leaf and 10 not in leaf
    geometry = []
    with pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True) as file:
        assert file.num_row_groups == len(groups)
        assert file.schema_arrow.field("blob") == pa.field("blob", pa.binary())
        for group, indices in enumerate(groups):
            assert file.read_row_group(group, columns=["blob"]).column(0).to_pylist() == rows(group, indices)
            column = file.metadata.row_group(group).column(1)
            assert column.compression == "GZIP" and column.path_in_schema == "blob"
            assert set(column.encodings) == {"PLAIN", "RLE", "RLE_DICTIONARY"}
            dictionary, *data = PHYSICAL["frames"](wire, column, crc)
            assert data[-1].stop <= footer_start and dictionary.fields[1][1] == 2
            assert [dictionary.fields[7][1][i][1] for i in (1, 2)] == [len(ENTRIES[group]), 0]
            expanded = PHYSICAL["expand"](wire[dictionary.body:dictionary.stop])
            assert len(expanded) == dictionary.fields[2][1]
            assert expanded == b"".join(pack("<I", len(entry)) + entry for entry in ENTRIES[group])
            flags = []
            parts = [indices[i:i + 128] for i in range(0, len(indices), 128)]
            for part, frame in zip(parts, data, strict=True):
                assert frame.fields[1][1] == 3
                fields = frame.fields[8][1]
                assert [fields[i][1] for i in (1, 2, 3, 4, 6)] == [len(part), part.count(None), len(part), 8, 0]
                size, stored = frame.fields[2][1], frame.fields[3][1]
                level_bytes = fields[5][1]
                assert 0 < level_bytes <= min(size, stored)
                split = frame.body + level_bytes
                definitions, suffix = wire[frame.body:split], wire[split:frame.stop]
                assert HYBRID(definitions, 1, len(part)) == [int(index is not None) for index in part]
                flag = fields[7][1]
                flags.append(flag)
                decoded = PHYSICAL["expand"](suffix) if flag else suffix
                assert len(decoded) == size - level_bytes
                present = [index for index in part if index is not None]
                assert HYBRID(decoded[1:], decoded[0], len(present)) == present
            assert flags == [len(part) == 128 and any(index is not None for index in part) for part in parts]
            print(f"V2 CRC={crc} group {group}: flag sequence {flags}, {len(indices)} rows", flush=True)
            geometry.append([dictionary, *data])
    return geometry


def produce_fallback():
    values = [b"a", b"\xff\x00", None, b""] * 8 + [b"\x80" + bytes([i]) + b"long" * 5 for i in range(32)]
    sink = pa.BufferOutputStream()
    pq.write_table(pa.table({"ordinal": pa.array(range(64), pa.int32()), "blob": values}), sink,
                   version="2.6", compression="GZIP", data_page_version="2.0", use_dictionary=["blob"],
                   data_page_size=16, dictionary_pagesize_limit=64, write_batch_size=8,
                   write_statistics=False, store_schema=False, write_page_checksum=True)
    wire = sink.getvalue().to_pybytes()
    with pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True) as file:
        assert file.read_row_group(0, columns=["blob"]).column(0).to_pylist() == values
        frames = PHYSICAL["frames"](wire, file.metadata.row_group(0).column(1), True)
        assert [frame.fields[8][1][4][1] for frame in frames[1:]] == [8] * 5 + [0] * 3
        return wire, frames[6].header


cases = {}
geometry = {}
for name, groups, crc in [("v2-crc", GROUPS, True), ("v2-absent", GROUPS, False),
                          ("compressed-tail", COMPRESSED_TAIL, False)]:
    cases[name] = produce(groups, crc)
    geometry[name] = inspect(cases[name], groups, crc)

index_page = geometry["v2-absent"][1][-1]
index_wire = cases["v2-absent"]
assert index_wire[index_page.body + index_page.fields[8][1][5][1]:index_page.stop] == bytes([3, 2, 0])
cases["bad-raw-index"] = index_wire[:index_page.stop - 1] + b"\x07" + index_wire[index_page.stop:]

crc_page = geometry["v2-crc"][1][1]
crc_wire = cases["v2-crc"]
cases["bad-level-crc"] = crc_wire[:crc_page.body] + bytes([crc_wire[crc_page.body] ^ 1]) + crc_wire[crc_page.body + 1:]
expected_crc = crc_page.fields[4][1] % 2**32
actual_crc = crc32(cases["bad-level-crc"][crc_page.body:crc_page.stop])
assert actual_crc != expected_crc

member_page = geometry["compressed-tail"][1][-1]
assert member_page.fields[8][1][7][1]
cases["extra-member"] = PHYSICAL["add_member"](cases["compressed-tail"], member_page)
with pq.ParquetFile(pa.BufferReader(cases["extra-member"])) as file:
    original = PHYSICAL["frames"](cases["extra-member"], file.metadata.row_group(1).column(1), False)[-1]
    split = original.body + original.fields[8][1][5][1]
    decoder = decompressobj(wbits=31)
    decoded = decoder.decompress(cases["extra-member"][split:original.stop])
    assert decoder.eof and decoder.unused_data and PHYSICAL["expand"](decoder.unused_data) == b""
    assert len(decoded) == original.fields[2][1] - original.fields[8][1][5][1]

cases["fallback"], fallback_offset = produce_fallback()
cases["v1"] = PHYSICAL["produce"]("1.0", True)
v1_frames = PHYSICAL["inspect"](cases["v1"], "1.0", True)
for name in ("bad-raw-index", "bad-level-crc", "extra-member"):
    with pq.ParquetFile(pa.BufferReader(cases[name]), page_checksum_verification=True) as file:
        assert file.read_row_group(0, columns=["blob"]).column(0).to_pylist() == rows(0, GROUPS[0])
        if name != "extra-member":
            try:
                file.read_row_group(1, columns=["blob"])
            except (OSError, ValueError):
                pass
            else:
                raise AssertionError(f"PyArrow accepted {name}")

for name, wire in cases.items():
    (OUT / f"{name}.parquet").write_bytes(wire)

offsets = [index_page.header, crc_page.header, member_page.header, fallback_offset,
           v1_frames[0][1].header, geometry["v2-crc"][0][1].header, expected_crc, actual_crc]
subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                "--run", str(HERE / "Emit.lean"), str(OUT), *map(str, offsets)], cwd=ROOT, check=True)
outputs = ["v2-crc", "v2-absent", "compressed-tail"]
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
print("PyArrow/Thrift: original raw levels, both suffix flags, exact members and BinaryView pin replay")
