"""Pin native PLAIN-only Snappy V2 files and verify Lean BinaryView readback."""

from hashlib import sha256
from importlib.metadata import version
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


assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUT = Path(sys.argv[1]).resolve()
OUT.mkdir(parents=True, exist_ok=True)
PHYSICAL = run_path(str(HERE.parent / "parquet-gzip-dictionary-binary-view-oracle/check.py"))
HYBRID = run_path(str(HERE.parent / "parquet-timestamp-snappy-dictionary-oracle/check.py"))["hybrid"]
CODEC = pa.Codec("snappy")
ROWS = [
    [None if index % 7 == 3 else b"\xff\x00" + bytes([group]) + b"payload" * 6 for index in range(count)]
    + ([b""] if group == 0 else [b"\xfe"])
    for group, count in enumerate((64, 32))
] + [[None] * 32]
COMPRESSED_TAIL = [ROWS[0], ROWS[1][:-1]]


def produce(groups, crc, version="2.0", dictionary=False):
    schema = pa.schema([pa.field("ordinal", pa.int32(), nullable=False), pa.field("blob", pa.binary())])
    sink = pa.BufferOutputStream()
    options = {"use_dictionary": ["blob"]} if dictionary else {"use_dictionary": False, "column_encoding": "PLAIN"}
    with pq.ParquetWriter(sink, schema, version="2.6", compression={"blob": "SNAPPY", "ordinal": "NONE"}, data_page_version=version, data_page_size=1,
                          write_batch_size=32, write_statistics=False, store_schema=False,
                          write_page_checksum=crc, **options) as writer:
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
            assert column.compression == "SNAPPY" and column.path_in_schema == "blob"
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
                expected_size = frame.fields[2][1] - levels
                if flag:
                    decoded = CODEC.decompress(suffix, expected_size).to_pybytes()
                else:
                    decoded = suffix
                assert len(decoded) == expected_size
                assert decoded == b"".join(pack("<I", len(value)) + value for value in part if value is not None)
            assert flags == [len(part) == 32 and any(value is not None for value in part) for part in parts]
            geometry.append(frames)
            print(f"PLAIN V2 CRC={crc} group {group}: flags {flags}, {len(rows)} rows, no dictionary", flush=True)
    return geometry


cases = {}
geometry = {}
settings = [("v2-crc", ROWS, True), ("v2-absent", ROWS, False),
            ("compressed-tail", COMPRESSED_TAIL, False)]
for name, groups, crc in settings:
    cases[name] = produce(groups, crc)
    geometry[name] = inspect(cases[name], groups, crc)

# Corrupt only the original raw definition section, leaving the stored checksum.
crc_page = geometry["v2-crc"][1][0]
crc_wire = cases["v2-crc"]
cases["bad-level-crc"] = crc_wire[:crc_page.body] + bytes([crc_wire[crc_page.body] ^ 1]) + crc_wire[crc_page.body + 1:]
expected_crc = crc_page.fields[4][1] % 2**32
actual_crc = crc32(cases["bad-level-crc"][crc_page.body:crc_page.stop])
assert actual_crc != expected_crc

raw_page = geometry["v2-absent"][1][-1]
raw_wire = cases["v2-absent"]
raw_start = raw_page.body + raw_page.fields[8][1][5][1]
assert raw_page.fields[8][1][7][1] is False and raw_wire[raw_start:raw_page.stop] == pack("<I", 1) + b"\xfe"
cases["bad-raw-length"] = raw_wire[:raw_start] + pack("<I", 2**31) + raw_wire[raw_start + 4:]

# Append a complete second Snappy block to the last compressed value suffix.
last_page = geometry["compressed-tail"][1][-1]
tail = cases["compressed-tail"]
assert last_page.fields[8][1][7][1]
encoded = tail[last_page.body + last_page.fields[8][1][5][1]:last_page.stop]
cases["extra-block"] = PHYSICAL["append_payload"](tail, last_page, encoded)
with pq.ParquetFile(pa.BufferReader(cases["extra-block"])) as file:
    frame = PHYSICAL["frames"](cases["extra-block"], file.metadata.row_group(1).column(1), False)[-1]
    start = frame.body + frame.fields[8][1][5][1]
    suffix = cases["extra-block"][start:frame.stop]
    assert suffix == encoded + encoded
    expected = frame.fields[2][1] - frame.fields[8][1][5][1]
    assert CODEC.decompress(encoded, expected).to_pybytes() == b"".join(
        pack("<I", len(value)) + value for value in COMPRESSED_TAIL[1] if value is not None)
    try:
        CODEC.decompress(suffix, expected)
    except (OSError, ValueError):
        pass
    else:
        raise AssertionError("independent Snappy accepted the trailing block")

cases["dictionary"] = produce(ROWS, True, dictionary=True)
with pq.ParquetFile(pa.BufferReader(cases["dictionary"]), page_checksum_verification=True) as file:
    assert file.read_row_group(0, columns=["blob"]).column(0).to_pylist() == ROWS[0]
    dictionary = PHYSICAL["frames"](cases["dictionary"], file.metadata.row_group(0).column(1), True)[0]
    assert dictionary.fields[1][1] == 2 and dictionary.fields[7][1][2][1] == 0

cases["v1"] = produce(ROWS, True, "1.0")
with pq.ParquetFile(pa.BufferReader(cases["v1"]), page_checksum_verification=True) as file:
    assert file.read_row_group(0, columns=["blob"]).column(0).to_pylist() == ROWS[0]
    v1_frames = PHYSICAL["frames"](cases["v1"], file.metadata.row_group(0).column(1), True)
    assert all(frame.fields[1][1] == 0 and frame.fields[5][1][2][1] == 0 for frame in v1_frames)

sink = pa.BufferOutputStream()
pq.write_table(pa.table({"blob": pa.array(["雪", None, ""], pa.string())}), sink,
               compression="SNAPPY", data_page_version="2.0", use_dictionary=False,
               write_page_checksum=True, store_schema=False)
cases["string"] = sink.getvalue().to_pybytes()
_, string_footer = PHYSICAL["read_footer"](cases["string"])
assert 10 in PHYSICAL["THRIFT"]["list_field"](string_footer, 2)[1]

for name in ("bad-level-crc", "bad-raw-length", "extra-block"):
    with pq.ParquetFile(pa.BufferReader(cases[name]), page_checksum_verification=True) as file:
        assert file.read_row_group(0, columns=["blob"]).column(0).to_pylist() == ROWS[0]
        try:
            file.read_row_group(1, columns=["blob"])
        except (OSError, ValueError):
            pass
        else:
            raise AssertionError(f"PyArrow accepted {name}")

for name, wire in cases.items():
    (OUT / f"{name}.parquet").write_bytes(wire)

offsets = [crc_page.header, raw_page.header, last_page.header, v1_frames[0].header,
           dictionary.header, geometry["v2-crc"][0][0].header, expected_crc, actual_crc]
subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                "--run", str(HERE / "Emit.lean"), str(OUT), *map(str, offsets)], cwd=ROOT, check=True)

outputs = [name for name, _, _ in settings]
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
print("PyArrow/Thrift: native PLAIN Snappy V2, exact stored levels and suffixes, BinaryView pin replay")
