"""Pin producer Snappy STRING pages and checked native Utf8View output."""

from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
from runpy import run_path
import struct
import subprocess
import sys
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
groups = [
    [None, "", "é", "e\u0301", "雪🙂", "a\x00b", "k", None],
    [""],
    ["雪🙂" * 30] * 4 + ["界"],
]
page_rows = 4


def produce(page_version, crc, mode="SNAPPY", dictionary=False, nullable=True):
    schema = pa.schema([pa.field("row_id", pa.int32(), nullable=False),
                        pa.field("label", pa.string(), nullable=nullable)])
    sink = pa.BufferOutputStream()
    options = {} if dictionary else {"column_encoding": "PLAIN"}
    with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=page_version,
                          compression=mode, use_dictionary=dictionary, write_batch_size=page_rows,
                          data_page_size=1, write_statistics=False,
                          write_page_checksum=crc, store_schema=False, **options) as writer:
        for group in groups:
            values = [value if value is not None or nullable else "雪" for value in group]
            writer.write_table(pa.Table.from_arrays([
                pa.array(range(len(values)), pa.int32()), pa.array(values, pa.string()),
            ], schema=schema))
    return sink.getvalue().to_pybytes()


def inspect(wire, kind, has_crc, nullable=True):
    footer_size, = struct.unpack_from("<I", wire, len(wire)-8)
    footer_start = len(wire)-8-footer_size
    footer = thrift["read_struct"](TCompactProtocol(TMemoryBuffer(wire[footer_start:-8])))
    _, _, leaf = thrift["list_field"](footer, 2)
    assert leaf[1] == (TType.I32, 6) and leaf[3] == (TType.I32, int(nullable))
    assert leaf[6] == (TType.I32, 0)
    assert leaf[10] == (TType.STRUCT, {1: (TType.STRUCT, {})})
    result = []
    flags = set()
    with pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True) as file:
        assert file.schema_arrow.field("label") == pa.field("label", pa.string(), nullable=nullable)
        assert [file.metadata.row_group(i).num_rows for i in range(file.num_row_groups)] == [8, 1, 5]
        for group_index, group in enumerate(groups):
            values = [value if value is not None or nullable else "雪" for value in group]
            assert file.read_row_group(group_index, columns=["label"]).column(0).to_pylist() == values
            chunk = file.metadata.row_group(group_index).column(1)
            assert chunk.compression == "SNAPPY" and not chunk.has_dictionary_page
            assert chunk.path_in_schema == "label"
            header_start = chunk.data_page_offset
            stop = header_start + chunk.total_compressed_size
            assert 4 <= header_start < stop <= footer_start
            for row in range(0, len(values), page_rows):
                slots = values[row:row+page_rows]
                memory = TMemoryBuffer(wire[header_start:stop])
                header = thrift["read_struct"](TCompactProtocol(memory))
                body_start = header_start + memory.cstringio_buf.tell()
                csize, usize = header[3][1], header[2][1]
                end = body_start + csize
                assert header[1] == (TType.I32, kind) and end <= stop
                body = wire[body_start:end]
                assert has_crc == (4 in header)
                if has_crc:
                    assert header[4][1] % 2**32 == crc32(body)
                if kind == 0:
                    fields = header[5][1]
                    assert [fields[k][1] for k in range(1, 5)] == [len(slots), 0, 3, 3]
                    expanded = codec.decompress(body, usize).to_pybytes()
                    levels = 4 + struct.unpack_from("<I", expanded)[0] if nullable else 0
                    plain = expanded[levels:]
                    compressed = True
                    suffix_start = body_start
                else:
                    fields = header[8][1]
                    assert [fields[k][1] for k in (1, 2, 3, 4, 6)] == [
                        len(slots), slots.count(None), len(slots), 0, 0,
                    ]
                    levels = fields[5][1]
                    assert 0 <= levels <= min(csize, usize)
                    compressed = fields.get(7, (TType.BOOL, True))[1]
                    suffix = body[levels:]
                    if compressed:
                        plain = codec.decompress(suffix, usize-levels).to_pybytes()
                    else:
                        assert len(suffix) == usize - levels
                        plain = suffix
                    suffix_start = body_start + levels
                flags.add(compressed)
                expected = b"".join(struct.pack("<I", len(x)) + x
                                    for x in (value.encode() for value in slots if value is not None))
                assert plain == expected
                result.append((group_index, row // page_rows, header_start, csize, usize,
                               compressed, body_start, suffix_start, end))
                header_start = end
            assert header_start == stop
    return result, flags


cases = {}
geometry = {}
for page_version, kind in (("1.0", 0), ("2.0", 3)):
    for crc in (False, True):
        name = f"v{page_version[0]}-{'crc' if crc else 'absent'}"
        wire = produce(page_version, crc)
        frames, flags = inspect(wire, kind, crc)
        assert flags == ({True} if kind == 0 else {True, False})
        cases[name], geometry[name] = wire, frames
required = produce("2.0", True, nullable=False)
inspect(required, 3, True, nullable=False)
cases["required"] = required


def damage(wire, frames):
    group, page, header, _, _, compressed, body, suffix, end = frames[-1]
    assert (group, page) == (2, 1) and not compressed
    assert wire[suffix+4:end] == "界".encode()
    changed = wire[:suffix+4] + b"\xff" + wire[suffix+5:]
    return changed, header, crc32(wire[body:end]), crc32(changed[body:end])


cases["bad-text"], text_offset, _, _ = damage(cases["v2-absent"], geometry["v2-absent"])
cases["bad-crc"], crc_offset, expected_crc, actual_crc = damage(cases["v2-crc"], geometry["v2-crc"])
for file, crc_check in (("bad-text", False), ("bad-crc", True)):
    with pq.ParquetFile(pa.BufferReader(cases[file]), page_checksum_verification=crc_check) as parquet:
        assert [parquet.read_row_group(i, columns=["label"]).column(0).to_pylist() for i in range(2)] == groups[:2]
        try:
            parquet.read_row_group(2, columns=["label"]).validate(full=True)
        except (OSError, ValueError):
            pass
        else:
            raise AssertionError(f"PyArrow accepted {file}")

cases["plain"] = produce("2.0", False, mode="NONE")
cases["dictionary"] = produce("2.0", False, dictionary=["label"])
for name, wire in cases.items():
    (out / f"{name}.parquet").write_bytes(wire)
frames = geometry["v2-crc"]
first_late = next(frame for frame in frames if frame[:2] == (2, 0))
cap = max(first_late[3], max(max(frame[3:5]) for frame in frames if frame[0] < 2))
assert first_late[3] <= cap < first_late[4]
coordinates = [first_late[2], cap, crc_offset, text_offset, expected_crc, actual_crc]
print(f"Thrift checked CRC and source geometry {coordinates}", flush=True)

subprocess.run(
    [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
     "--run", str(here / "Emit.lean"), str(out), *map(str, coordinates)], cwd=root, check=True,
)
positive = ("v1-absent", "v1-crc", "v2-absent", "v2-crc", "required")
for name in positive:
    wire = (out / f"{name}.arrows").read_bytes()
    carrier = pa.BufferReader(wire)
    assert wire.endswith(b"\xff\xff\xff\xff\x00\x00\x00\x00")
    with pq.ParquetFile(out / f"{name}.parquet") as file, pa.ipc.open_stream(carrier) as reader:
        assert reader.schema == pa.schema([pa.field("label", pa.string_view(), nullable=name != "required")])
        for index, batch in zip(range(file.num_row_groups), reader, strict=True):
            expected = file.read_row_group(index, columns=["label"]).column(0).to_pylist()
            assert batch.num_rows == len(expected) and batch.column(0).to_pylist() == expected
        assert carrier.tell() == len(wire)
for refused in cases.keys() - set(positive):
    assert not (out / f"{refused}.arrows").exists()
artifacts = [out / f"{name}.parquet" for name in cases]
artifacts += [out / f"{name}.arrows" for name in positive]
pins = {path.name: sha256(path.read_bytes()).hexdigest() for path in artifacts}
assert pins == json.loads((here / "fixtures.json").read_text(encoding="utf-8")), pins
print(json.dumps(pins, indent=2))
