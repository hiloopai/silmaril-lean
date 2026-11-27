"""Compare the native Utf8View-to-Parquet writer with pinned PyArrow and Thrift."""

from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
from runpy import run_path
import struct
import subprocess
import sys

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
i32 = TType.I32
i64 = TType.I64
marker = TType.STRUCT

long_text = "snow雪pinned🙂é"
cases = {
    "optional": ("étiquette", True, [[None, "", "é", "e\u0301", "雪🙂"], [], [None, long_text, "a\x00b", "界"]]),
    "required": ("必須", False, [["雪", ""], [], ["e\u0301", "🙂"]]),
    "schema-only": ("texte", True, []),
}


def make_ipc(name, kind, nullable, groups):
    schema = pa.schema([pa.field(name, kind, nullable=nullable)])
    output = pa.BufferOutputStream()
    opts = pa.ipc.IpcWriteOptions(metadata_version=pa.ipc.MetadataVersion.V5, compression=None)
    with pa.ipc.new_stream(output, schema, options=opts) as writer:
        for group in groups:
            writer.write_batch(pa.record_batch([pa.array(group, type=kind)], schema=schema))
    return output.getvalue().to_pybytes()


inputs = {key: make_ipc(name, pa.string_view(), nullable, groups)
          for key, (name, nullable, groups) in cases.items()}
inputs["binary"] = make_ipc("étiquette", pa.binary_view(), True, [["é".encode()]])
optional = inputs["optional"]
assert optional[-8:] == b"\xff\xff\xff\xff\x00\x00\x00\x00"
inputs["truncated"] = optional[:-8]
target = long_text.encode()
assert optional.count(target) == 1
offset = optional.index(target) + 5
inputs["bad-text"] = optional[:offset] + b"\xff" + optional[offset+1:]
with pa.ipc.open_stream(inputs["bad-text"]) as reader:
    assert [reader.read_next_batch().num_rows for _ in range(2)] == [5, 0]
    try:
        reader.read_next_batch().validate(full=True)
    except pa.ArrowInvalid:
        pass
    else:
        raise AssertionError("PyArrow admitted invalid UTF-8 in the last input batch")
for key, wire in inputs.items():
    (out / f"{key}.arrows").write_bytes(wire)

subprocess.run(
    [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
     "--run", str(here / "Emit.lean"), str(out)], cwd=root, check=True,
)


def inspect(wire, name, nullable, groups):
    size, = struct.unpack_from("<I", wire, len(wire) - 8)
    footer_start = len(wire) - 8 - size
    assert wire[:4] == wire[-4:] == b"PAR1"
    memory = TMemoryBuffer(wire[footer_start:-8])
    footer = thrift["read_struct"](TCompactProtocol(memory))
    assert memory.cstringio_buf.tell() == size
    root_leaf, leaf = thrift["list_field"](footer, 2)
    assert root_leaf[5] == (i32, 1)
    assert leaf == {
        1: (i32, 6), 3: (i32, int(nullable)), 4: (TType.STRING, name.encode()),
        6: (i32, 0), 10: (marker, {1: (marker, {})}),
    }
    assert footer[3] == (i64, sum(map(len, groups)))
    next_page = 4
    for index, (group, row_group) in enumerate(zip(groups, thrift["list_field"](footer, 4), strict=True)):
        assert row_group[3] == (i64, len(group))
        chunk = thrift["column_metadata"](footer, group=index, column=0)
        assert chunk[1] == (i32, 6) and chunk[4] == (i32, 0)
        assert chunk[2] == (TType.LIST, (i32, [0, 3]))
        assert chunk[3] == (TType.LIST, (TType.STRING, [name.encode()]))
        assert chunk[5] == (i64, len(group))
        assert chunk[6] == chunk[7] and chunk[9] == (i64, next_page)
        end = next_page + chunk[7][1]
        memory = TMemoryBuffer(wire[next_page:end])
        header = thrift["read_struct"](TCompactProtocol(memory))
        assert header[1] == (i32, 0) and 4 not in header
        assert header[2] == header[3]
        assert header[5] == (marker, {1: (i32, len(group)), 2: (i32, 0), 3: (i32, 3), 4: (i32, 3)})
        body = memory.readAll(header[3][1])
        assert memory.cstringio_buf.tell() == end - next_page
        levels = b"".join(bytes((2, int(value is not None))) for value in group)
        scalar = b"".join(struct.pack("<I", len(octets)) + octets
                          for octets in (value.encode() for value in group if value is not None))
        prefix = struct.pack("<I", len(levels)) + levels if nullable else b""
        assert body == prefix + scalar
        next_page = end
    assert next_page == footer_start
    with pq.ParquetFile(pa.BufferReader(wire)) as file:
        assert file.schema_arrow == pa.schema([pa.field(name, pa.string(), nullable=nullable)])
        assert file.num_row_groups == len(groups)
        assert [file.read_row_group(i).column(0).to_pylist() for i in range(file.num_row_groups)] == groups


for key, (name, nullable, groups) in cases.items():
    inspect((out / f"{key}.parquet").read_bytes(), name, nullable, groups)
for refused in inputs.keys() - cases.keys():
    assert not (out / f"{refused}.parquet").exists()
artifacts = [out / f"{key}.arrows" for key in inputs]
artifacts += [out / f"{key}.parquet" for key in cases]
digests = {path.name: sha256(path.read_bytes()).hexdigest() for path in artifacts}
assert digests == json.loads((here / "fixtures.json").read_text(encoding="utf-8"))
for name, digest in digests.items():
    print(f"{digest}  {name}")
print("PyArrow and Thrift matched all native PLAIN bodies, descriptors and row groups")
