"""Compare ordered mixed-view IPC output with an independent pinned PyArrow stream."""

from hashlib import sha256
from importlib.metadata import version
import os
from pathlib import Path
import subprocess
import sys

import pyarrow as pa

assert version("pyarrow") == "26.0.1"
here = Path(__file__).resolve().parent
out = Path(sys.argv[1]).resolve()
out.mkdir(parents=True, exist_ok=True)

digests = {
    "pyarrow.arrows": "8bd50794f8b8ff15317897a1837a3f75c5a90c84eee149369383ba267a82e1f3",
    "lean.arrows": "740d13ee9272064f1ec1b0272db59b9aa460079a737070511c357e43267f2678",
}

schema = pa.schema([
    pa.field("text", pa.string_view()),
    pa.field("blob", pa.binary_view()),
    pa.field("ordinal", pa.int32(), nullable=False),
    pa.field("notes", pa.string_view(), nullable=False),
    pa.field("raw", pa.binary_view()),
])
columns = [
    [
        [None, "", "é" * 6, "a\x00b"],
        [b"\xff\x00", b"\xff\x00\xfe" + bytes(range(12)), None, b""],
        [-7, 0, 42, 2**31 - 1],
        ["é" * 7, "雪🙂e\u0301", "", "é"],
        ["é".encode(), None, b"", b"\x80"],
    ],
    [[], [], [], [], []],
    [
        ["雪" * 5, "e\u0301", "é"],
        [b"", b"\xff\xc3", None],
        [-(2**31), 2, 3],
        ["🙂" * 3, "雪", ""],
        [b"\xff\x00\xfe" + bytes([191]) * 13, None, b"\x00"],
    ],
]
batches = [
    pa.record_batch(
        [pa.array(values, type=field.type) for field, values in zip(schema, batch, strict=True)],
        schema=schema,
    )
    for batch in columns
]
sink = pa.BufferOutputStream()
options = pa.ipc.IpcWriteOptions(metadata_version=pa.ipc.MetadataVersion.V5, compression=None)
with pa.ipc.new_stream(sink, schema, options=options) as writer:
    for batch in batches:
        writer.write_batch(batch)
reference = sink.getvalue().to_pybytes()
assert sha256(reference).hexdigest() == digests["pyarrow.arrows"]
(out / "pyarrow.arrows").write_bytes(reference)

subprocess.run(
    [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
     "--run", str(here / "Check.lean"), str(out)],
    cwd=here.parents[1], check=True,
)
for name in ("pyarrow.arrows", "lean.arrows"):
    wire = (out / name).read_bytes()
    assert wire.endswith(b"\xff\xff\xff\xff\x00\x00\x00\x00")
    carrier = pa.BufferReader(wire)
    with pa.ipc.open_stream(carrier) as reader:
        assert reader.schema.equals(schema, check_metadata=True)
        for actual, expected in zip(reader, batches, strict=True):
            assert actual.equals(expected, check_metadata=True)
        assert carrier.tell() == len(wire)
    digest = sha256(wire).hexdigest()
    assert digest == digests[name]
    print(f"{digest}  {name}  [4, 0, 3]")
