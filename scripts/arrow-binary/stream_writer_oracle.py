#!/usr/bin/env python3
"""Open checked Lean plain Binary V5 streams in pinned PyArrow."""
import argparse
import hashlib
from pathlib import Path
import struct
import subprocess
import sys

import pyarrow as pa


ROOT = Path(__file__).resolve().parents[2]
EOS = b"\xff\xff\xff\xff\x00\x00\x00\x00"
CASES = {
    "nullable": ("payload", True, [
        [None, b"", b"\xff\x00\x80", None, b"x\x00z", b"", None, b"*", b"\xfe", None],
        [], [None, None], [b""],
    ]),
    "required": ("raw_雪", False, [[b"", b"\x00\xff\x81"]]),
    "schema_only": ("raw_雪", False, []),
    "empty_batch": ("raw_雪", False, [[]]),
}


def verify(wire, name, nullable, expected):
    expected_schema = pa.schema([pa.field(name, pa.binary(), nullable=nullable)])
    with pa.ipc.open_stream(wire) as reader:
        assert reader.schema.equals(expected_schema, check_metadata=True)
        records = list(reader)
    assert [batch.num_rows for batch in records] == [len(values) for values in expected]
    for batch, values in zip(records, expected, strict=True):
        batch.validate(full=True)
        assert batch.column(0).to_pylist() == values

    messages = list(pa.ipc.MessageReader.open_stream(wire))
    assert [message.type for message in messages] == ["schema"] + ["record batch"] * len(expected)
    offset = 0
    ranges = []
    for message in messages:
        assert message.metadata_version == pa.ipc.MetadataVersion.V5
        size = message.metadata.size
        body_size = message.body.size if message.body is not None else 0
        assert struct.unpack_from("<II", wire, offset) == (0xFFFFFFFF, size)
        if message.type == "record batch":
            ranges.append((offset, size, body_size))
        offset += 8 + size + body_size
    assert wire[offset:] == EOS
    return ranges, offset


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    if (sys.byteorder != "little" or pa.__version__ != "26.0.1"
            or pa.cpp_build_info.version != "26.0.1"):
        raise SystemExit("oracle requires little-endian PyArrow 26.0.1")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    subprocess.run(
        ["lake", "env", "lean", "-DwarningAsError=true", "--run",
         "scripts/arrow-binary/WriteStream.lean", str(output)],
        cwd=ROOT, check=True,
    )
    for case, (name, nullable, expected) in CASES.items():
        wire = (output / f"{case}.arrows").read_bytes()
        ranges, eos = verify(wire, name, nullable, expected)
        print(f"{case}: SHA-256 {hashlib.sha256(wire).hexdigest()}, records {ranges}, EOS {eos}")


if __name__ == "__main__":
    main()
