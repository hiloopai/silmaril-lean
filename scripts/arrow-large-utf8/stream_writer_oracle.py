#!/usr/bin/env python3
"""Open checked Lean LargeUtf8 V5 streams in pinned PyArrow."""
import argparse
import hashlib
from itertools import accumulate
from pathlib import Path
import struct
import subprocess
import sys

import pyarrow as pa


ROOT = Path(__file__).resolve().parents[2]
EOS = b"\xff\xff\xff\xff\x00\x00\x00\x00"
CASES = {
    "nullable": ("text", True, [
        [None, "", "é雪🙂", None, "x\x00z", "", None, "a", "𐍈", None],
        [], [None, None], [""],
    ]),
    "required": ("text_雪", False, [["", "ééééé"]]),
    "schema_only": ("text_雪", False, []),
    "empty_batch": ("text_雪", False, [[]]),
}

SHA256 = {
    "nullable": "048970ba7b0d63adc24f9f2744c049bfea9a2ce47f31bdc05ec57c9d755e4630",
    "required": "217f9d1e537d0717e98a767076f440f5ae5b383e24c9db194ca87137bf995ce0",
    "schema_only": "44cf8b8146738472a547ebef735f8ea9b1e2e5c9728d52dc5b4767d7184a07b2",
    "empty_batch": "5ff44593a03cce4070714a46fe0e95fa4ea8c60a9dde0165af9df287129a8920",
}


def verify(wire, name, nullable, expected):
    schema = pa.schema([pa.field(name, pa.large_string(), nullable=nullable)])
    with pa.ipc.open_stream(wire) as reader:
        assert reader.schema.equals(schema, check_metadata=True)
        records = list(reader)
    assert [batch.num_rows for batch in records] == [len(values) for values in expected]
    for batch, values in zip(records, expected, strict=True):
        batch.validate(full=True)
        column = batch.column(0)
        assert column.offset == 0 and column.to_pylist() == values
        validity, offsets, data = column.buffers()
        utf8 = [(value or "").encode("utf-8") for value in values]
        words = list(accumulate(map(len, utf8), initial=0))
        assert offsets.size == 8 * len(words)
        assert struct.unpack(f"<{len(words)}q", offsets) == tuple(words)
        assert (data.to_pybytes() if data is not None else b"") == b"".join(utf8)
        if None in values:
            for i, value in enumerate(values):
                assert ((validity[i // 8] >> (i % 8)) & 1) == (value is not None)

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
         "scripts/arrow-large-utf8/WriteStream.lean", str(output)],
        cwd=ROOT, check=True,
    )
    for case, (name, nullable, expected) in CASES.items():
        wire = (output / f"{case}.arrows").read_bytes()
        ranges, eos = verify(wire, name, nullable, expected)
        digest = hashlib.sha256(wire).hexdigest()
        assert digest == SHA256[case], (case, digest)
        print(f"{case}: SHA-256 {digest}, records {ranges}, EOS {eos}")


if __name__ == "__main__":
    main()
