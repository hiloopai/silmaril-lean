#!/usr/bin/env python3
"""Open pinned mixed LargeUtf8 streams emitted by Lean in PyArrow."""
import argparse
import hashlib
from itertools import accumulate
from pathlib import Path
import runpy
import struct
import subprocess
import sys

import pyarrow as pa


ROOT = Path(__file__).resolve().parents[2]
PINS = {
    "mixed": "e18ffb39ec329c33efd5e6ff0790d7efec312a4035b79c866500d49c64ce8cab",
    "reversed": "e61de2bf491bae6a7885a278e9016d1380b70eb88eca779ce2710d22042e7bd2",
    "schema_only": "badd004c924eaf88d42553983e8ce4a551ad7bfab574f5b64563f07648ee8087",
    "empty_batch": "ec966e4a960b7e75a4b922364ae912f1f33e601b0fc0b131a6a768707c66f39e",
    "zero_width": "e3853edf19cfa66fc7534a1b99a4569993f35a525cb8bef2f8c585c6799b1dab",
}


def fixture_cases():
    fields = [
        pa.field("text", pa.large_string()),
        pa.field("number", pa.int32(), nullable=False),
        pa.field("view", pa.binary_view()),
        pa.field("wide_雪", pa.large_string(), nullable=False),
        pa.field("plain", pa.string()),
    ]
    values = [
        [[None, "", "雪🙂", "é"], [-7, 0, 12, 2147483647],
         [b"0123456789abcdef", None, b"", b"\x00\xff"],
         ["", "a\x00b", "ééééé", "𐍈"], ["", None, "a", "雪"]],
        [[], [], [], [], []],
        [["", None], [-2147483648, 7], [b"", None], ["雪", ""], ["plain", ""]],
    ]

    def make(schema, columns):
        return pa.record_batch(
            [pa.array(col, type=field.type) for col, field in zip(columns, schema, strict=True)],
            schema=schema,
        )

    schema = pa.schema(fields)
    backwards = pa.schema(fields[::-1])
    return {
        "mixed": (schema, [make(schema, batch) for batch in values], [[1], [0], [0]]),
        "reversed": (backwards, [make(backwards, batch[::-1]) for batch in values], [[1], [0], [0]]),
        "schema_only": (schema, [], []),
        "empty_batch": (schema, [make(schema, values[1])], [[0]]),
        "zero_width": (
            pa.schema([]),
            [pa.RecordBatch.from_struct_array(pa.array([{}] * n, type=pa.struct([]))) for n in (3, 0, 2)],
            [[], [], []],
        ),
    }


def check_layout(wire, schema, expected, count_vectors):
    helpers = runpy.run_path(str(ROOT / "scripts/arrow-binary-view/batch_fixtures.py"))
    slot_at, target, vector_at = (helpers[name] for name in ("slot_at", "target", "vector_at"))
    messages = list(pa.ipc.MessageReader.open_stream(wire))
    assert all(msg.metadata_version == pa.ipc.MetadataVersion.V5 for msg in messages)
    for message, batch, counts in zip(messages[1:], expected, count_vectors, strict=True):
        metadata = message.metadata.to_pybytes()
        body = message.body.to_pybytes() if message.body is not None else b""
        root = struct.unpack_from("<I", metadata)[0]
        payload = target(metadata, slot_at(metadata, root, 2)[1])
        _, nodes = vector_at(metadata, slot_at(metadata, payload, 1)[1], "<qq")
        _, buffers = vector_at(metadata, slot_at(metadata, payload, 2)[1], "<qq")
        _, words = vector_at(metadata, slot_at(metadata, payload, 4)[1], "<q")
        assert words == [(count,) for count in counts]
        assert nodes == [(batch.num_rows, array.null_count) for array in batch.columns]

        prior_end = 0
        for start, length in buffers:
            assert prior_end <= start and start % 8 == 0 and 0 <= length <= len(body) - start
            prior_end = start + length

        index = 0
        variadic = iter(counts)
        for field, column in zip(schema, batch.columns, strict=True):
            if pa.types.is_large_string(field.type):
                values = column.to_pylist()
                octets = [(value or "").encode("utf-8") for value in values]
                offsets = tuple(accumulate(map(len, octets), initial=0))
                validity, (start, length), (data, data_length) = buffers[index:index + 3]
                assert length == 8 * len(offsets)
                assert struct.unpack_from(f"<{len(offsets)}q", body, start) == offsets
                assert body[data:data + data_length] == b"".join(octets)
                bitmap, size = validity
                assert size == (len(values) + 7) // 8
                for i, value in enumerate(values):
                    assert ((body[bitmap + i // 8] >> (i % 8)) & 1) == (value is not None)
                index += 3
            elif pa.types.is_binary_view(field.type):
                index += 2 + next(variadic)
            elif pa.types.is_int32(field.type):
                index += 2
            else:
                assert pa.types.is_string(field.type)
                index += 3
        assert index == len(buffers)
        assert next(variadic, None) is None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    if (sys.byteorder != "little" or pa.__version__ != "26.0.1"
            or pa.cpp_build_info.version != "26.0.1"):
        raise SystemExit("oracle requires little-endian PyArrow 26.0.1")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    scripts = ROOT / "scripts/arrow-mixed-flat"
    verify = runpy.run_path(str(scripts / "plain_utf8_stream_oracle.py"))["verify"]
    subprocess.run(
        ["lake", "env", "lean", "-DwarningAsError=true", "--run",
         str(scripts / "LargeUtf8StreamWriter.lean"), str(output)],
        cwd=ROOT, check=True,
    )
    for name, (schema, batches, counts) in fixture_cases().items():
        wire = (output / f"{name}.arrows").read_bytes()
        ranges, eos = verify(wire, schema, batches)
        check_layout(wire, schema, batches, counts)
        digest = hashlib.sha256(wire).hexdigest()
        assert digest == PINS[name], (name, digest)
        print(f"{name}: SHA-256 {digest}, records {ranges}, EOS {eos}")


if __name__ == "__main__":
    main()
