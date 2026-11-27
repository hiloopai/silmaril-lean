#!/usr/bin/env python3
"""Rebuild independent PyArrow 26.0.1 files and check mixed-file writer output."""
import argparse
import hashlib
from pathlib import Path
import runpy
import struct
import subprocess
import sys

import pyarrow as pa


ROOT = Path(__file__).resolve().parents[2]
EOS = b"\xff\xff\xff\xff\0\0\0\0"
PINS = {
    "mixed": (
        "098a8e0fc4b0053d52bcaf9466fdf16aa5ac0e6ea433441fa454cc2ff832eac4",
        [(240, 304, 160), (704, 248, 0), (952, 304, 72)],
    ),
    "schema_only": (
        "ad4297e2eabc593f3f5133d2245b297ff4ef5e9a339194b4415d8066221a7651",
        [],
    ),
    "empty": (
        "153ac196d592cf0b8eb86cefd9cd1a11fe7c5f925c77f37b4523510d544ba81a",
        [(240, 248, 0)],
    ),
    "zero_width": (
        "882b395bef1dcd60d3b6c195bcf06663ebd0d2c856507d05d60fef1f5f7f4d9c",
        [(64, 80, 0), (144, 72, 0)],
    ),
    "plain_mixed": (
        "f300ec98b8ff6a62e5fafae7eaa6400f78b33f02366e8a928a7429e9f0c3999a",
        [(320, 432, 216), (968, 392, 16), (1376, 432, 128)],
    ),
    "plain_schema_only": (
        "0abfc65b66d917708215af7b17e8e084304bb85790e296a943ee6e4ef5c7afe3",
        [],
    ),
    "plain_empty": (
        "7a06c0a4daebacad70f3a492e32cf469eecc4d74fc430069da84dfc712e9845a",
        [(320, 392, 16)],
    ),
}


def fixture_cases():
    schema = pa.schema([
        pa.field("t", pa.string_view()),
        pa.field("i", pa.int32(), nullable=False),
        pa.field("b", pa.binary_view()),
    ])

    def batch(text, ints, blobs):
        return pa.record_batch([
            pa.array(text, type=schema[0].type),
            pa.array(ints, type=schema[1].type),
            pa.array(blobs, type=schema[2].type),
        ], schema=schema)

    empty = batch([], [], [])
    plain_schema = pa.schema([
        pa.field("u", pa.string()), pa.field("v", pa.string_view()),
        pa.field("i", pa.int32(), nullable=False), pa.field("q", pa.string(), nullable=False),
        pa.field("b", pa.binary_view()),
    ])

    def plain_batch(*columns):
        return pa.record_batch([
            pa.array(values, type=field.type)
            for field, values in zip(plain_schema, columns, strict=True)
        ], schema=plain_schema)

    plain_empty = plain_batch([], [], [], [], [])
    return {
        "mixed": (schema, [
            batch(["雪" * 5, None, ""], [-7, 0, 42], [bytes([255]) + bytes(12), b"", None]),
            empty,
            batch(["é", "a"], [-2**31, 2**31 - 1], [bytes([128, 255]), bytes([1]) + bytes(11)]),
        ]),
        "schema_only": (schema, []),
        "empty": (schema, [empty]),
        "zero_width": (pa.schema([]), [
            pa.RecordBatch.from_struct_array(pa.array([{}] * rows, type=pa.struct([])))
            for rows in (3, 0)
        ]),
        "plain_mixed": (plain_schema, [
            plain_batch(
                [None, "", "é雪"], ["雪" * 5, None, ""], [-7, 0, 42], ["", "é", "a\0b"],
                [bytes([255]) + bytes(12), b"", None],
            ),
            plain_empty,
            plain_batch(["🙂", "é"], ["", "é"], [1, 2], ["雪", ""], [None, bytes([128, 255])]),
        ]),
        "plain_schema_only": (plain_schema, []),
        "plain_empty": (plain_schema, [plain_empty]),
    }


def produce(schema, batches):
    sink = pa.BufferOutputStream()
    options = pa.ipc.IpcWriteOptions(metadata_version=pa.ipc.MetadataVersion.V5,
                                     use_legacy_format=False, compression=None)
    with pa.ipc.new_file(sink, schema, options=options) as writer:
        for batch in batches:
            writer.write_batch(batch)
    return sink.getvalue().to_pybytes()


def verify(wire, schema, expected):
    helpers = runpy.run_path(str(ROOT / "scripts/arrow-binary-view/batch_fixtures.py"))
    slot_at, vector_at = (helpers[name] for name in ("slot_at", "vector_at"))
    assert wire[:8] == b"ARROW1\0\0" and wire[-6:] == b"ARROW1"
    footer_size, = struct.unpack_from("<i", wire, len(wire) - 10)
    footer_start = len(wire) - 10 - footer_size
    assert footer_size > 0 and footer_start % 8 == 0
    footer = wire[footer_start:-10]
    root, = struct.unpack_from("<I", footer)
    block_slot = slot_at(footer, root, 3)
    _, blocks = vector_at(footer, block_slot[1], "<qi4xq") if block_slot else (0, [])
    stream = wire[8:footer_start]
    messages = list(pa.ipc.MessageReader.open_stream(stream))
    assert [message.type for message in messages] == ["schema"] + ["record batch"] * len(expected)
    assert len(blocks) == len(expected)
    next_offset = 16 + messages[0].metadata.size
    for (offset, metadata, body), message in zip(blocks, messages[1:], strict=True):
        assert offset == next_offset
        assert (metadata, body) == (8 + message.metadata.size, message.body.size)
        assert struct.unpack_from("<II", wire, offset) == (0xFFFFFFFF, metadata - 8)
        next_offset = offset + metadata + body
    assert wire[next_offset:footer_start] == EOS

    with pa.ipc.open_file(wire) as reader:
        assert reader.schema.equals(schema, check_metadata=True)
        observed = [reader.get_batch(n) for n in range(reader.num_record_batches)]
    with pa.ipc.open_stream(stream) as reader:
        assert reader.schema.equals(schema, check_metadata=True)
        sequential = list(reader)
    for batches in (observed, sequential):
        assert [batch.num_rows for batch in batches] == [batch.num_rows for batch in expected]
        for reference, actual in zip(expected, batches, strict=True):
            actual.validate(full=True)
            assert actual.equals(reference, check_metadata=True)
    return blocks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    if sys.byteorder != "little" or pa.__version__ != "26.0.1" or pa.cpp_build_info.version != "26.0.1":
        raise SystemExit("fixture requires little-endian PyArrow 26.0.1")
    args.output.mkdir(parents=True, exist_ok=True)
    cases = fixture_cases()
    for name, (schema, batches) in cases.items():
        wire = produce(schema, batches)
        blocks = verify(wire, schema, batches)
        digest = hashlib.sha256(wire).hexdigest()
        assert (digest, blocks) == PINS[name]
        (args.output / f"pyarrow-{name}.arrow").write_bytes(wire)
        print(f"PyArrow {name} {digest} blocks {blocks}", flush=True)
    subprocess.run(
        ["lake", "env", "lean", "-DwarningAsError=true", "--run",
         str(ROOT / "scripts/arrow-mixed-flat/FileWriterOracle.lean"), str(args.output.resolve())],
        cwd=ROOT, check=True,
    )
    for name, (schema, batches) in cases.items():
        wire = (args.output / f"lean-{name}.arrow").read_bytes()
        blocks = verify(wire, schema, batches)
        print(f"Lean {name} {hashlib.sha256(wire).hexdigest()} blocks {blocks}")


if __name__ == "__main__":
    main()
