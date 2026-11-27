#!/usr/bin/env python3
"""Reproduce the pinned three-BinaryView V5 stream."""

import argparse
import hashlib
from pathlib import Path
import runpy
import struct
import sys

import pyarrow as pa


ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "Silmaril/Formats/Arrow/MixedFlat/Stream/Incremental/Portable/Fixture.lean"
EOS = b"\xff\xff\xff\xff\x00\x00\x00\x00"


def produce():
    if sys.byteorder != "little" or pa.__version__ != "26.0.1":
        raise SystemExit("fixture requires little-endian PyArrow 26.0.1")

    schema = pa.schema([
        pa.field("a", pa.binary_view()),
        pa.field("i", pa.int32(), nullable=False),
        pa.field("b", pa.binary_view()),
        pa.field("c", pa.binary_view()),
    ])
    values = [
        [[b"A" * 13, None], [7, -2], [b"short", b""], [b"C" * 17, b"\xff"]],
        [[b"a", None], [9, 0], [b"B" * 14, None], [None, b""]],
        [[], [], [], []],
    ]
    options = pa.ipc.IpcWriteOptions(metadata_version=pa.ipc.MetadataVersion.V5,
                                     use_legacy_format=False, compression=None)
    def make_column(cells, field):
        column = pa.array(cells, type=field.type)
        if pa.types.is_binary_view(field.type) and all(value is None or len(value) <= 12 for value in cells):
            column = pa.Array.from_buffers(field.type, len(cells), column.buffers()[:2],
                                           null_count=column.null_count)
        return column

    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, schema, options=options) as writer:
        for batch in values:
            columns = [make_column(column, field) for column, field in zip(batch, schema)]
            writer.write_batch(pa.record_batch(columns, schema=schema))
    raw = sink.getvalue().to_pybytes()

    reader = pa.ipc.open_stream(raw)
    assert reader.schema.equals(schema)
    batches = list(reader)
    assert [batch.num_rows for batch in batches] == [2, 2, 0]
    assert [[column.to_pylist() for column in batch.columns] for batch in batches] == values
    positions = [3, 0, 3, 1]
    projected = [[list(row) for row in zip(*(batch[i] for i in positions))] for batch in values]

    helpers = runpy.run_path(str(ROOT / "scripts/arrow-binary-view/batch_fixtures.py"))
    slot_at, target, vector_at = (helpers[name] for name in ("slot_at", "target", "vector_at"))
    messages = list(pa.ipc.MessageReader.open_stream(raw))
    assert [message.type for message in messages] == ["schema", "record batch", "record batch", "record batch"]
    offset = 8 + messages[0].metadata.size
    ranges, counts = [], []
    for message in messages[1:]:
        metadata = message.metadata.to_pybytes()
        size = len(metadata)
        body = message.body.size if message.body is not None else 0
        assert struct.unpack_from("<II", raw, offset) == (0xFFFFFFFF, size)
        ranges.append((offset, size, body))
        root = struct.unpack_from("<I", metadata)[0]
        payload = target(metadata, slot_at(metadata, root, 2)[1])
        _, words = vector_at(metadata, slot_at(metadata, payload, 4)[1], "<q")
        counts.append([word[0] for word in words])
        offset += 8 + size + body
    assert raw[offset:] == EOS
    assert counts == [[1, 0, 1], [0, 1, 0], [0, 0, 0]], counts
    print(f"threeViews SHA-256 {hashlib.sha256(raw).hexdigest()}")
    print(f"record ranges {ranges}, view counts {counts}, EOS {offset}")
    print(f"PyArrow projected rows at {positions} {projected}")

    ranges_lean = ", ".join(f"({start}, {size}, {body})" for start, size, body in ranges)
    return (
        "module\n\npublic import Silmaril.Prelude.Bytes.Defs\n\n"
        "/-! Reproduced by scripts/arrow-mixed-flat/ordered_incremental_fixtures.py. -/\n\n"
        "@[expose] public section\n\n"
        "namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Portable.Fixture\n\n"
        f"def threeViews : KBytes :=\n  .leaf {len(raw)} 0x{int.from_bytes(raw, 'little'):x}\n\n"
        f"def ranges : List (Nat × Nat × Nat) :=\n  [{ranges_lean}]\n\n"
        "end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Portable.Fixture\n"
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", type=Path, help="write the reproduced Lean fixture")
    args = parser.parse_args()
    reproduced = produce()
    if args.write:
        args.write.write_text(reproduced, encoding="utf-8")
    elif FIXTURE.read_text(encoding="utf-8") != reproduced:
        raise SystemExit("reproduced fixture differs from the checked Lean bytes")


if __name__ == "__main__":
    main()
