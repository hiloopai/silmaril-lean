#!/usr/bin/env python3
"""Reproduce a plain Binary IPC fixture with little-endian PyArrow 26.0.1."""

import argparse
import hashlib
from pathlib import Path
import struct
import sys


ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "Silmaril/Formats/Arrow/Binary/Fixture.lean"
EOS = b"\xff\xff\xff\xff\x00\x00\x00\x00"


def produce():
    import pyarrow as pa

    if sys.byteorder != "little" or pa.__version__ != "26.0.1":
        raise SystemExit("fixture requires little-endian PyArrow 26.0.1")

    schema = pa.schema([pa.field("payload", pa.binary(), nullable=True)])
    expected = [[b"\xff\x00\x80", None, b"", b"abc\x00xyz" * 3], [], [None, None], [b""]]
    parent = pa.array([b"prefix", *expected[0], b"suffix"], type=pa.binary())
    sliced = parent.slice(1, len(expected[0]))
    assert sliced.offset == 1
    assert struct.unpack_from("<i", sliced.buffers()[1], 4)[0] == len(b"prefix")
    arrays = [sliced, *[pa.array(values, type=pa.binary()) for values in expected[1:]]]
    options = pa.ipc.IpcWriteOptions(metadata_version=pa.ipc.MetadataVersion.V5,
                                     use_legacy_format=False, compression=None)
    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, schema, options=options) as writer:
        for array in arrays:
            writer.write_batch(pa.record_batch([array], schema=schema))
    wire = sink.getvalue().to_pybytes()

    reader = pa.ipc.open_stream(wire)
    assert reader.schema.equals(schema)
    assert [batch.column(0).to_pylist() for batch in reader] == expected

    messages = list(pa.ipc.MessageReader.open_stream(wire))
    assert [message.type for message in messages] == ["schema"] + ["record batch"] * len(expected)
    schema_size = messages[0].metadata.size
    assert struct.unpack_from("<II", wire) == (0xFFFFFFFF, schema_size)
    offset = 8 + schema_size
    ranges = []
    for message in messages[1:]:
        metadata_size = message.metadata.size
        body_size = message.body.size
        assert struct.unpack_from("<II", wire, offset) == (0xFFFFFFFF, metadata_size)
        ranges.append((offset + 8, metadata_size, body_size))
        offset += 8 + metadata_size + body_size
    assert wire[offset:] == EOS

    print(f"PyArrow {pa.__version__} stream SHA-256 {hashlib.sha256(wire).hexdigest()}")
    print(f"Metadata start, metadata size, body size: {ranges}")
    lean_ranges = ", ".join(f"({start}, {metadata}, {body})" for start, metadata, body in ranges)
    return f"""module

public import Silmaril.Prelude.Bytes.Defs

/-! Genuine PyArrow V5 output reproduced by scripts/arrow-binary/batch_fixture.py. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.Binary.Fixture

def stream : KBytes :=
  .leaf {len(wire)} 0x{int.from_bytes(wire, 'little'):x}

def schemaSize : Nat := {schema_size}

def batches : List (Nat × Nat × Nat) :=
  [{lean_ranges}]

end Silmaril.Formats.Arrow.Binary.Fixture
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate the checked-in Lean fixture")
    args = parser.parse_args()
    rendered = produce()
    if args.write:
        FIXTURE.write_text(rendered)
    elif FIXTURE.read_text() != rendered:
        raise SystemExit(f"fixture drift: {FIXTURE}")


if __name__ == "__main__":
    main()
