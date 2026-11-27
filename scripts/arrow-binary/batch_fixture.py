#!/usr/bin/env python3
"""Reproduce a plain Binary IPC fixture with little-endian PyArrow 26.0.1."""

import argparse
import hashlib
from pathlib import Path
import struct
import sys


ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "Silmaril/Formats/Arrow/Binary/Fixture.lean"
LEGACY_FIXTURE = ROOT / "Silmaril/Formats/Arrow/Binary/Stream/Fixture.lean"


def produce(legacy=False):
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
                                     use_legacy_format=legacy, compression=None)

    def emit(columns):
        sink = pa.BufferOutputStream()
        with pa.ipc.new_stream(sink, schema, options=options) as writer:
            for array in columns:
                writer.write_batch(pa.record_batch([array], schema=schema))
        return sink.getvalue().to_pybytes()

    wire = emit(arrays)
    reader = pa.ipc.open_stream(wire)
    assert reader.schema.equals(schema)
    assert [batch.column(0).to_pylist() for batch in reader] == expected

    messages = list(pa.ipc.MessageReader.open_stream(wire))
    assert [message.type for message in messages] == ["schema"] + ["record batch"] * len(expected)
    schema_size = messages[0].metadata.size
    marker = b"" if legacy else b"\xff" * 4
    prefix_size = len(marker) + 4
    assert wire[:prefix_size] == marker + struct.pack("<i", schema_size)
    offset = prefix_size + schema_size
    eos = marker + bytes(4)
    assert emit([]) == wire[:offset] + eos
    empty_reader = pa.ipc.open_stream(emit([]))
    assert empty_reader.schema.equals(schema) and list(empty_reader) == []
    ranges = []
    for message in messages[1:]:
        metadata_size = message.metadata.size
        body_size = message.body.size
        assert wire[offset:offset + prefix_size] == marker + struct.pack("<i", metadata_size)
        assert (offset + prefix_size + metadata_size) % 8 == 0
        ranges.append((offset + prefix_size, metadata_size, body_size))
        offset += prefix_size + metadata_size + body_size
    assert wire[offset:] == eos

    profile = "legacy prefix" if legacy else "continuation prefix"
    topic = "Binary.Stream.Fixture" if legacy else "Binary.Fixture"
    print(f"PyArrow {pa.__version__} {profile} SHA-256 {hashlib.sha256(wire).hexdigest()}")
    print(f"Metadata start, metadata size, body size: {ranges}")
    lean_ranges = ", ".join(f"({start}, {metadata}, {body})" for start, metadata, body in ranges)
    return f"""module

public import Silmaril.Prelude.Bytes.Defs

/-! Genuine PyArrow V5 output reproduced by scripts/arrow-binary/batch_fixture.py. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.{topic}

def stream : KBytes :=
  .leaf {len(wire)} 0x{int.from_bytes(wire, 'little'):x}

def schemaSize : Nat := {schema_size}

def batches : List (Nat × Nat × Nat) :=
  [{lean_ranges}]

end Silmaril.Formats.Arrow.{topic}
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate the checked-in Lean fixture")
    args = parser.parse_args()
    for legacy, fixture in [(False, FIXTURE), (True, LEGACY_FIXTURE)]:
        rendered = produce(legacy)
        if args.write:
            fixture.write_text(rendered)
        elif fixture.read_text() != rendered:
            raise SystemExit(f"fixture drift: {fixture}")


if __name__ == "__main__":
    main()
