#!/usr/bin/env python3
"""Reproduce genuine V5 LargeUtf8 IPC streams from pinned PyArrow."""
import argparse
import hashlib
from pathlib import Path
import struct
import sys

import pyarrow as pa


ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "Silmaril/Formats/Arrow/LargeUtf8/Stream/Fixture.lean"
EXPECTED = [["雪", None, "", "é\x00🙂"], [], [None, "", "é"], [None, None]]


def produce(legacy):
    kind = pa.large_string()
    schema = pa.schema([pa.field("payload", kind, nullable=True)])
    parent = pa.array(["prefix", *EXPECTED[0], "suffix"], type=kind)
    sliced = parent.slice(1, len(EXPECTED[0]))
    assert sliced.offset == 1
    assert struct.unpack_from("<q", sliced.buffers()[1], 8)[0] == len(b"prefix")
    covered_null = pa.Array.from_buffers(
        kind, 3, [pa.py_buffer(b"\x06"), pa.py_buffer(struct.pack("<4q", 0, 1, 1, 3)),
                  pa.py_buffer(b"Q\xc3\xa9")], null_count=1,
    )
    covered_null.validate(full=True)
    arrays = [sliced, pa.array([], type=kind), covered_null, pa.array(EXPECTED[3], type=kind)]
    options = pa.ipc.IpcWriteOptions(metadata_version=pa.ipc.MetadataVersion.V5,
                                     use_legacy_format=legacy, compression=None)

    def emit(columns):
        sink = pa.BufferOutputStream()
        with pa.ipc.new_stream(sink, schema, options=options) as writer:
            for array in columns:
                writer.write_batch(pa.record_batch([array], schema=schema))
        return sink.getvalue().to_pybytes()

    wire = emit(arrays)
    with pa.ipc.open_stream(wire) as reader:
        assert reader.schema.equals(schema, check_metadata=True)
        batches = list(reader)
    assert [batch.column(0).to_pylist() for batch in batches] == EXPECTED
    for batch in batches:
        batch.validate(full=True)
    validity, offsets, data = batches[2].column(0).buffers()
    assert validity.to_pybytes() == b"\x06"
    assert struct.unpack("<4q", offsets) == (0, 1, 1, 3)
    assert data.to_pybytes() == b"Q\xc3\xa9"

    messages = list(pa.ipc.MessageReader.open_stream(wire))
    assert [msg.type for msg in messages] == ["schema"] + ["record batch"] * len(EXPECTED)
    marker = b"" if legacy else b"\xff" * 4
    prefix_size = len(marker) + 4
    offset = 0
    ranges = []
    for message in messages:
        assert message.metadata_version == pa.ipc.MetadataVersion.V5
        metadata = message.metadata.size
        body = message.body.size if message.body is not None else 0
        assert wire[offset:offset + prefix_size] == marker + struct.pack("<i", metadata)
        next_offset = offset + prefix_size + metadata + body
        assert next_offset % 8 == 0
        if message.type == "record batch":
            ranges.append((offset, metadata, body))
        offset = next_offset
    eos = marker + bytes(4)
    assert wire[offset:] == eos
    schema_size = messages[0].metadata.size
    schema_only = emit([])
    assert schema_only == wire[:prefix_size + schema_size] + eos
    with pa.ipc.open_stream(schema_only) as reader:
        assert reader.schema.equals(schema) and list(reader) == []

    name = "legacy" if legacy else "modern"
    print(f"{name}: SHA-256 {hashlib.sha256(wire).hexdigest()}, ranges {ranges}, EOS {offset}")
    lean_ranges = ", ".join(f"({start}, {metadata}, {body})" for start, metadata, body in ranges)
    return f"""def {name} : KBytes :=
  .leaf {len(wire)} 0x{int.from_bytes(wire, 'little'):x}

def {name}SchemaSize : Nat := {schema_size}

def {name}Ranges : List (Nat × Nat × Nat) :=
  [{lean_ranges}]

def {name}Eos : Nat := {offset}

"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate the checked-in fixture")
    args = parser.parse_args()
    if (sys.byteorder != "little" or pa.__version__ != "26.0.1"
            or pa.cpp_build_info.version != "26.0.1"):
        raise SystemExit("fixture requires little-endian PyArrow 26.0.1")
    rendered = """module

public import Silmaril.Prelude.Bytes.Defs

/-! Genuine PyArrow V5 output reproduced by scripts/arrow-large-utf8/stream_fixture.py. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.LargeUtf8.Stream.Fixture

""" + produce(False) + produce(True) + "end Silmaril.Formats.Arrow.LargeUtf8.Stream.Fixture\n"
    if args.write:
        FIXTURE.write_text(rendered)
    elif FIXTURE.read_text() != rendered:
        raise SystemExit(f"fixture drift: {FIXTURE}")


if __name__ == "__main__":
    main()
