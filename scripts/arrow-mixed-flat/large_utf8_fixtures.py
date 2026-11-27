#!/usr/bin/env python3
"""Reproduce genuine modern and legacy V5 mixed LargeUtf8 streams."""
import argparse
import hashlib
from itertools import accumulate
from pathlib import Path
import runpy
import struct
import sys

import pyarrow as pa


ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "Silmaril/Formats/Arrow/MixedFlat/LargeUtf8/Stream/Fixture.lean"
TEXT = [["雪", None, "", "é\x00🙂"], [], ["", "β", None]]
TEXT_REQUIRED = [["雪", "", "é\x00🙂", "x"], [], ["", "β", "z"]]
INTS = [[-7, 0, 9, 2147483647], [], [-2147483648, 12, 6]]
INTS_OPTIONAL = [[None, -7, 0, 9], [], [None, -2147483648, 6]]
INLINE = [[None, b"", b"a", b"\xff"], []]
EXTERNAL = [[b"0123456789abcdef", None, b"", b"x"], []]


def inspect(carrier, schema, values, legacy, expected_counts):
    with pa.ipc.open_stream(carrier) as reader:
        assert reader.schema.equals(schema, check_metadata=True)
        read = list(reader)
    assert [batch.num_rows for batch in read] == [len(batch[0]) for batch in values]
    for batch, columns in zip(read, values, strict=True):
        batch.validate(full=True)
        assert [column.to_pylist() for column in batch.columns] == list(columns)
    helpers = runpy.run_path(str(ROOT / "scripts/arrow-binary-view/batch_fixtures.py"))
    slot_at, target, vector_at = (helpers[name] for name in ("slot_at", "target", "vector_at"))

    messages = list(pa.ipc.MessageReader.open_stream(carrier))
    assert [msg.type for msg in messages] == ["schema"] + ["record batch"] * len(values)
    prefix = b"" if legacy else b"\xff" * 4
    prefix_size = len(prefix) + 4
    offset = 0
    ranges, layouts = [], []
    for index, message in enumerate(messages):
        assert message.metadata_version == pa.ipc.MetadataVersion.V5
        metadata = message.metadata.to_pybytes()
        body = message.body.to_pybytes() if message.body is not None else b""
        assert carrier[offset:offset + prefix_size] == prefix + struct.pack("<i", len(metadata))
        if index > 0:
            columns = values[index - 1]
            root = struct.unpack_from("<I", metadata)[0]
            payload = target(metadata, slot_at(metadata, root, 2)[1])
            _, nodes = vector_at(metadata, slot_at(metadata, payload, 1)[1], "<qq")
            _, buffers = vector_at(metadata, slot_at(metadata, payload, 2)[1], "<qq")
            count_slot = slot_at(metadata, payload, 4)
            counts = [word for (word,) in vector_at(metadata, count_slot[1], "<q")[1]] if count_slot else []
            assert counts == expected_counts[index - 1], (counts, expected_counts[index - 1])
            assert nodes == [(len(col), col.count(None)) for col in columns]
            prior_end = 0
            for start, length in buffers:
                assert prior_end <= start and start % 8 == 0 and 0 <= length <= len(body) - start
                prior_end = start + length
            descriptor = 0
            count_iter = iter(counts)
            for field, column in zip(schema, columns, strict=True):
                if pa.types.is_large_string(field.type):
                    start, length = buffers[descriptor + 1]
                    payload_start, payload_length = buffers[descriptor + 2]
                    octets = [(text or "").encode("utf-8") for text in column]
                    offsets = tuple(accumulate(map(len, octets), initial=0))
                    assert length == 8 * len(offsets)
                    assert struct.unpack_from(f"<{len(offsets)}q", body, start) == offsets
                    assert body[payload_start:payload_start + payload_length] == b"".join(octets)
                    descriptor += 3
                elif pa.types.is_binary_view(field.type):
                    descriptor += 2 + next(count_iter)
                else:
                    assert pa.types.is_int32(field.type)
                    descriptor += 2
            assert descriptor == len(buffers)
            ranges.append((offset, len(metadata), len(body)))
            layouts.append(buffers)
        offset += prefix_size + len(metadata) + len(body)
        assert offset % 8 == 0
    assert carrier[offset:] == prefix + bytes(4)
    return messages[0].metadata.size, ranges, layouts, offset


def make_array(field, values):
    array = pa.array(values, type=field.type)
    if field.name == "inline":
        validity, views, *data = array.buffers()
        assert all(buffer.size == 0 for buffer in data)
        return pa.Array.from_buffers(field.type, len(array), [validity, views], null_count=array.null_count)
    return array


def fixture(name, fields, columns, legacy, expected_counts):
    schema = pa.schema(fields)
    options = pa.ipc.IpcWriteOptions(metadata_version=pa.ipc.MetadataVersion.V5,
                                     use_legacy_format=legacy, compression=None)
    values = list(zip(*columns, strict=True))
    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, schema, options=options) as writer:
        for batch in values:
            arrays = [make_array(field, col) for field, col in zip(fields, batch, strict=True)]
            writer.write_batch(pa.record_batch(arrays, schema=schema))
    wire = sink.getvalue().to_pybytes()
    schema_size, ranges, layouts, eos = inspect(wire, schema, values, legacy, expected_counts)
    digest = hashlib.sha256(wire).hexdigest()
    print(f"{name}: SHA-256 {digest}, ranges {ranges}, counts {expected_counts}, EOS {eos}")
    return (f"-- SHA-256 {digest}\n"
            f"def {name} : KBytes :=\n  .leaf {len(wire)} 0x{int.from_bytes(wire, 'little'):x}\n\n"
            f"def {name}SchemaSize : Nat := {schema_size}\n"
            f"def {name}Ranges : List (Nat × Nat × Nat) := {ranges!r}\n"
            f"def {name}Buffers : List (List (Nat × Nat)) := {layouts!r}\n"
            f"def {name}Eos : Nat := {eos}\n\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate the checked-in fixture")
    args = parser.parse_args()
    if (sys.byteorder != "little" or pa.__version__ != "26.0.1"
            or pa.cpp_build_info.version != "26.0.1"):
        raise SystemExit("fixture requires little-endian PyArrow 26.0.1")
    text = pa.field("text", pa.large_string())
    number = pa.field("number", pa.int32(), nullable=False)
    ns = "Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Fixture"
    rendered = ("module\n\npublic import Silmaril.Prelude.Bytes.Defs\n\n"
                "/-! Reproduced by scripts/arrow-mixed-flat/large_utf8_fixtures.py. -/\n\n"
                f"@[expose] public section\n\nnamespace {ns}\n\n")
    for suffix, legacy in (("Modern", False), ("Legacy", True)):
        rendered += fixture(f"intFirst{suffix}", [number, text], [INTS, TEXT], legacy, [[], [], []])
        rendered += fixture(f"textFirst{suffix}", [text.with_nullable(False), number.with_nullable(True)],
                            [TEXT_REQUIRED, INTS_OPTIONAL], legacy, [[], [], []])
    rendered += fixture("withViews", [pa.field("inline", pa.binary_view()), text, number,
                                      pa.field("external", pa.binary_view())],
                        [INLINE, TEXT[:2], INTS[:2], EXTERNAL], False, [[0, 1], [0, 0]])
    rendered += f"end {ns}\n"
    if args.write:
        FIXTURE.write_text(rendered)
    elif FIXTURE.read_text() != rendered:
        raise SystemExit(f"fixture drift: {FIXTURE}")


if __name__ == "__main__":
    main()
