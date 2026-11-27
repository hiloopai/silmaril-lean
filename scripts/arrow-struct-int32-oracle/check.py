"""Compare the fixed Struct profile against pinned producer bytes and emitted IPC."""

from hashlib import sha256
import json
from pathlib import Path
import platform
import runpy
import struct
import subprocess
import tempfile

import pyarrow as pa

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
LIST = runpy.run_path(str(HERE.parent / "arrow-list-int32-stream/Oracle.py"))
scalar, target, slot, vector, field_table = (LIST[name] for name in
                                             ("scalar", "target", "slot", "vector", "field_table"))
EOS = b"\xff\xff\xff\xff\0\0\0\0"
MIN, MAX = -(2**31), 2**31 - 1
MIXED = pa.field("点", pa.struct([
    pa.field("signed", pa.int32(), nullable=False), pa.field("北", pa.int32()),
]))
REPEATED = pa.field("pair", pa.struct([pa.field("same", pa.int32()), pa.field("same", pa.int32())]))
# Keep physical child values independently of the parent bit, including
# a null required child that is hidden and a nonzero hidden child word.
MIXED_SLOTS = [
    [(False, 99, 12), (True, MIN, None), (True, 7, 0), (False, None, -121), (True, 0, MAX)],
    [],
    [(True, MAX, MIN), (True, 5, None)],
]
REPEATED_SLOTS = [[(True, None, None), (False, -19, 27), (True, None, -1),
                   (True, 2, None), (True, -3, 4)], []]
CASES = {"mixed": (MIXED, MIXED_SLOTS), "repeated": (REPEATED, REPEATED_SLOTS), "schema_only": (MIXED, [])}


def produce(field, batches, compression=None):
    schema = pa.schema([field])
    sink = pa.BufferOutputStream()
    opts = pa.ipc.IpcWriteOptions(metadata_version=pa.ipc.MetadataVersion.V5, compression=compression)
    with pa.ipc.new_stream(sink, schema, options=opts) as writer:
        for rows in batches:
            children = [pa.array([row[i + 1] for row in rows], type=child.type)
                        for i, child in enumerate(field.type)]
            mask = pa.array([not present for present, *_ in rows], type=pa.bool_())
            array = pa.StructArray.from_arrays(children, fields=list(field.type), mask=mask)
            writer.write_batch(pa.record_batch([array], schema=schema))
    return sink.getvalue().to_pybytes()


def batch_metadata(message):
    metadata = message.metadata.to_pybytes()
    root = target(metadata, 0)
    assert scalar(metadata, slot(metadata, root, 0), "H") == 4
    assert scalar(metadata, slot(metadata, root, 1), "B") == 3
    batch = target(metadata, slot(metadata, root, 2))
    node_start, nodes = vector(metadata, batch, 1, "<qq")
    buffer_start, buffers = vector(metadata, batch, 2, "<qq")
    return metadata, node_start, nodes, buffer_start, buffers


def inspect_wire(wire, field, expected, *, canonical):
    messages = list(pa.ipc.MessageReader.open_stream(wire))
    assert [message.type for message in messages] == ["schema"] + ["record batch"] * len(expected)
    schema = messages[0].metadata.to_pybytes()
    parent = field_table(schema, 0)
    assert scalar(schema, slot(schema, parent, 2), "B") == 13
    assert scalar(schema, slot(schema, parent, 1), "B") == 1
    start, children = vector(schema, parent, 5, "<I")
    assert len(children) == 2
    for i, child in enumerate(field.type):
        table = target(schema, start + 4 * i)
        nullable = slot(schema, table, 1)
        assert (nullable is not None and bool(scalar(schema, nullable, "B"))) == child.nullable
        assert scalar(schema, slot(schema, table, 2), "B") == 2
        payload = target(schema, slot(schema, table, 3))
        assert scalar(schema, slot(schema, payload, 0), "i") == child.type.bit_width
        assert scalar(schema, slot(schema, payload, 1), "B") == 1

    assert struct.unpack_from("<II", wire, 0) == (0xFFFFFFFF, len(schema))
    offset = 8 + len(schema)
    locations = []
    for record, rows in zip(messages[1:], expected, strict=True):
        metadata, node_at, nodes, buffer_at, descriptors = batch_metadata(record)
        assert struct.unpack_from("<II", wire, offset) == (0xFFFFFFFF, len(metadata))
        body_at = offset + 8 + len(metadata)
        body = record.body.to_pybytes() if record.body else b""
        assert body == wire[body_at:body_at + len(body)]
        count = len(rows)
        assert [node[0] for node in nodes] == [count] * 3 and len(descriptors) == 5
        assert len(body) % 8 == 0
        cursor = 0
        for pos, size in descriptors:
            assert cursor <= pos and pos % 8 == 0 and pos + size <= len(body)
            cursor = pos + size
        parent_bits, left_bits, left_words, right_bits, right_words = [
            body[pos:pos + size] for pos, size in descriptors]
        valid = LIST["valid"]
        assert [valid(parent_bits, r) for r in range(count)] == [row[0] for row in rows]
        assert nodes[0][1] == sum(not row[0] for row in rows)
        for child_index, (bits, values) in enumerate([(left_bits, left_words), (right_bits, right_words)]):
            expected_slots = [row[child_index + 1] if row[0] or not canonical
                              else None if field.type[child_index].nullable else 0 for row in rows]
            width = field.type[child_index].type.bit_width // 8
            word_format = {4: "<i", 8: "<q"}[width]
            observed = [struct.unpack_from(word_format, values, width * r)[0] if valid(bits, r) else None
                        for r in range(count)]
            assert observed == expected_slots
            assert nodes[child_index + 1][1] == expected_slots.count(None)
        locations.append((offset + 8 + node_at, offset + 8 + buffer_at, body_at, descriptors, len(body)))
        offset = body_at + len(body)
    assert wire[offset:] == EOS
    return locations


def check_pyarrow(wire, field, rows):
    source = pa.BufferReader(wire)
    with pa.ipc.open_stream(source) as reader:
        assert list(reader.schema) == [field]
        batches = list(reader)
        assert source.tell() == len(wire)
    for batch, expected in zip(batches, rows, strict=True):
        assert batch.num_rows == len(expected)
        array = batch.column(0)
        actual = [tuple(slots) if valid else None for valid, *slots in zip(
            array.is_valid().to_pylist(), array.field(0).to_pylist(), array.field(1).to_pylist(), strict=True)]
        assert actual == [tuple(slots) if valid else None for valid, *slots in expected]


def edit(wire, position, encoding, value):
    updated = bytearray(wire)
    assert struct.unpack_from(encoding, updated, position) != (value,)
    struct.pack_into(encoding, updated, position, value)
    return bytes(updated)


def fixtures():
    inputs = {name: produce(field, rows) for name, (field, rows) in CASES.items()}
    inputs["required_parent"] = produce(MIXED.with_nullable(False), [])
    inputs["wrong_integer"] = produce(MIXED.with_type(pa.struct([MIXED.type[0], pa.field("wide", pa.int64())])), [])
    inputs["one_child"] = produce(MIXED.with_type(pa.struct([MIXED.type[0]])), [])
    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, pa.schema([pa.field("plain", pa.int32())])):
        pass
    inputs["flat"] = sink.getvalue().to_pybytes()
    inputs["required_visible"] = produce(MIXED, [[(True, None, 0)]])
    inputs["compressed"] = produce(MIXED, MIXED_SLOTS, compression="lz4")
    source = inputs["mixed"]
    assert source.endswith(EOS)
    first, _, late = inspect_wire(source, MIXED, MIXED_SLOTS, canonical=False)
    nodes, buffers, body, descriptors, length = first
    inputs["edited_trailing"] = source + b"\0"
    inputs["edited_missing_eos"] = source[:-len(EOS)]
    inputs["edited_late_child_length"] = edit(source, late[0] + 16, "<q", 1)
    inputs["edited_body_extent"] = edit(source, buffers + 4 * 16, "<q", length + 8)
    parent_byte = body + descriptors[0][0]
    inputs["edited_parent_bitmap"] = edit(source, parent_byte, "<B", source[parent_byte] ^ 1)
    inputs["edited_child_null_count"] = edit(source, nodes + 16 + 8, "<q", 0)
    return inputs


def main():
    assert platform.python_version() == "3.13.5" and pa.__version__ == "26.0.1"
    inputs = fixtures()
    assert {name: sha256(data).hexdigest() for name, data in inputs.items()} == json.loads(
        (HERE / "fixtures.json").read_text())
    with tempfile.TemporaryDirectory(prefix="arrow-struct-int32-") as output:
        directory = Path(output)
        for name, data in inputs.items():
            (directory / f"{name}.arrow").write_bytes(data)
        subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
                        str(HERE / "Emit.lean"), output], cwd=ROOT, check=True)
        for name, (field, rows) in CASES.items():
            check_pyarrow(inputs[name], field, rows)
            emitted = (directory / f"{name}.lean.arrow").read_bytes()
            check_pyarrow(emitted, field, rows)
            inspect_wire(emitted, field, rows, canonical=True)
    print("PyArrow and independent descriptor and bitmap checks verified three actual Lean IPC streams")


if __name__ == "__main__":
    main()
