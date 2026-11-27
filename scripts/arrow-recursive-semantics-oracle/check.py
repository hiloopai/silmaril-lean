"""Compare a recursive physical observation with pinned PyArrow and raw IPC."""

import json
from pathlib import Path
import platform
import runpy
import struct
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
MANIFEST = Path(__file__).with_name("fixtures.json")
BATCH = runpy.run_path(str(ROOT / "scripts/arrow-recursive-batch-oracle/check.py"))
metadata, read_record, inspect = (BATCH[key] for key in ("metadata", "read_record", "inspect"))
require, fingerprint, bytes_term = (BATCH[key] for key in ("require", "fingerprint", "bytes_term"))

LEAN = """\
module

meta import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Semantics.Defs

open Silmaril
open Silmaril.Formats.Arrow.RecursiveSchema.Batch (readFrame)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Semantics

private meta def sees (input : KBytes) (following : Bool) (wanted : Observation) : Bool :=
  match readFirst {} input with
  | .error _ => false
  | .ok (first, observed) =>
    if following then
      match readFrame {} first.schema input first.batch.next with
      | .error _ => false
      | .ok frame =>
        match decode frame with
        | .error _ => false
        | .ok second => second == wanted
    else observed == wanted

private meta def refuses (input : KBytes) (wanted : Error) : Bool :=
  match readFirst {} input with
  | .error cause => cause == wanted
  | .ok _ => false
"""


def hidden_stream(pa):
    # Set required children explicitly and let PyArrow serialize the full physical arrays.
    record_type = pa.struct([pa.field("must", pa.int32(), nullable=False),
                             pa.field("wide", pa.int64())])
    record = pa.StructArray.from_arrays(
        [pa.array([10, None, 12, 13], type=pa.int32()),
         pa.array([-(2**63), 99, 2**63 - 1, None], type=pa.int64())],
        type=record_type, mask=pa.array([False, True, False, False]))
    all_null = pa.StructArray.from_arrays(
        [pa.array([None, None, 0, 5], type=pa.int32()),
         pa.array([None, None, 100, 4], type=pa.int64())],
        names=["left", "right"], mask=pa.array([False, True, False, False]))
    list_type = pa.list_(pa.field("item", pa.int64(), nullable=False))
    windows = pa.ListArray.from_arrays(
        pa.array([0, 1, 3, 3, 4], type=pa.int32()),
        pa.array([-(2**63), None, 2**45, 2**63 - 1], type=pa.int64()),
        type=list_type, mask=pa.array([False, True, False, False]))

    batch = pa.record_batch([record, all_null, windows], names=["record", "all", "list"])
    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, batch.schema) as writer:
        writer.write_batch(batch)
    data = sink.getvalue().to_pybytes()
    require(pa.ipc.open_stream(data).read_next_batch().equals(batch), "PyArrow round trip differs")
    return data


def produce(pa):
    previous = BATCH["produce"](pa)
    return {"four_level": previous["populated"], "hidden": hidden_stream(pa),
            "empty_schema": previous["empty_schema"]}


def positional(pa, record, batch):
    inspect(pa, batch, record)  # Compare each descriptor's actual slice with the PyArrow buffer.
    nodes = iter(record.nodes)
    regions = iter(record.buffers)

    def bytes_at_next_region():
        offset, length = next(regions)
        return record.body[offset:offset + length]

    def walk(array, visible):
        length, nulls = next(nodes)
        raw = bytes_at_next_region()
        validity = [not raw or bool(raw[i // 8] & (1 << (i % 8))) for i in range(length)]
        require(validity == array.is_valid().to_pylist() and validity.count(False) == nulls,
                "original logical bits or null count differ")
        present = [reached and valid for reached, valid in zip(visible, validity, strict=True)]
        children = []

        if pa.types.is_struct(array.type):
            kind, payload = "struct", None
            children = [walk(array.field(i), present) for i in range(array.type.num_fields)]

            def value_at(i):
                return {field.name: child_value(i)
                        for field, (_, child_value) in zip(array.type, children, strict=True)}
        else:
            data = bytes_at_next_region()
            if pa.types.is_list(array.type):
                kind = "list"
                payload = list(struct.unpack_from(f"<{length + 1}i", data))
                require(payload == array.offsets.to_pylist(), "original List offsets differ")
                child_visibility = [bit for i, bit in enumerate(present)
                                    for _ in range(payload[i], payload[i + 1])]
                children = [walk(array.values, child_visibility)]

                def value_at(i):
                    child = children[0][1]
                    return [child(j) for j in range(payload[i], payload[i + 1])]
            else:
                width = array.type.bit_width
                kind = f"int{width}"
                payload = [item[0] for item in struct.iter_unpack("<i" if width == 32 else "<q", data)]

                def value_at(i):
                    return payload[i]

        return ((visible, validity, kind, payload, [child for child, _ in children]),
                lambda i: value_at(i) if present[i] else None)

    columns = []
    for array in batch:
        column, value_at = walk(array, [True] * record.rows)
        require([value_at(i) for i in range(record.rows)] == array.to_pylist(),
                "nested logical values differ from PyArrow")
        columns.append(column)
    require(next(nodes, None) is None and next(regions, None) is None, "unconsumed original entries")
    return columns


def controls(ipc, preceding):
    _, start = metadata(ipc)
    record = read_record(ipc, start)
    edit_record, edit_body = (BATCH[key] for key in ("edit_record", "edit_body"))

    def change_count(data, node, count):
        return edit_record(data, record, record.node_start + 16 * node + 8, "q", count)

    def bitmap(data, buffer, mask):
        offset, length = record.buffers[buffer]
        require(length == 1, "expected one genuine bitmap byte")
        return edit_body(data, record, offset, "B", record.body[offset] | mask)

    require(record.rows == 4 and record.nodes[0] == (4, 1) and record.nodes[1] == (4, 1)
            and record.nodes[6] == (4, 1) and record.nodes[7] == (4, 1),
            "unexpected original hidden slots")
    list_offset, list_bytes = record.buffers[11]
    require(list_bytes == 20 and struct.unpack_from("<5i", record.body, list_offset) == (0, 1, 3, 3, 4),
            "producer did not retain the nonempty null List window")
    require(record.body[record.buffers[0][0]] & 0xf0 == 0, "expected zero original bitmap padding")
    list_reached = change_count(bitmap(ipc, 10, 2), 6, 0)
    struct_reached = change_count(bitmap(ipc, 0, 2), 0, 0)
    require(bitmap(ipc, 0, 2) != ipc and list_reached != ipc, "expected a visibility edit")
    original_edits, _ = BATCH["controls"](preceding)
    wrong_layout = original_edits["missing_buffer"][0]
    edits = {
        "null_count": (change_count(ipc, 0, 0), ".nullCount 0 0 1"),
        "bitmap_bit": (bitmap(ipc, 0, 2), ".nullCount 0 1 0"),
        "hidden_null_count": (change_count(ipc, 1, 0), ".nullCount 1 0 1"),
        "struct_required_exposed": (struct_reached, ".requiredNull 1 1"),
        "list_required_exposed": (list_reached, ".requiredNull 7 1"),
        "layout_precedence": (wrong_layout, ".layout (.missingBuffer 18)"),
    }
    return edits, bitmap(ipc, 0, 0xf0)


def lean_list(items):
    return "[" + ", ".join(items) + "]"


def lean_bits(bits):
    return "#" + lean_list(str(bit).lower() for bit in bits)


def lean_column(column):
    visible, validity, kind, payload, children = column
    p = "." + kind
    if kind == "list":
        p = f"(.list #{payload})"
    elif kind != "struct":
        words = lean_list(f"({word})" if word < 0 else str(word) for word in payload)
        p = f"({p} {words})"
    return f".node ⟨{lean_bits(visible)}, {lean_bits(validity)}⟩ {p} {lean_list(map(lean_column, children))}"


def guard(data, rows, columns, following=False):
    value = lean_list(map(lean_column, columns))
    return f"#guard sees {bytes_term(data)} {str(following).lower()} ⟨{rows}, {value}⟩"


def checks(pa, genuine, edits, padding):
    for label, data in genuine.items():
        _, cursor = metadata(data)
        for index, batch in enumerate(pa.ipc.open_stream(data)):
            record = read_record(data, cursor)
            columns = positional(pa, record, batch)
            yield guard(data, record.rows, columns, following=index == 1)
            if label == "hidden":
                padded = pa.ipc.open_stream(padding).read_next_batch()
                require(padded.equals(batch), "padding edit changed logical Arrow values")
                raw = read_record(padding, cursor)
                yield guard(padding, raw.rows, positional(pa, raw, padded))
                require(batch.column(1).to_pylist()[:2] == [{"left": None, "right": None}, None]
                        and batch.column(2).to_pylist()[1:3] == [None, []],
                        "expected distinct present-all-null Struct, absent Struct, null and empty List")
            cursor = record.end
            print(f"{label} batch {index}: {record.rows} rows and {len(record.nodes)} physical nodes")
    for data, wanted in edits.values():
        yield f"#guard refuses {bytes_term(data)} ({wanted})"


def main():
    import pyarrow as pa

    pins = json.loads(MANIFEST.read_text(encoding="utf-8"))
    require(platform.python_implementation() == "CPython" and
            platform.python_version() == pins["producer"]["cpython"], "CPython pin differs")
    require(pa.__version__ == pins["producer"]["pyarrow"], "PyArrow pin differs")
    genuine = produce(pa)
    edits, padding = controls(genuine["hidden"], genuine["four_level"])
    require({name: fingerprint(data) for name, data in genuine.items()} == pins["genuine_ipc"],
            "genuine IPC pins differ")
    actual = {name: fingerprint(data) for name, (data, _) in edits.items()}
    actual["bitmap_padding"] = fingerprint(padding)
    require(actual == pins["labeled_edits"], "labeled edit pins differ")
    with tempfile.TemporaryDirectory() as directory:
        driver = Path(directory) / "Check.lean"
        driver.write_text("\n".join([LEAN, *checks(pa, genuine, edits, padding)]), encoding="utf-8")
        subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                        str(driver)], cwd=ROOT, check=True)
    print(f"Checked {len(genuine)} genuine IPC pins, {len(actual)} labeled edits, and {len(edits)} typed refusals")


if __name__ == "__main__":
    main()
