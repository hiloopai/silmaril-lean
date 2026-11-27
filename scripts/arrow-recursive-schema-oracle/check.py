"""Compare recursive Arrow V5 schema observations with pinned PyArrow and raw metadata."""

import hashlib
import json
from pathlib import Path
import platform
import struct
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
MANIFEST = Path(__file__).with_name("fixtures.json")
LEAN_DRIVER = """\
module

meta import Silmaril.Formats.Arrow.RecursiveSchema.Defs

open Silmaril Silmaril.Formats.Arrow.RecursiveSchema

private meta def agrees (actual : Except Error (Schema × Nat))
    (expected : Except Error (Schema × Nat)) : Bool :=
  match actual, expected with
  | .ok (schema, next), .ok (wanted, cursor) => schema == wanted && next == cursor
  | .error error, .error wanted => error == wanted
  | _, _ => false

private meta def hasValue {ε α : Type} [DecidableEq α] (actual : Except ε α)
    (expected : α) : Bool :=
  match actual with
  | .ok value => decide (value = expected)
  | .error _ => false
"""


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def scalar(data, position, code):
    return struct.unpack_from("<" + code, data, position)[0]


def target(data, position):
    return position + scalar(data, position, "I")


def slot(data, table, index):
    vtable = table - scalar(data, table, "i")
    index_offset = 4 + 2 * index
    if index_offset >= scalar(data, vtable, "H"):
        return None
    displacement = scalar(data, vtable + index_offset, "H")
    return table + displacement if displacement else None


def read_scalar(data, table, index, code):
    position = slot(data, table, index)
    return 0 if position is None else scalar(data, position, code)


def vector(data, table, index):
    position = slot(data, table, index)
    if position is None:
        return 0, 0
    start = target(data, position)
    return start + 4, scalar(data, start, "I")


def words(start, count):
    return range(start, start + 4 * count, 4)


def root_vector(data):
    message = target(data, 0)
    require(read_scalar(data, message, 0, "H") == 4, "expected V5")
    require(read_scalar(data, message, 1, "B") == 1, "expected Schema")
    require(read_scalar(data, message, 3, "Q") == 0, "expected a bodyless Schema")
    schema = target(data, slot(data, message, 2))
    require(read_scalar(data, schema, 0, "H") == 0, "expected little endian")
    return vector(data, schema, 1)


def original_fields(data, start, count):
    for word in words(start, count):
        position = target(data, word)
        string = target(data, slot(data, position, 0))
        length = scalar(data, string, "I")
        require(data[string + 4 + length] == 0, "missing string terminator")
        name = data[string + 4:string + 4 + length].decode("utf-8")
        nullable = read_scalar(data, position, 1, "B")
        require(nullable in (0, 1), "invalid nullability")
        tag = read_scalar(data, position, 2, "B")
        payload = target(data, slot(data, position, 3))
        width = None
        if tag == 2:
            width = read_scalar(data, payload, 0, "I")
            require(width in (32, 64) and read_scalar(data, payload, 1, "B") == 1,
                    "expected signed Int32 or Int64")
        else:
            require(tag in (12, 13), "unexpected recursion tag")
        children_span = vector(data, position, 5)
        children = list(original_fields(data, *children_span))
        yield ((name, bool(nullable), tag, width, [child[0] for child in children]),
               word, position, children_span, children)


def pyarrow_field(pa, field):
    kind = field.type
    if pa.types.is_struct(kind):
        tag, width, children = 13, None, list(kind)
    elif pa.types.is_list(kind):
        tag, width, children = 12, None, [kind.value_field]
    elif pa.types.is_int32(kind) or pa.types.is_int64(kind):
        tag, width, children = 2, kind.bit_width, []
    else:
        raise ValueError(kind)
    return field.name, field.nullable, tag, width, [pyarrow_field(pa, child) for child in children]


def stream(pa, schema, empty_batch=False, *, options=None):
    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, schema, options=options) as writer:
        if empty_batch:
            writer.write_batch(pa.record_batch([pa.nulls(0, f.type) for f in schema], schema=schema))
    return sink.getvalue().to_pybytes()


def fixtures(pa):
    nested = pa.schema([
        pa.field("地点", pa.struct([
            pa.field("bounds", pa.list_(pa.field("élément", pa.struct([
                pa.field("low", pa.int32(), nullable=False),
                pa.field("high", pa.int64()),
            ]), nullable=False))),
            pa.field("rank", pa.int64(), nullable=False),
        ])),
        pa.field("groups", pa.list_(pa.field("item", pa.list_(
            pa.field("tick", pa.int64())), nullable=False)), nullable=False),
        pa.field("empty", pa.struct([])),
        pa.field("groups", pa.int32(), nullable=False),
    ])
    main = stream(pa, nested, empty_batch=True)
    empty = stream(pa, pa.schema([]))
    unsigned = stream(pa, pa.schema([pa.field("s", pa.struct([pa.field("u", pa.uint64())]))]))
    large_list = stream(pa, pa.schema([pa.field("s", pa.struct([pa.field("l", pa.large_list(pa.int32()))]))]))
    custom = stream(pa, pa.schema([pa.field("s", pa.struct([
        pa.field("c", pa.int32(), metadata={b"feature": b"custom"})
    ]))]))
    legacy = stream(pa, nested, options=pa.ipc.IpcWriteOptions(use_legacy_format=True))
    v4 = stream(pa, nested, options=pa.ipc.IpcWriteOptions(metadata_version=pa.ipc.MetadataVersion.V4))

    data, _ = metadata(main)
    root_start, _ = root_vector(data)
    parent = target(data, root_start)
    children_start, _ = vector(data, parent, 5)
    list_position = target(data, children_start)
    child_start, _ = vector(data, list_position, 5)
    edits = {
        "child_vector_extent": (child_start - 4, "I", 0xffffffff, f".field {list_position} (.malformed .flatbuffer)"),
        "child_vector_offset": (slot(data, list_position, 5), "I", 0, f".field {list_position} (.malformed .flatbuffer)"),
        "child_slot_offset": (child_start, "I", 0, f".offset {child_start} (.malformed .flatbuffer)"),
        "child_table_alignment": (child_start, "I", 5, f".field {child_start + 5} (.malformed .flatbuffer)"),
        "list_arity_zero": (child_start - 4, "I", 0, f".arity {list_position} .list 0"),
        "list_arity_two": (slot(data, parent, 2), "B", 12, f".arity {parent} .list 2"),
    }
    controls = {}
    for label, (position, code, value, error) in edits.items():
        changed = bytearray(main)
        struct.pack_into("<" + code, changed, 8 + position, value)
        controls[label] = (bytes(changed), error)
    return ({"nested": main, "empty": empty, "unsigned": unsigned, "large_list": large_list,
             "field_metadata": custom, "legacy": legacy, "v4": v4}, controls)


def metadata(ipc):
    marker, size = struct.unpack_from("<II", ipc)
    require(marker == 0xffffffff and size > 0 and size % 8 == 0, "unexpected native prefix")
    end = 8 + size
    return ipc[8:end], end


def bytes_term(data):
    return f"(KBytes.leaf {len(data)} {int.from_bytes(data, 'little')})"


def kind_term(tag, width):
    return {2: f".int{width}", 12: ".list", 13: ".struct"}[tag]


def field_term(field):
    name, nullable, tag, width, children = field
    return (f".node (some {json.dumps(name, ensure_ascii=False)}) "
            f"{str(nullable).lower()} {kind_term(tag, width)} {fields_term(children)}")


def fields_term(fields):
    return "[" + ", ".join(field_term(field) for field in fields) + "]"


def assert_frame(ipc, expected, limits="{}"):
    return f"#guard agrees (readFrame {limits} {bytes_term(ipc)}) ({expected})"


def local_checks(nodes, depth=1):
    for (name, nullable, tag, width, _), word, position, (start, count), children in nodes:
        yield depth, position, (
            f"#guard hasValue (Wire.fieldOffset wire {word}) {position}",
            f"#guard hasValue (Wire.fieldHeader wire {position}) "
            f"⟨some {json.dumps(name, ensure_ascii=False)}, {str(nullable).lower()}, "
            f"{kind_term(tag, width)}, {start}, {count}⟩",
            f"#guard Wire.Kind.tag {kind_term(tag, width)} == {tag}",
        )
        yield from local_checks(children, depth + 1)


def descendant(ipc):
    data, _ = metadata(ipc)
    start, _ = root_vector(data)
    start, _ = vector(data, target(data, start), 5)
    return target(data, start)


def checks(pa, genuine, edits):
    for name in ("nested", "empty"):
        ipc = genuine[name]
        reader = pa.ipc.open_stream(ipc)
        expected_fields = [pyarrow_field(pa, field) for field in reader.schema]
        require([batch.num_rows for batch in reader] == ([0] if name == "nested" else []),
                f"{name}: unexpected batch sequence")
        data, end = metadata(ipc)
        start, count = root_vector(data)
        observed = list(original_fields(data, start, count))
        require([node[0] for node in observed] == expected_fields, f"{name}: original field tree differs")
        yield f"private meta def wire : KBytes := {bytes_term(data)}" if name == "nested" else ""
        local = list(local_checks(observed))
        total = len(local)
        depth = max((level for level, _, _ in local), default=0)
        limits = f"{{ depth := {depth}, ipc := {{ fields := {total} }} }}"
        yield assert_frame(ipc, f".ok (⟨{fields_term(expected_fields)}⟩, {end})", limits)
        if name == "nested":
            require(depth == 4 and total == 11, "expected a four-level, eleven-field schema")
            yield f"#guard hasValue (Wire.rootFields {{}} wire) ({start}, {count})"
            for _, _, guards in local:
                yield from guards
            first_at_depth = next(pos for level, pos, _ in local if level == depth)
            yield assert_frame(ipc, f".error (.depth {first_at_depth})", f"{{ depth := {depth - 1} }}")
            # The final root would fit under a per-vector check; descendants have used its budget.
            yield assert_frame(ipc, f".error (.fields {local[-1][1]})",
                               f"{{ ipc := {{ fields := {total - 1} }} }}")
            yield assert_frame(ipc, ".error (.envelope (.limit .metadataBytes))",
                               f"{{ ipc := {{ metadataBytes := {len(data) - 1} }} }}")
            yield assert_frame(ipc[:end - 1], ".error (.envelope (.malformed .truncated))")
            yield assert_frame(ipc[end:], ".error (.metadata (.unsupported (.messageKind 3)))")
        print(f"{name}: {total} original field occurrences, depth {depth}, schema ends at byte {end}")

    errors = {
        "unsigned": lambda ipc: f".field {descendant(ipc)} (.unsupported .fieldInteger)",
        "large_list": lambda ipc: f".field {descendant(ipc)} (.unsupported (.fieldType 21))",
        "field_metadata": lambda ipc: f".field {descendant(ipc)} (.unsupported .customMetadata)",
        "legacy": lambda _: ".envelope (.unsupported .legacyFraming)",
        "v4": lambda _: ".metadata (.unsupported (.metadataVersion 3))",
    }
    for label, error in errors.items():
        yield assert_frame(genuine[label], f".error ({error(genuine[label])})")
    for ipc, error in edits.values():
        yield assert_frame(ipc, f".error ({error})")


def fingerprint(data):
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def main():
    import pyarrow as pa

    pins = json.loads(MANIFEST.read_text(encoding="utf-8"))
    require(platform.python_implementation() == "CPython" and
            platform.python_version() == pins["producer"]["cpython"], "CPython pin differs")
    require(pa.__version__ == pins["producer"]["pyarrow"], "PyArrow pin differs")
    genuine, edits = fixtures(pa)
    require({name: fingerprint(data) for name, data in genuine.items()} == pins["genuine_ipc"],
            "genuine IPC pins differ")
    require({name: fingerprint(data) for name, (data, _) in edits.items()} == pins["labeled_edits"],
            "labeled edit pins differ")
    with tempfile.TemporaryDirectory() as directory:
        driver = Path(directory) / "Check.lean"
        driver.write_text("\n".join([LEAN_DRIVER, *checks(pa, genuine, edits)]), encoding="utf-8")
        subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                        str(driver)], cwd=ROOT, check=True)
    print(f"Checked {len(genuine)} genuine IPC pins, {len(edits)} labeled edits, and 16 typed refusals")


if __name__ == "__main__":
    main()
