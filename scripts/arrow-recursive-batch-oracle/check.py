"""Check recursive RecordBatch layouts against PyArrow and original IPC words."""

from dataclasses import dataclass
import json
from pathlib import Path
import platform
import runpy
import struct
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
MANIFEST = Path(__file__).with_name("fixtures.json")
SCHEMA_ORACLE = runpy.run_path(str(ROOT / "scripts/arrow-recursive-schema-oracle/check.py"))
metadata = SCHEMA_ORACLE["metadata"]
target = SCHEMA_ORACLE["target"]
slot = SCHEMA_ORACLE["slot"]
vector = SCHEMA_ORACLE["vector"]
read_scalar = SCHEMA_ORACLE["read_scalar"]
require = SCHEMA_ORACLE["require"]
fingerprint = SCHEMA_ORACLE["fingerprint"]
LEAN = """\
module

meta import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Defs

open Silmaril
open Silmaril.Formats.Arrow.Body (sliceBuffer offsetAt)
open Silmaril.Formats.Arrow.RecursiveSchema.Wire (BatchHeader)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch

private meta def refuses (limits : Limits) (input : KBytes) (wanted : Error) : Bool :=
  match readFirst limits input with
  | .error cause => cause == wanted
  | .ok _ => false

private meta def seesFrame {limits : Limits} {schema : Silmaril.Formats.Arrow.RecursiveSchema.Schema}
    {input : KBytes} {start : Nat} (frame : Frame limits schema input start)
    (wantedStart : Nat) (expected : BatchHeader)
    (wantedNext slots : Nat) (layouts : List FieldLayout) (regions : List (Nat × Nat × KBytes))
    (lists : List (Nat × Nat × List Nat)) : Bool :=
  start == wantedStart && decide (frame.header = expected) && frame.next == wantedNext &&
  frame.layout.fields.next.slots == slots && frame.layout.fields.layouts == layouts &&
  regions.all (fun (offset, length, bytes) =>
    (sliceBuffer frame.body ⟨offset, length⟩).sameBytes 32 bytes) &&
  lists.all (fun (offset, length, words) =>
    let bytes := sliceBuffer frame.body ⟨offset, length⟩
    (List.range words.length).map (offsetAt bytes) == words.map some)

private meta def sees (limits : Limits) (input : KBytes) (following : Bool) (start : Nat)
    (expected : BatchHeader) (wantedNext slots : Nat) (layouts : List FieldLayout)
    (regions : List (Nat × Nat × KBytes)) (lists : List (Nat × Nat × List Nat)) : Bool :=
  match readFirst limits input with
  | .error _ => false
  | .ok first =>
    if following then
      match readFrame limits first.schema input first.batch.next with
      | .error _ => false
      | .ok second => seesFrame second start expected wantedNext slots layouts regions lists
    else seesFrame first.batch start expected wantedNext slots layouts regions lists
"""


@dataclass
class Record:
    start: int
    metadata: bytes
    body: bytes
    rows: int
    node_start: int
    nodes: list
    buffer_start: int
    buffers: list

    @property
    def body_start(self):
        return self.start + 8 + len(self.metadata)

    @property
    def end(self):
        return self.body_start + len(self.body)


def read_record(ipc, start):
    marker, length = struct.unpack_from("<II", ipc, start)
    require(marker == 0xffffffff and length > 0 and length % 8 == 0, "unexpected RecordBatch prefix")
    data = ipc[start + 8:start + 8 + length]
    message = target(data, 0)
    require(read_scalar(data, message, 0, "H") == 4, "expected V5 RecordBatch")
    require(read_scalar(data, message, 1, "B") == 3, "expected RecordBatch tag")
    body_length = read_scalar(data, message, 3, "q")
    record = target(data, slot(data, message, 2))
    rows = read_scalar(data, record, 0, "q")
    node_start, nodes = vector(data, record, 1)
    buffer_start, buffers = vector(data, record, 2)
    node_words = [struct.unpack_from("<qq", data, node_start + 16 * index) for index in range(nodes)]
    buffer_words = [struct.unpack_from("<qq", data, buffer_start + 16 * index) for index in range(buffers)]
    body_start = start + 8 + length
    return Record(start, data, ipc[body_start:body_start + body_length], rows,
                  node_start, node_words, buffer_start, buffer_words)


def produce(pa):
    original = SCHEMA_ORACLE["fixtures"](pa)[0]["nested"]
    schema = pa.ipc.open_stream(original).schema
    rows = [
        [{"bounds": [{"low": -(2**31), "high": -(2**63)}, {"low": 7, "high": None}], "rank": 4},
         None, {"bounds": None, "rank": -9},
         {"bounds": [{"low": 2**31 - 1, "high": 2**63 - 1}], "rank": -4}],
        [[[-1, None], []], [], [[-2**40]], [[0, 1], [2**40]]],
        [{}, None, {}, {}],
        [-2**31, -1, 0, 2**31 - 1],
    ]
    batch = pa.record_batch([pa.array(values, type=field.type)
                             for values, field in zip(rows, schema, strict=True)], schema=schema)

    def emit(options=None):
        sink = pa.BufferOutputStream()
        with pa.ipc.new_stream(sink, schema, options=options) as stream:
            stream.write_batch(batch)
            stream.write_batch(batch.slice(0, 0))
        return sink.getvalue().to_pybytes()

    populated = emit()
    require(metadata(populated) == metadata(original), "producer changed the pinned four-level schema")
    first, second = list(pa.ipc.open_stream(populated))
    require(first.equals(batch) and second.num_rows == 0, "genuine producer IPC rows differ")
    compressed = emit(pa.ipc.IpcWriteOptions(compression="lz4"))
    empty_schema_batch = pa.RecordBatch.from_struct_array(pa.array([{}, {}], type=pa.struct([])))
    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, empty_schema_batch.schema) as stream:
        stream.write_batch(empty_schema_batch)
    empty_schema = sink.getvalue().to_pybytes()
    return {"populated": populated, "predecessor_empty": original,
            "empty_schema": empty_schema, "compressed": compressed}


def inspect(pa, batch, record):
    nodes = iter(record.nodes)
    buffers = iter(record.buffers)
    regions = []
    lists = []

    def region(physical):
        offset, length = next(buffers)
        raw = record.body[offset:offset + length]
        require(len(raw) == length and offset % 8 == 0, "raw region differs")
        require(raw == (bytes(physical) if physical is not None else b""),
                "original region differs from PyArrow's physical buffer")
        regions.append((offset, length, raw))
        return (offset, length), raw

    def walk(array):
        node = next(nodes)
        require(node == (len(array), array.null_count), "raw node words differ from PyArrow")
        physical = array.buffers()
        validity, _ = region(physical[0])
        payload = None
        children = []
        if pa.types.is_struct(array.type):
            children = [walk(array.field(index)) for index in range(array.type.num_fields)]
        else:
            payload, raw = region(physical[1])
            if pa.types.is_list(array.type):
                words = [word[0] for word in struct.iter_unpack("<i", raw[:4 * (len(array) + 1)])]
                require(words == array.offsets.to_pylist() and words[-1] == len(array.values),
                        "original offsets or terminal child length differ from PyArrow")
                lists.append((*payload, words))
                children = [walk(array.values)]
            else:
                require(array.type in (pa.int32(), pa.int64()), "unexpected primitive")
                require(len(raw) == (array.type.bit_width // 8) * len(array), "primitive extent differs")
        return node, validity, payload, children

    tree = [walk(batch.column(index)) for index in range(batch.num_columns)]
    require(next(nodes, None) is None and next(buffers, None) is None, "unconsumed original entries")
    return tree, regions, lists


def edit_record(ipc, record, position, code, value, *, vector_extent=None):
    changed = bytearray(record.metadata)
    struct.pack_into("<" + code, changed, position, value)
    if vector_extent is not None and vector_extent > len(changed):
        changed.extend(b"\0" * ((vector_extent - len(changed) + 7) // 8 * 8))
    return (ipc[:record.start] + struct.pack("<II", 0xffffffff, len(changed)) +
            changed + ipc[record.body_start:])


def edit_body(ipc, record, position, code, value):
    changed = bytearray(ipc)
    struct.pack_into("<" + code, changed, record.body_start + position, value)
    return bytes(changed)


def controls(ipc):
    _, start = metadata(ipc)
    r = read_record(ipc, start)
    node_count, buffer_count = len(r.nodes), len(r.buffers)
    list_buffer = 2
    offsets, offsets_length = r.buffers[list_buffer]
    node_word = lambda index: r.node_start + 16 * index
    buffer_word = lambda index: r.buffer_start + 16 * index
    final = struct.unpack_from("<i", r.body, offsets + offsets_length - 4)[0]
    require(r.nodes[2][0] == final and final == 3, "expected List of three Struct slots")
    require(r.nodes[0][1] > 0 and r.buffers[0][1] > 0, "expected materialized parent bitmap")
    controls = {
        "missing_node": (edit_record(ipc, r, r.node_start - 4, "I", node_count - 1),
                         f".missingNode {node_count - 1}"),
        "missing_buffer": (edit_record(ipc, r, r.buffer_start - 4, "I", buffer_count - 1),
                           f".missingBuffer {buffer_count - 1}"),
        "extra_node": (edit_record(ipc, r, r.node_start - 4, "I", node_count + 1,
                                   vector_extent=node_word(node_count + 1)),
                       f".extraNodes {node_count} {node_count + 1}"),
        "extra_buffer": (edit_record(ipc, r, r.buffer_start - 4, "I", buffer_count + 1,
                                     vector_extent=buffer_word(buffer_count + 1)),
                         f".extraBuffers {buffer_count} {buffer_count + 1}"),
        "struct_child_length": (edit_record(ipc, r, node_word(1), "q", r.rows + 1),
                                f".nodeLength 1 {r.rows} {r.rows + 1}"),
        "list_terminal_length": (edit_body(ipc, r, offsets + offsets_length - 4, "i", final + 1),
                                 f".nodeLength 2 {final + 1} {final}"),
        "list_descending": (edit_body(ipc, r, offsets + 8, "i", 1), ".offsetOrder 2 2 2 1"),
        "list_negative": (edit_body(ipc, r, offsets + 4, "i", -1), ".offsetWord 2 1"),
        "list_nonzero_start": (edit_body(ipc, r, offsets, "i", 1), ".offsetStart 2 1"),
        "list_short": (edit_record(ipc, r, buffer_word(list_buffer) + 8, "q", offsets_length - 4),
                       f".payloadExtent 2 {offsets_length} {offsets_length - 4}"),
        "integer_short": (edit_record(ipc, r, buffer_word(buffer_count - 1) + 8, "q", 4 * r.rows - 4),
                          f".payloadExtent {buffer_count - 1} {4 * r.rows} {4 * r.rows - 4}"),
        "out_of_body": (edit_record(ipc, r, buffer_word(buffer_count - 1), "q", len(r.body)),
                        f".region {buffer_count - 1}"),
        "overlap": (edit_record(ipc, r, buffer_word(list_buffer), "q", 0), ".region 2"),
        "negative_node": (edit_record(ipc, r, node_word(0), "q", -1),
                          ".node 0 (.malformed .flatbuffer)"),
        "negative_buffer": (edit_record(ipc, r, buffer_word(0) + 8, "q", -1),
                            ".buffer 0 (.malformed .flatbuffer)"),
        "null_count_bound": (edit_record(ipc, r, node_word(0) + 8, "q", r.rows + 1),
                             f".nullCount 0 {r.rows} {r.rows + 1}"),
        "absent_bitmap": (edit_record(ipc, r, buffer_word(0) + 8, "q", 0), ".validityExtent 0"),
        "truncated_body": (ipc[:r.end - 1], ".body (.malformed .truncated)"),
    }
    # The profile only checks declared bitmap extent. Keep a mismatching count
    # and a physically allocated bitmap, but clear the contents.
    opaque_bitmap = edit_body(ipc, r, r.buffers[0][0], "B", 0)
    return controls, opaque_bitmap


def bytes_term(data):
    return f"(KBytes.leaf {len(data)} 0x{int.from_bytes(data, 'little'):x})"


def lean_tuple(pair):
    return f"⟨{pair[0]}, {pair[1]}⟩"


def lean_list(parts):
    return "[" + ", ".join(parts) + "]"


def lean_tree(tree):
    node, validity, payload, children = tree
    payload = f"(some {lean_tuple(payload)})" if payload is not None else "none"
    return f".field {lean_tuple(node)} {lean_tuple(validity)} {payload} {lean_list(map(lean_tree, children))}"


def assertion(ipc, record, tree, regions, lists, *, following=False, cap=None):
    slots = sum(length for length, _ in record.nodes)
    header = (f"⟨{len(record.body)}, {record.rows}, {record.node_start}, {len(record.nodes)}, "
              f"{record.buffer_start}, {len(record.buffers)}⟩")
    layout = lean_list(map(lean_tree, tree))
    regions = lean_list(f"({offset}, {length}, {bytes_term(data)})" for offset, length, data in regions)
    lists = lean_list(f"({offset}, {length}, {words})" for offset, length, words in lists)
    cap = slots if cap is None else cap
    return (f"#guard sees {{ slots := {cap} }} {bytes_term(ipc)} {str(following).lower()} {record.start} "
            f"{header} {record.end} {slots} {layout} {regions} {lists}")


def refusals(ipc, error, limits="{}"):
    return f"#guard refuses {limits} {bytes_term(ipc)} ({error})"


def checks(pa, genuine, edits, opaque_bitmap):
    for name in ("populated", "predecessor_empty", "empty_schema"):
        ipc = genuine[name]
        _, start = metadata(ipc)
        record = read_record(ipc, start)
        batch = pa.ipc.open_stream(ipc).read_next_batch()
        tree, regions, lists = inspect(pa, batch, record)
        yield assertion(ipc, record, tree, regions, lists)
        print(f"{name}: {record.rows} rows, {len(record.nodes)} nodes, {len(record.buffers)} buffers, "
              f"{len(lists)} List offset vectors")
        if name == "populated":
            trailing = read_record(ipc, record.end)
            require(list(pa.ipc.open_stream(ipc))[1].num_rows == 0, "expected empty second batch")
            second = inspect(pa, list(pa.ipc.open_stream(ipc))[1], trailing)
            slots = sum(length for length, _ in record.nodes)
            yield assertion(ipc, trailing, *second, following=True, cap=slots)
            yield refusals(ipc, f".slots {len(record.nodes) - 1}", f"{{ slots := {slots - 1} }}")
            yield refusals(ipc, ".metadata (.limit .rows)", "{ schema := { ipc := { rows := 3 } } }")
            yield refusals(ipc, ".body (.limit .bodyBytes)",
                           f"{{ schema := {{ ipc := {{ bodyBytes := {len(record.body) - 1} }} }} }}")
            end = record.end
            yield refusals(ipc[:start] + ipc[-8:], ".expectedRecord")
            require(end > record.body_start, "expected a real RecordBatch body")
            offset, length, _ = regions[0]
            changed = [(offset, length, b"\0")] + regions[1:]
            yield assertion(opaque_bitmap, record, tree, changed, lists)

    yield refusals(genuine["compressed"], ".metadata (.unsupported .compression)")
    yield refusals(edits["extra_node"][0], ".metadata (.limit .fields)",
                   "{ schema := { ipc := { fields := 11 } } }")
    for ipc, error in edits.values():
        yield refusals(ipc, error)


def main():
    import pyarrow as pa

    pins = json.loads(MANIFEST.read_text(encoding="utf-8"))
    require(platform.python_implementation() == "CPython" and
            platform.python_version() == pins["producer"]["cpython"], "CPython pin differs")
    require(pa.__version__ == pins["producer"]["pyarrow"], "PyArrow pin differs")
    genuine = produce(pa)
    edits, opaque = controls(genuine["populated"])
    require({name: fingerprint(data) for name, data in genuine.items()} == pins["genuine_ipc"],
            "genuine IPC pins differ")
    fingerprints = {name: fingerprint(data) for name, (data, _) in edits.items()}
    fingerprints["opaque_bitmap"] = fingerprint(opaque)
    require(fingerprints == pins["labeled_edits"], "labeled edit pins differ")
    with tempfile.TemporaryDirectory() as directory:
        driver = Path(directory) / "Check.lean"
        driver.write_text("\n".join([LEAN, *checks(pa, genuine, edits, opaque)]), encoding="utf-8")
        subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                        str(driver)], cwd=ROOT, check=True)
    print(f"Checked {len(genuine)} genuine IPC pins, {len(fingerprints)} labeled edits, "
          f"and {len(edits) + 6} typed refusals")


if __name__ == "__main__":
    main()
