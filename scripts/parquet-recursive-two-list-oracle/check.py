"""Inspect original two-LIST signed V1 levels and words independently of Lean."""

from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import struct
import tempfile
import zlib

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
V1 = runpy.run_path(str(HERE.parent / "parquet-recursive-dictionary-v1-oracle/check.py"))
V2, CHUNK, THRIFT, MIXED, FRAMES, fingerprints, lst = (
    V1[key] for key in ("V2", "CHUNK", "THRIFT", "MIXED", "FRAMES", "fingerprints", "lst")
)
raw_chunks, header_body, repack, encode = (V1[key] for key in ("raw_chunks", "header_body", "repack", "encode"))
SCHEMA = V1["SCHEMA"]
PATH = ["series", "list", "element", "list", "element"]

LEAN = """\
module

import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk.Defs

open Silmaril.Formats (Bytes)
open Silmaril.Formats.Parquet
open RecursiveSchema.TwoList
open RecursiveSchema.TwoList.Chunk

private def take {ε α : Type} [Repr ε] (input : Except ε α) : IO α :=
  match input with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def deny {ε α : Type} [DecidableEq ε] [Repr ε] (wanted : ε) (input : Except ε α) : IO Unit :=
  match input with
  | .ok _ => throw (IO.userError s!"unexpected acceptance, expected {reprStr wanted}")
  | .error error =>
    unless error = wanted do throw (IO.userError s!"expected {reprStr wanted}, got {reprStr error}")

private def load (folder : System.FilePath) (label : String) : IO Bytes :=
  return ⟨← IO.FS.readBinFile (folder / (label ++ ".parquet"))⟩

private structure ExpectedPage where
  span : Nat × Nat × Nat
  crc : Option UInt32
  start : State
  stop : State
  slots : List Slot
  words : List (Option Word)

private def checkChunk (file : Bytes) (group : Nat) (nullable : List Bool)
    (steps : Nat × Nat × Nat) (kind : RecursiveSchema.Kind) (span : Footer.Span)
    (stop : State) (pages : List ExpectedPage) : IO Unit := do
  let source ← take (openFile {} file)
  let plan := source.schema.plan
  unless [plan.outer.site.nullable, plan.inner.site.nullable, plan.leaf.nullable] = nullable ∧
      (plan.outerEmpty, plan.innerEmpty, plan.maxDefinition) = steps ∧ plan.kind = kind ∧
      plan.leaf.location.path = ["series", "list", "element", "list", "element"] do
    throw (IO.userError "original two-LIST declaration or thresholds differ")
  let binding ← take (Chunk.bind source.schema group)
  let observed ← take (read {} binding)
  unless observed.stop = stop ∧ observed.pages.length = pages.length ∧ binding.span = span do
    throw (IO.userError "original chunk extent, counts or final cursor differ")
  for (page, expected) in observed.pages.zip pages do
    let frame := page.frame
    unless (frame.header.start, frame.payload.start, frame.payload.stop) = expected.span ∧
        frame.value.crc = expected.crc ∧ page.start = expected.start ∧ page.decoded.after = expected.stop ∧
        page.decoded.levels = expected.slots ∧ page.decoded.words = expected.words do
      throw (IO.userError "original frame, levels, words or page cursor differ")

private def refuse (file : Bytes) (group : Nat) (limits : Limits) (error : Chunk.Error) : IO Unit := do
  let source ← take (openFile {} file)
  let binding ← take (Chunk.bind source.schema group)
  deny error (read limits binding)

private def refuseBind (file : Bytes) (error : BindError) : IO Unit := do
  let source ← take (openFile {} file)
  deny error (Chunk.bind source.schema 0)

private def refuseOldProfile (file : Bytes) : IO Unit :=
  deny (.nestedRepeated ⟨3, ["series", "list", "element"]⟩ ⟨2, ["series", "list"]⟩)
    (RecursiveSchema.Repeated.openFile {} file)

private def unequalLevelCounts (file : Bytes) : IO Unit := do
  let source ← take (openFile {} file)
  deny (.levelCount 0) (classify source.schema.plan 1 {} [] [0])

set_option maxRecDepth 8192
"""


def samples(nullable, width):
    outer, inner, value = nullable
    edge = 1 << (width - 1)
    null_inner = None if inner else []
    null_value = None if value else 0
    group0 = ([None] if outer else []) + [[], [null_inner, [], [-edge, null_value, edge - 1]], [[2], [3, 4]]]
    group1 = [[], [[7], null_inner, [], [null_value, -9]], [[0, 1], [], [2, 3]], [[edge - 1, -edge]]]
    return [group0, group1]


def schema_for(nullable, width):
    outer, inner, value = nullable
    signed = pa.int32() if width == 32 else pa.int64()
    return pa.schema([pa.field("series", pa.list_(pa.field("element", pa.list_(pa.field("element", signed, value)),
                                                          inner)), outer)])


def write(schema, groups, **options):
    sink = pa.BufferOutputStream()
    settings = dict(compression="NONE", use_dictionary=False, data_page_version="1.0", store_schema=False,
                    use_compliant_nested_type=True, write_page_checksum=True, write_page_index=False,
                    data_page_size=64, write_batch_size=2, max_rows_per_page=2)
    with pq.ParquetWriter(sink, schema, **(settings | options)) as writer:
        for group in groups:
            writer.write_table(pa.Table.from_arrays([pa.array(group, type=schema.field(0).type)], schema=schema))
    return sink.getvalue().to_pybytes()


def thresholds(nullable):
    outer, inner, leaf = nullable
    return int(outer), 1 + outer + inner, 2 + outer + inner + leaf


def expected_slots(group, nullable):
    outer, inner, maximum = thresholds(nullable)
    slots = []
    for row in group:
        if row is None or not row:
            slots.append((0, 0 if row is None else outer, None))
            continue
        for index, values in enumerate(row):
            rep = int(index != 0)
            if values is None or not values:
                slots.append((rep, outer + 1 if values is None else inner, None))
                continue
            for i, value in enumerate(values):
                slots.append((2 if i else rep, inner + 1 if value is None else maximum, value))
    return slots


def inspect(wire, nullable, width, groups):
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=True)
    assert parquet.schema_arrow.equals(schema_for(nullable, width))
    assert parquet.num_row_groups == len(groups)
    outer, inner, maximum = thresholds(nullable)
    for position, metadata, start, stop in V2["columns"](wire):
        group, column = position
        assert column == 0 and metadata[4][1] == 0 and [name.decode() for name in metadata[3][1][1]] == PATH
        assert parquet.read_row_group(group).column(0).to_pylist() == groups[group]
        expected = expected_slots(groups[group], nullable)
        assert metadata[5][1] == len(expected) and metadata[6][1] == metadata[7][1] == stop - start
        cursor, pages = (0, 0, 0), []
        for at, header, payload, body in FRAMES(wire, start, stop):
            crc = zlib.crc32(body)
            assert header[1][1] == 0 and header[2][1] == header[3][1] == len(body)
            assert header[4][1] & 0xffffffff == crc
            data = header[5][1]
            count = data[1][1]
            assert [data[i][1] for i in (2, 3, 4)] == [0, 3, 3]
            reps, rest = CHUNK["level_section"](body, 2, count)
            defs, suffix = CHUNK["level_section"](rest, maximum, count)
            assert len(suffix) == defs.count(maximum) * (width // 8)
            words = iter(word for word, in struct.iter_unpack("<i" if width == 32 else "<q", suffix))
            trace = [(r, d, next(words) if d == maximum else None) for r, d in zip(reps, defs, strict=True)]
            slots, rows, live = before = cursor
            assert trace == expected[slots:slots + count]
            for rep, definition, _ in trace:
                reached = int(outer < definition) + int(inner < definition)
                assert rep <= min(live, reached) and 0 <= definition <= maximum
                live = reached
                rows += rep == 0
            cursor = slots + count, rows, live
            pages.append((at, payload, payload + len(body), crc, before, cursor, trace))
        assert cursor[:2] == (len(expected), len(groups[group]))
        assert pages[0][0] == start and pages[-1][2] == stop
        yield group, start, stop, cursor, pages


def frame(template, events, width, *, extra_rep=b"", extra_word=b"", crc=True):
    header, _ = header_body(template)
    header[5][1][1] = TType.I32, len(events)
    reps = b"".join(bytes([2, r]) for r, _, _ in events) + extra_rep
    defs = b"".join(bytes([2, d]) for _, d, _ in events)
    body = (struct.pack("<I", len(reps)) + reps + struct.pack("<I", len(defs)) + defs +
            b"".join(struct.pack("<i" if width == 32 else "<q", w) for _, _, w in events if w is not None) +
            extra_word)
    return encode(header, body, crc=crc)


def state_term(cursor):
    slots, rows, live = cursor
    return f"⟨{slots}, {rows}, .{('closed', 'outer', 'inner')[live]}⟩"


def page_term(page, nullable, width):
    at, payload, stop, crc, before, after, trace = page
    outer, inner, maximum = thresholds(nullable)
    tags = {outer: "emptyOuter", inner: "emptyInner", maximum: "value"}
    if nullable[0]:
        tags[0] = "nullOuter"
    if nullable[1]:
        tags[outer + 1] = "nullInner"
    if nullable[2]:
        tags[inner + 1] = "nullValue"
    positions = ("rowStart", "innerStart", "innerContinue")
    slots = lst(f"⟨{r}, {d}, .{positions[r]}, .{tags[d]}⟩" for r, d, _ in trace)
    words = lst("none" if w is None else f"(some (.int{width} ({w})))" for _, _, w in trace)
    return f"⟨({at}, {payload}, {stop}), some {crc}, {state_term(before)}, {state_term(after)}, {slots}, {words}⟩"


def verify(scratch):
    positives, genuine, edits = {}, {}, {}
    for bits in range(8):
        nullable = tuple(bool(bits & (1 << bit)) for bit in range(3))
        width = 32 if bits % 2 == 0 else 64
        label = f"native_{bits}"
        rows = samples(nullable, width)
        positives[label] = nullable, width, rows
        genuine[label] = write(schema_for(nullable, width), rows)
    nullable, width, rows = (True, True, True), 32, samples((True, True, True), 32)
    schema = schema_for(nullable, width)
    genuine["native_full_int32"] = write(schema, rows)
    positives["native_full_int32"] = nullable, width, rows
    genuine["snappy"] = write(schema, rows, compression="SNAPPY")
    genuine["indexes"] = write(schema, rows, write_page_index=True)

    source = genuine["native_full_int32"]
    original = list(inspect(source, nullable, width, rows))
    _, _, _, _, original_pages = original[1]
    events = [event for *_, trace in original_pages for event in trace]
    assert [(r, d) for r, d, _ in events[:6]] == [(0, 1), (0, 5), (1, 2), (1, 3), (1, 4), (2, 5)]
    key = (1, 0)
    carrier = raw_chunks(source)
    template = carrier[key][0]
    cuts = [events[i:i + 1] for i in range(5)] + [events[5:]]
    rewritten = [frame(template, segment, width) for segment in cuts]
    edits["continued"] = repack(source, carrier | {key: rewritten})
    positives["continued"] = nullable, width, rows

    def patch(label, ordinal, first=None, **options):
        segment = cuts[ordinal]
        if first is not None:
            segment = [first, *segment[1:]]
        changed = frame(template, segment, width, **options)
        pages = rewritten[:ordinal] + [changed] + rewritten[ordinal + 1:]
        edits[label] = repack(source, carrier | {key: pages})

    patch("closed_outer", 1, (1, 5, 7))
    patch("stale_inner", 3, (2, 5, 7))
    patch("unreached_outer", 2, (1, 1, None))
    patch("unreached_inner", 5, (2, 3, None))
    patch("bad_rep", 5, (3, 5, -9))
    patch("bad_def", 5, (2, 6, None))
    patch("trailing_rep", 5, extra_rep=b"\x02\0")
    patch("extra_word", 5, extra_word=b"\0")
    patch("bad_crc", 5, crc=False)
    for label, delta in (("slot_total", 1), ("slot_overrun", -1), ("row_total", 1),
                         ("too_many_rows", -1), ("footer_extent", 1)):
        footer = MIXED["metadata"](edits["continued"])
        meta = THRIFT["column_metadata"](footer, *key)
        if label.startswith("slot"):
            meta[5] = TType.I64, meta[5][1] + delta
        elif label == "footer_extent":
            meta[6] = TType.I64, meta[6][1] + delta
        else:
            group = THRIFT["list_field"](footer, 4)[1]
            group[3] = TType.I64, group[3][1] + delta
            footer[3] = TType.I64, footer[3][1] + delta
        edits[label] = SCHEMA["pack"](edits["continued"], footer)

    files = genuine | edits
    for label, wire in files.items():
        (scratch / f"{label}.parquet").write_bytes(wire)
    code, captured, frame_count = [LEAN, *V1["ENTRY"]], {}, 0
    for label, (nullable, width, rows) in positives.items():
        captured[label] = list(inspect(files[label], nullable, width, rows))
        for group, lo, hi, end, pages in captured[label]:
            opts = lst(str(value).lower() for value in nullable)
            outer, inner, end_def = thresholds(nullable)
            terms = lst(page_term(page, nullable, width) for page in pages)
            code.append(f'  checkChunk (← load folder "{label}") {group} {opts} ({outer}, {inner}, {end_def}) '
                        f'.int{width} ⟨{lo}, {hi}⟩ {state_term(end)} {terms}')
            frame_count += len(pages)

    _, lo, hi, stop, pages = captured["continued"][1]
    assert [page[-1][0][0] for page in pages] == [0, 0, 1, 1, 1, 2]
    address = f"⟨1, 0, {json.dumps(PATH)}⟩"

    def chunk_error(label, cause, limits="{}"):
        code.append(f'  refuse (← load folder "{label}") 1 {limits} (.chunk {address} ⟨{lo}, {hi}⟩ ({cause}))')

    def page_error(label, ordinal, cause, limits="{}"):
        begin, end = next((begin, end) for position, _, begin, end in V2["columns"](files[label]) if position == key)
        offset = list(FRAMES(files[label], begin, end))[ordinal][0]
        start = state_term(pages[ordinal][4])
        code.append(f'  refuse (← load folder "{label}") 1 {limits} (.page {address} {ordinal} {offset} {start} ({cause}))')

    page_error("closed_outer", 1, ".level (.closedAncestor 1 1 .closed)")
    page_error("stale_inner", 3, ".level (.closedAncestor 3 2 .outer)")
    page_error("unreached_outer", 2, ".level (.unreachedAncestor 2 1 1)")
    page_error("unreached_inner", 5, ".level (.unreachedAncestor 5 2 3)")
    page_error("bad_rep", 5, ".level (.repetition 5 3)")
    page_error("bad_def", 5, ".level (.definition 5 6 5)")
    page_error("trailing_rep", 5, ".repetition (.hybrid .trailingBytes)")
    page_error("extra_word", 5, ".plain .trailingBytes")
    _, h, _, body = list(FRAMES(files["bad_crc"], *next((begin, end) for position, _, begin, end in
                                V2["columns"](files["bad_crc"]) if position == key)))[5]
    page_error("bad_crc", 5, f".checksum (.mismatch {h[4][1] & 0xffffffff} {zlib.crc32(body)})")
    page_error("continued", 0, ".checksum .byteLimit", "{ maxBodyBytes := 0 }")
    page_error("slot_overrun", 5, f".slotOverrun {stop[0] - 6} {stop[0] - 5}")
    row_start = next(i for i, slot in reversed(list(enumerate(events))) if slot[0] == 0)
    page_error("too_many_rows", 5, f".level (.rowLimit {row_start} {stop[1] - 1})")

    chunk_error("continued", ".chunkLimit", "{ maxChunkBytes := 0 }")
    chunk_error("continued", ".slotLimit", "{ maxSlots := 0 }")
    chunk_error("continued", ".rowLimit", "{ maxRows := 0 }")
    chunk_error("continued", ".framing .pageLimit", "{ framing.maxPages := 5 }")
    chunk_error("slot_total", f".slotCount {stop[0] + 1} {stop[0]}")
    chunk_error("row_total", f".rowCount {stop[1] + 1} {stop[1]}")
    chunk_error("footer_extent", f".uncompressedSize {hi - lo + 1} {hi - lo}")
    address0 = f"⟨0, 0, {json.dumps(PATH)}⟩"
    code.extend([f'  refuseBind (← load folder "snappy") (.column {address0} (.codec 1))',
                 f'  refuseBind (← load folder "indexes") (.column {address0} .pageIndex)',
                 '  refuseOldProfile (← load folder "native_full_int32")',
                 '  unequalLevelCounts (← load folder "native_full_int32")'])
    V2["run_lean"](scratch, "TwoList.lean", code)
    print(f"Checked {frame_count} original frames, {len(positives)} positive files and 23 typed refusals")
    return {"genuine": fingerprints(genuine), "authored": fingerprints(edits)}


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert pins["producer"] == {"cpython": platform.python_version(), "pyarrow": pa.__version__,
                                "thrift": version("thrift")}
    with tempfile.TemporaryDirectory() as directory:
        captured = verify(Path(directory))
    for name, fixtures in captured.items():
        assert fixtures == pins[name], f"{name} fixture pins changed"


if __name__ == "__main__":
    main()
