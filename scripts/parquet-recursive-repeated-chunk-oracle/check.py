"""Check repeated signed V1 chunks against PyArrow and original page words."""

from dataclasses import dataclass
from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import struct
import subprocess
import tempfile
import zlib

import pyarrow as pa
import pyarrow.parquet as pq


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ORACLES = HERE.parent
SCHEMA = runpy.run_path(str(ORACLES / "parquet-recursive-list-schema-oracle/check.py"))
CHUNK = runpy.run_path(str(ORACLES / "parquet-recursive-chunk-oracle/check.py"))
CONT = runpy.run_path(str(ORACLES / "parquet-list-continuation/Oracle.py"))
MIXED, THRIFT, fingerprints, lst = (SCHEMA[key] for key in ("MIXED", "THRIFT", "fingerprints", "lst"))
FRAMES, HYBRID, path_term = (CHUNK[key] for key in ("FRAMES", "HYBRID", "path_term"))

LEAN = """\
module

import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Defs

open Silmaril Silmaril.Formats
open Parquet.RecursiveSchema.Repeated (openFile)
open Parquet.RecursiveSchema.Repeated.Chunk

set_option maxRecDepth 4096

private structure ExpectedPage where
  start : Cursor
  payload : Nat
  stop : Nat
  crc : Option UInt32
  after : State
  levels : List LevelSlot
  words : List (Option Word)

private def load (folder : System.FilePath) (label : String) : IO Bytes :=
  return ⟨← IO.FS.readBinFile (folder / (label ++ ".parquet"))⟩

private def take {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"unexpected refusal: {repr cause}")

private def deny {ε α : Type} [DecidableEq ε] [Repr ε] (wanted : ε) (result : Except ε α) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"accepted source expecting {repr wanted}")
  | .error actual =>
    unless actual = wanted do throw (IO.userError s!"expected {repr wanted}, got {repr actual}")

private def check (file : Bytes) (limits : Limits) (group column : Nat) (path : List String)
    (slots rows start stop : Nat) (expected : List ExpectedPage) : IO Unit := do
  let source ← take (openFile {} file)
  let binding ← take (bindChunk source.schema group column)
  unless binding.leaf.site.location.path = path ∧ binding.span.start = start ∧
      binding.span.stop = stop ∧ binding.chunk.metadata.numValues = Int.ofNat slots ∧
      binding.rowGroup.numRows = Int.ofNat rows do
    throw (IO.userError s!"original binding differs at ({group}, {column})")
  let seen ← take (Parquet.RecursiveSchema.Repeated.Chunk.read limits binding)
  unless seen.pages.length = expected.length do throw (IO.userError "page count differs")
  for (page, wanted) in seen.pages.zip expected do
    unless page.start = wanted.start ∧ page.frame.header.start = wanted.start.byte ∧
        page.frame.payload.start = wanted.payload ∧ page.frame.payload.stop = wanted.stop ∧
        page.frame.value.crc = wanted.crc ∧ page.decoded.after = wanted.after ∧
        page.decoded.levels = wanted.levels ∧ page.decoded.words = wanted.words do
      throw (IO.userError s!"page differs at ({group}, {column}, {wanted.start.page})")
  unless seen.levels.length = slots ∧ seen.levels.countP LevelSlot.startsRow = rows do
    throw (IO.userError "independent slot or row total differs")

private def refuse (file : Bytes) (group column : Nat) (limits : Limits) (wanted : Error) :
    IO Unit := do
  let source ← take (openFile {} file)
  let binding ← take (bindChunk source.schema group column)
  deny wanted (Parquet.RecursiveSchema.Repeated.Chunk.read limits binding)

private def checkLongList (file : Bytes) : IO Unit := do
  let source ← take (openFile {} file)
  let binding ← take (bindChunk source.schema 0 0)
  let count := ({} : Limits).maxSlots
  let classified ← take (classifySlots binding.leaf 1 (0 :: List.replicate (count - 1) 1)
    (List.replicate count 2) {})
  unless classified.levels.length = count ∧ classified.after = ⟨count, 1, true⟩ do
    throw (IO.userError "large bounded classification differs")
"""


@dataclass(frozen=True)
class Page:
    index: int
    header: int
    payload: int
    stop: int
    crc: int | None
    before: tuple
    after: tuple
    events: list


@dataclass(frozen=True)
class Column:
    group: int
    index: int
    path: tuple
    width: int
    start: int
    stop: int
    slots: int
    rows: int
    steps: tuple
    pages: list


def level_section(body, maximum, count):
    if not maximum:
        return [0] * count, body
    size, = struct.unpack_from("<I", body)
    assert size <= len(body) - 4
    return HYBRID(body[4:4+size], maximum.bit_length(), count), body[4+size:]


def from_arrow(row, field, path, repetition=0, definition=0):
    if row is None:
        assert field.nullable
        return [(repetition, definition, None)]
    definition += int(field.nullable)
    if pa.types.is_list(field.type):
        element = field.type.value_field
        assert path[:2] == ("list", element.name)
        if not row:
            return [(repetition, definition, None)]
        return [slot for index, item in enumerate(row)
                for slot in from_arrow(item, element, path[2:], repetition if index == 0 else 1,
                                       definition + 1)]
    if pa.types.is_struct(field.type):
        return from_arrow(row[path[0]], field.type.field(path[0]), path[1:], repetition, definition)
    assert not path and field.type in (pa.int32(), pa.int64())
    return [(repetition, definition, row)]


def capture(wire, schema, rows, checksummed=False):
    _, leaves = SCHEMA["describe"](wire, schema, rows)
    footer = MIXED["metadata"](wire)
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=checksummed)
    for group in range(parquet.num_row_groups):
        original_rows = parquet.read_row_group(group).to_pylist()
        for index, ((_, path), field, steps, boundary) in enumerate(leaves):
            metadata = THRIFT["column_metadata"](footer, group, index)
            start, stop = MIXED["column_extent"](metadata)
            assert metadata[6][1] == stop - start and metadata[4][1] == 0
            expected = [event for row in original_rows
                        for event in from_arrow(row[path[0]], schema.field(path[0]), path[1:])]
            slot, row, live, pages = 0, 0, False, []
            for page, (header, fields, payload, body) in enumerate(FRAMES(wire, start, stop)):
                assert fields[1][1] == 0 and fields[2][1] == fields[3][1] == len(body)
                assert (4 in fields) == checksummed
                crc = fields[4][1] & 0xffffffff if checksummed else None
                if checksummed:
                    assert crc == zlib.crc32(body)
                data = fields[5][1]
                count = data[1][1]
                assert [data[i][1] for i in (2, 3, 4)] == [0, 3, 3]
                reps, tail = level_section(body, int(boundary is not None), count)
                defs, tail = level_section(tail, len(steps), count)
                code = "<i" if field.type.bit_width == 32 else "<q"
                words = [word for word, in struct.iter_unpack(code, tail)]
                assert len(reps) == len(defs) == count and len(words) == defs.count(len(steps))
                values = iter(words)
                events = [(rep, level, next(values) if level == len(steps) else None)
                          for rep, level in zip(reps, defs, strict=True)]
                assert events == expected[slot:slot+count]
                before = (slot, row, live)
                for rep, definition, _ in events:
                    assert rep == 0 or live
                    live = boundary is not None and definition > boundary[2]
                    row += int(rep == 0)
                slot += count
                pages.append(Page(page, header, payload, payload+len(body), crc, before,
                                  (slot, row, live), events))
            assert pages[-1].stop == stop and slot == len(expected) == metadata[5][1]
            assert row == len(original_rows) == parquet.metadata.row_group(group).num_rows
            yield Column(group, index, path, field.type.bit_width, start, stop, slot, row, steps, pages)


def multipage(schema):
    rows = []
    for i in range(36):
        values = [None, {"items": None, "flag": 1}, {"items": [], "flag": 2}]
        items = [None] + [
            {"lo": -(2**31) if j == 0 else (2**31 - 1 if j == 1 else j-i),
             "nested": {"hi": (-(2**63) if i % 3 else 2**63-1) if j == 1 else None}
             if j % 2 else None}
            for j in range(i % 5 + 9)
        ]
        values.append({"items": items, "flag": i})
        rows.append({"packet": values[i % 4], "seq": 2**40+i})
    sink = pa.BufferOutputStream()
    pq.write_table(pa.Table.from_pylist(rows, schema=schema), sink, compression="NONE",
                   use_dictionary=False, data_page_version="1.0", data_page_size=40,
                   write_batch_size=2, write_page_checksum=True, use_compliant_nested_type=False,
                   store_schema=False, row_group_size=18)
    return sink.getvalue().to_pybytes(), rows


def continuation_fixtures(directory):
    native = CONT["write"](directory / "native.parquet", indexed=False)
    indexed = CONT["write"](directory / "indexed.parquet", indexed=True)
    footer_start, original = CONT["metadata"](native)
    footer = MIXED["metadata"](native)
    chunk = THRIFT["column_metadata"](footer, 0, 0)
    frames = list(FRAMES(native, *MIXED["column_extent"](chunk)))
    rep_words, def_words = [], []
    for _, header, payload, _ in frames:
        count = header[5][1][1][1]
        _, next_at, rep = CONT["section"](native, payload, 1, count)
        _, _, definition = CONT["section"](native, next_at, 2, count)
        rep_words.append(rep)
        def_words.append(definition)

    def changed(source, edits):
        data = bytearray(source)
        for at, value in edits:
            data[at] = value
        return bytes(data)

    rows_three, _ = CONT["change_footer_counts"](native, footer_start, original, 3)
    marker = bytes.fromhex("15 00 16 0c 16 8c 02")
    assert native.count(marker, footer_start) == 1
    slot_at = native.index(marker, footer_start) + 3
    edits = {
        "authored_continuation": changed(rows_three, [(rep_words[3], 3)]),
        "first_continuation": changed(native, [(rep_words[0], 1), (def_words[0], 2)]),
        "after_empty": changed(native, [(rep_words[2], 3)]),
        "wrong_row_total": changed(native, [(rep_words[3], 3)]),
        "wrong_slot_total": changed(native, [(slot_at, 14)]),
        "too_few_slots": changed(native, [(slot_at, 10)]),
        "too_few_rows": bytes(rows_three),
        "short_words": changed(native, [(def_words[3], 15)]),
        "extra_word": changed(native, [(def_words[3], 10)]),
        "repetition_extent": changed(native, [(frames[3][2], 255)]),
    }
    return native, indexed, edits


def fixtures(directory):
    old, samples, _ = SCHEMA["fixtures"]()
    nested_schema = samples["nullable_lists"][0]
    multi, rows = multipage(nested_schema)
    native, indexed, edits = continuation_fixtures(directory)
    genuine = {"nested": old["nullable_lists"], "mixed_required": old["required_lists"],
               "multipage_crc": multi, "native": native, "indexed": indexed}
    alone = pq.ParquetFile(pa.BufferReader(native)).schema_arrow
    positives = {
        "nested": (*samples["nullable_lists"], False),
        "mixed_required": (*samples["required_lists"], False),
        "multipage_crc": (nested_schema, rows, True),
        "native": (alone, [{"items": value} for value in CONT["ROWS"]], False),
        "authored_continuation": (alone, [{"items": value} for value in CONT["CONTINUED"]], False),
    }
    footer = MIXED["metadata"](multi)
    first = next(FRAMES(multi, *MIXED["column_extent"](THRIFT["column_metadata"](footer, 0, 0))))
    edited = bytearray(multi)
    edited[first[2] + len(first[3]) - 1] ^= 1
    edits["bad_crc"] = bytes(edited)
    return genuine, edits, positives


def state_term(state):
    slot, rows, live = state
    return f"⟨{slot}, {rows}, {str(live).lower()}⟩"


def cursor_term(page):
    return f"⟨{page.index}, {page.header}, {state_term(page.before)}⟩"


def page_term(column, page):
    levels, words = [], []
    for rep, definition, word in page.events:
        position = ".rowStart" if rep == 0 else ".continuation"
        presence = ".value" if definition == len(column.steps) else f".absent ({column.steps[definition]})"
        levels.append(f"⟨{rep}, {definition}, ⟨{position}, {presence}⟩⟩")
        words.append("none" if word is None else f"some (.int{column.width} ({word}))")
    crc = "none" if page.crc is None else f"(some {page.crc})"
    return (f"⟨{cursor_term(page)}, {page.payload}, {page.stop}, {crc}, {state_term(page.after)}, "
            f"{lst(levels)}, {lst(words)}⟩")


def check_term(column, label, limits="{}"):
    return (f'  check (← load folder "{label}") {limits} {column.group} {column.index} '
            f'{path_term(column.path)} {column.slots} {column.rows} {column.start} {column.stop} '
            f'{lst(page_term(column, page) for page in column.pages)}')


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    inherited = json.loads(SCHEMA["PREDECESSOR"]["MANIFEST"].read_text(encoding="utf-8"))["producer"]
    assert platform.python_implementation() == "CPython"
    assert platform.python_version() == inherited["cpython"]
    assert pa.__version__ == inherited["pyarrow"] and version("thrift") == inherited["thrift"]
    with tempfile.TemporaryDirectory() as directory:
        scratch = Path(directory)
        genuine, edits, positives = fixtures(scratch)
        assert fingerprints(genuine) == pins["genuine_parquet"]
        assert fingerprints(edits) == pins["labeled_edits"]
        all_files = genuine | edits
        code = [LEAN, "public def main (args : List String) : IO Unit := do",
                '  let [folder] := args | throw (IO.userError "expected fixture folder")']
        captured = {label: list(capture(all_files[label], *sample))
                    for label, sample in positives.items()}
        for label, columns in captured.items():
            code.extend(check_term(column, label) for column in columns)
            print(f"{label}: {len(columns)} chunks, {sum(len(column.pages) for column in columns)} pages",
                  flush=True)
        multipage_lo, multipage_hi, *_ = captured["multipage_crc"]
        assert len(multipage_lo.pages) > 1
        assert [page.before[1] for page in multipage_lo.pages] != [
            page.before[1] for page in multipage_hi.pages]
        [native] = captured["native"]
        [authored] = captured["authored_continuation"]
        assert authored.pages[3].before == (4, 3, True)
        assert authored.pages[3].events[0][:2] == (1, 3)
        code.append(check_term(authored, "authored_continuation",
                               "{ maxSlots := 6, maxRows := 3, framing.maxPages := 4 }"))
        address = f"⟨0, 0, {path_term(native.path)}⟩"

        def page_error(label, page, cause, limits="{}"):
            code.append(f'  refuse (← load folder "{label}") 0 0 {limits} '
                        f'(.page {address} {cursor_term(page)} ({cause}))')

        def chunk_error(label, cause, limits="{}"):
            code.append(f'  refuse (← load folder "{label}") 0 0 {limits} '
                        f'(.chunk {address} ⟨{native.start}, {native.stop}⟩ ({cause}))')

        page_error("first_continuation", native.pages[0], ".continuationWithoutList 0")
        page_error("after_empty", native.pages[2], ".continuationWithoutList 2")
        chunk_error("wrong_row_total", ".rowCount 4 3")
        chunk_error("wrong_slot_total", ".slotCount 7 6")
        page_error("too_few_slots", native.pages[3], ".slotOverrun 1 2")
        page_error("too_few_rows", native.pages[3], ".rowOverrun 4 3")
        page_error("short_words", native.pages[3], ".plain .truncated")
        page_error("extra_word", native.pages[3], ".plain .trailingBytes")
        page_error("repetition_extent", native.pages[3], ".repetition (.section .truncatedDefinitions)")
        chunk_error("authored_continuation", ".slotLimit 6", "{ maxSlots := 5 }")
        chunk_error("authored_continuation", ".rowLimit 3", "{ maxRows := 2 }")
        page_error("authored_continuation", authored.pages[3], ".framing .pageLimit",
                   "{ framing.maxPages := 3 }")
        crc_page = multipage_lo.pages[0]
        wrong_crc = zlib.crc32(edits["bad_crc"][crc_page.payload:crc_page.stop])
        code.extend([
            f'  refuse (← load folder "bad_crc") 0 0 {{}} '
            f'(.page ⟨0, 0, {path_term(multipage_lo.path)}⟩ {cursor_term(crc_page)} '
            f'(.checksum (.mismatch {crc_page.crc} {wrong_crc})))',
            '  checkLongList (← load folder "native")',
            '  let indexed ← take (openFile {} (← load folder "indexed"))',
            f'  deny (.column {address} .pageIndex) (bindChunk indexed.schema 0 0)',
        ])
        for label, wire in all_files.items():
            (scratch / f"{label}.parquet").write_bytes(wire)
        driver = scratch / "Check.lean"
        driver.write_text("\n".join(code) + "\n", encoding="utf-8")
        subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                        "--run", str(driver), directory], cwd=ROOT, check=True)
    print("Verified original level/value words, a live cross-page continuation and fourteen typed refusals")


if __name__ == "__main__":
    main()
