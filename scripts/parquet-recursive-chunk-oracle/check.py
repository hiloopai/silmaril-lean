"""Compare Lean's native recursive V1 chunks with original PyArrow Parquet."""

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
from thrift.Thrift import TType


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
MANIFEST = HERE / "fixtures.json"
SCHEMA = runpy.run_path(str(HERE.parent / "parquet-recursive-schema-oracle/check.py"))
THRIFT, MIXED, FRAMES, HYBRID, describe, lst, path_term, location_term, pack, fingerprints = (
    SCHEMA[key] for key in ("THRIFT", "MIXED", "FRAMES", "HYBRID", "describe", "lst",
                            "path_term", "location_term", "pack", "fingerprints")
)

LEAN = """\
module

import Silmaril.Formats.Parquet.RecursiveSchema.Chunk.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Chunk.Defs

open Silmaril Silmaril.Formats
open Parquet.RecursiveSchema (openFile bindChunk)
open Parquet.RecursiveSchema.Chunk (Error Slot Limits)

private def takeResult {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def load (folder : System.FilePath) (name : String) : IO Bytes :=
  return ⟨← IO.FS.readBinFile (folder / (name ++ ".parquet"))⟩

private structure ExpectedPage where
  header : Nat
  start : Nat
  stop : Nat
  row : Nat
  crc : Option UInt32
  slots : List Slot

private def verify (file : Bytes) (groups : List (List (List ExpectedPage))) : IO Unit := do
  let source ← takeResult (openFile {} file)
  unless source.snapshot.groupCount = groups.length do throw (IO.userError "group count differs")
  for (columns, group) in groups.zipIdx do
    unless source.schema.leaves.size = columns.length do throw (IO.userError "column count differs")
    for (want, column) in columns.zipIdx do
      let binding ← takeResult (bindChunk source.schema group column)
      let seen ← takeResult (Parquet.RecursiveSchema.Chunk.read { framing.maxPages := want.length } binding)
      unless seen.rows = want.flatMap ExpectedPage.slots ∧ seen.pages.length = want.length do
        throw (IO.userError s!"wrong positions at {group}, {column}")
      for (page, expected) in seen.pages.zip want do
        unless page.frame.header.start = expected.header ∧ page.frame.payload.start = expected.start ∧
            page.frame.payload.stop = expected.stop ∧ page.firstRow = expected.row ∧
            page.frame.value.crc = expected.crc ∧ page.slots = expected.slots do
          throw (IO.userError s!"wrong frame at {group}, {column}, {expected.header}")

private def refuse (file : Bytes) (group column : Nat) (limits : Limits) (wanted : Error) :
    IO Unit := do
  let source ← takeResult (openFile {} file)
  let binding ← takeResult (bindChunk source.schema group column)
  match Parquet.RecursiveSchema.Chunk.read limits binding with
  | .ok _ => throw (IO.userError s!"accepted malformed input expecting {repr wanted}")
  | .error actual =>
    unless actual = wanted do throw (IO.userError s!"expected {repr wanted}, got {repr actual}")
"""


@dataclass
class Page:
    index: int
    header: int
    payload: int
    body: bytes
    fields: dict
    row: int
    levels: list
    slots: list

    @property
    def end(self):
        return self.payload + len(self.body)


@dataclass
class Column:
    group: int
    index: int
    location: tuple
    field: object
    steps: tuple
    start: int
    end: int
    pages: list

    @property
    def path(self):
        return self.location[1]

    @property
    def width(self):
        return len(self.steps).bit_length()


def write(schema, groups, *, checksum=False, version="1.0"):
    sink = pa.BufferOutputStream()
    with pq.ParquetWriter(sink, schema, compression="NONE", use_dictionary=False,
                          data_page_version=version, data_page_size=24, write_batch_size=2,
                          write_page_checksum=checksum, store_schema=False) as writer:
        for rows in groups:
            writer.write_table(pa.Table.from_pylist(rows, schema=schema))
    return sink.getvalue().to_pybytes()


def projected(row, path, steps):
    current = row
    for index, name in enumerate(path):
        current = current[name]
        if current is None:
            return next(position for position in steps if position[1] == path[:index+1]), None
    return None, current


def capture(wire, schema, groups, checksummed):
    footer = MIXED["metadata"](wire)
    leaves = describe(schema, footer)[1]
    parquet = pq.ParquetFile(pa.BufferReader(wire), page_checksum_verification=checksummed)
    assert parquet.schema_arrow.equals(schema) and parquet.num_row_groups == len(groups)
    for group, expected in enumerate(groups):
        rows = parquet.read_row_group(group).to_pylist()
        assert rows == expected
        for ordinal, (location, field, steps) in enumerate(leaves):
            column = THRIFT["column_metadata"](footer, group, ordinal)
            start, end = MIXED["column_extent"](column)
            assert column[6][1] == end - start and column[4][1] == 0
            cursor, pages = 0, []
            for index, (header, fields, payload, body) in enumerate(FRAMES(wire, start, end)):
                assert fields[1][1] == 0 and fields[2][1] == fields[3][1] == len(body)
                assert (4 in fields) == checksummed
                if checksummed:
                    assert zlib.crc32(body) == (fields[4][1] & 0xffffffff)
                info = fields[5][1]
                count = info[1][1]
                assert [info[i][1] for i in (2, 3, 4)] == [0, 3, 3]
                if steps:
                    extent, = struct.unpack_from("<I", body)
                    levels = HYBRID(body[4:4+extent], len(steps).bit_length(), count)
                    scalar_bytes = body[4+extent:]
                else:
                    levels, scalar_bytes = [0] * count, body
                code = "<i" if field.type.bit_width == 32 else "<q"
                words = [word for word, in struct.iter_unpack(code, scalar_bytes)]
                assert len(levels) == count and len(words) == levels.count(len(steps))
                scalars = iter(words)
                slots = [(None, next(scalars)) if level == len(steps) else (steps[level], None)
                         for level in levels]
                expected = [projected(row, location[1], steps) for row in rows[cursor:cursor+count]]
                assert slots == expected
                pages.append(Page(index, header, payload, body, fields, cursor, levels, slots))
                cursor += count
            assert cursor == len(rows) and pages[-1].end == end
            yield Column(group, ordinal, location, field, steps, start, end, pages)


def page_term(page, width):
    checksum = f"(some {page.fields[4][1] & 0xffffffff})" if 4 in page.fields else "none"
    sites = [f".value (.int{width} ({word}))" if missing is None else f".absent {location_term(missing)}"
             for missing, word in page.slots]
    return f"⟨{page.header}, {page.payload}, {page.end}, {page.row}, {checksum}, {lst(sites)}⟩"


def address(column):
    return f"⟨{column.group}, {column.index}, {path_term(column.path)}⟩"


def page_error(column, page, cause):
    return f".page {address(column)} ⟨{page.index}, {page.header}, {page.row}⟩ ({cause})"


def chunk_error(column, cause):
    return f".chunk {address(column)} ⟨{column.start}, {column.end}⟩ ({cause})"


def replace_level(wire, column, page, index, value):
    extent, = struct.unpack_from("<I", page.body)
    section = page.body[4:4+extent]
    assert section[0] == 3 and len(section) == column.width + 1
    packed = int.from_bytes(section[1:], "little")
    shift = column.width * index
    packed = (packed & ~(((1 << column.width) - 1) << shift)) | (value << shift)
    changed = bytes([3]) + packed.to_bytes(column.width, "little")
    expected = list(page.levels)
    expected[index] = value
    assert HYBRID(changed, column.width, len(expected)) == expected
    return wire[:page.payload+4] + changed + wire[page.payload+4+extent:]


def level_target(column, predicate):
    for page in column.pages[1:]:
        extent, = struct.unpack_from("<I", page.body)
        if page.body[4] == 3 and extent == column.width + 1:
            for index, level in enumerate(page.levels):
                if predicate(level):
                    return page, index
    raise AssertionError("missing a suitable late packed level")


def fixtures():
    prior = {name: (schema, groups, wire, False)
             for name, (schema, groups, wire) in SCHEMA["fixtures"]()[0].items()}
    schema, groups, _, _ = prior["deep"]
    longer = [groups[0] * 5, (groups[1] + groups[0]) * 5]
    admitted = {
        **prior,
        "multipage": (schema, longer, write(schema, longer), False),
        "checksummed": (schema, longer, write(schema, longer, checksum=True), True),
    }
    controls = {"v2": write(schema, groups, version="2.0")}
    return admitted, controls


def negative(admitted, controls, observations):
    wire = admitted["multipage"][2]
    target = next(col for col in observations["multipage"] if (col.group, col.index) == (1, 1))
    maximum = len(target.steps)
    assert maximum == 4 and len(target.pages) > 1
    absent, slot = level_target(target, lambda level: level < maximum)
    present, word_slot = level_target(target, lambda level: level == maximum)
    out_of_range = (f".definition (.level {location_term(target.location)} "
                    f"{absent.row+slot} {maximum+1} {maximum})")
    edits = {
        "late_level": (replace_level(wire, target, absent, slot, maximum+1), target,
                       page_error(target, absent, out_of_range)),
        "late_short_words": (replace_level(wire, target, absent, slot, maximum), target,
                             page_error(target, absent, ".plain .truncated")),
        "late_extra_word": (replace_level(wire, target, present, word_slot, maximum-1), target,
                            page_error(target, present, ".plain .trailingBytes")),
    }

    checksummed = admitted["checksummed"][2]
    crc_target = next(col for col in observations["checksummed"] if (col.group, col.index) == (1, 1))
    crc_page = crc_target.pages[-1]
    corrupted = bytearray(checksummed)
    corrupted[crc_page.end-1] ^= 1
    declared = crc_page.fields[4][1] & 0xffffffff
    computed = zlib.crc32(corrupted[crc_page.payload:crc_page.end])
    edits["late_crc"] = (bytes(corrupted), crc_target,
                         page_error(crc_target, crc_page, f".checksum (.mismatch {declared} {computed})"))

    last = target.pages[-1]
    def edit_header(fields):
        assert THRIFT["encode"](last.fields) == wire[last.header:last.payload]
        changed = THRIFT["encode"](fields)
        assert len(changed) == last.payload - last.header
        return wire[:last.header] + changed + wire[last.payload:]

    edit_sizes = last.fields.copy()
    edit_sizes[2] = TType.I32, len(last.body) + 1
    edits["late_page_size"] = (edit_header(edit_sizes), target,
                               page_error(target, last, f".pageSizes {len(last.body)+1} {len(last.body)}"))
    edit_encoding = last.fields.copy()
    edit_encoding[5] = TType.STRUCT, {**last.fields[5][1], 2: (TType.I32, 5)}
    edits["late_encoding"] = (edit_header(edit_encoding), target,
                              page_error(target, last, ".encoding 5 3 3"))

    extent, = struct.unpack_from("<I", present.body)
    for label, changed, cause in (
        ("late_definition_extent", len(present.body), ".section .truncatedDefinitions"),
        ("late_trailing_levels", extent + 1, ".hybrid .trailingBytes"),
    ):
        modified = wire[:present.payload] + struct.pack("<I", changed) + wire[present.payload+4:]
        edits[label] = (modified, target, page_error(target, present, cause))

    for label, uncompressed_shrink, compressed_shrink in (("chunk_size", 1, 0), ("late_payload_bounds", 1, 1)):
        footer = MIXED["metadata"](wire)
        datum = THRIFT["column_metadata"](footer, target.group, target.index)
        datum[6] = TType.I64, datum[6][1] - uncompressed_shrink
        datum[7] = TType.I64, datum[7][1] - compressed_shrink
        cause = (chunk_error(target, f".uncompressedSize {datum[6][1]} {datum[7][1]}")
                 if compressed_shrink == 0 else page_error(target, last, ".framing .payloadBounds"))
        edits[label] = (pack(wire, footer), target, cause)

    expected_rows = len(admitted["multipage"][1][1])
    for label, delta in (("row_deficit", 1), ("late_row_overrun", -1)):
        footer = MIXED["metadata"](wire)
        footer[3] = TType.I64, footer[3][1] + delta
        group = THRIFT["list_field"](footer, 4)[target.group]
        group[3] = TType.I64, expected_rows + delta
        for chunk in THRIFT["list_field"](group, 1):
            column = chunk[3][1]
            column[5] = TType.I64, column[5][1] + delta
        cause = (chunk_error(target, f".rowCount {expected_rows+1} {expected_rows}") if delta > 0 else
                 page_error(target, last, f".rowOverrun {len(last.slots)-1} {len(last.slots)}"))
        edits[label] = (pack(wire, footer), target, cause)

    v2 = controls["v2"]
    footer = MIXED["metadata"](v2)
    v2_start, v2_end = MIXED["column_extent"](THRIFT["column_metadata"](footer, 0, 0))
    v2_header, spec, _, _ = next(FRAMES(v2, v2_start, v2_end))
    assert spec[1][1] == 3
    v2_detail = spec[8][1]
    v2_fields = ", ".join(str(v2_detail[i][1]) for i in range(1, 7))
    compressed_v2 = str(v2_detail.get(7, (None, True))[1]).lower()
    assert compressed_v2 in {"true", "false"}
    v2_cause = f'.page ⟨0, 0, {path_term(observations["deep"][0].path)}⟩ ⟨0, {v2_header}, 0⟩ '
    v2_cause += f'(.pageKind (.dataV2 ⟨{v2_fields}, {compressed_v2}⟩))'

    first = target.pages[0]
    required = next(col for col in observations["required_path"] if (col.group, col.index) == (0, 1))
    cases = [
        ("v2", 0, 0, "{}", v2_cause),
        ("multipage", 1, 1, "{ maxRows := 0 }", chunk_error(target, ".rowLimit")),
        ("multipage", 1, 1, "{ maxChunkBytes := 0 }", chunk_error(target, ".chunkLimit")),
        ("multipage", 1, 1, "{ maxBodyBytes := 0 }", page_error(target, first, ".checksum .byteLimit")),
        ("multipage", 1, 1, "{ framing.maxPages := 1 }", page_error(target, target.pages[1], ".framing .pageLimit")),
        ("multipage", 1, 1, "{ levels := ⟨0, 16 * 1024 * 1024⟩ }", page_error(target, first, ".hybrid .valueLimit")),
        ("required_path", 0, 1, "{ levels := ⟨0, 16 * 1024 * 1024⟩ }", page_error(required, required.pages[0], ".countLimit")),
    ]
    cases.extend((label, col.group, col.index, "{}", cause)
                 for label, (_, col, cause) in edits.items())
    return {label: item[0] for label, item in edits.items()}, cases


def compare(admitted, controls):
    observations = {label: list(capture(wire, schema, groups, crc))
                    for label, (schema, groups, wire, crc) in admitted.items()}
    edits, cases = negative(admitted, controls, observations)
    code = [LEAN, "public def main (args : List String) : IO Unit := do",
            '  let [folder] := args | throw (IO.userError "expected fixture folder")']
    for label, (_, groups, _, _) in admitted.items():
        columns = observations[label]
        expected = lst(lst(lst(page_term(page, col.field.type.bit_width) for page in col.pages)
                           for col in columns if col.group == group)
                       for group in range(len(groups)))
        code.append(f'  verify (← load folder "{label}") {expected}')
        print(f"{label}: {len(columns)} chunks, {sum(len(col.pages) for col in columns)} pages")
    for label, group, column, limits, cause in cases:
        code.append(f'  refuse (← load folder "{label}") {group} {column} {limits} ({cause})')
    code.append(f'  IO.println "Checked native signed chunks and {len(cases)} typed refusals"')
    with tempfile.TemporaryDirectory() as directory:
        scratch = Path(directory)
        sources = {label: fixture[2] for label, fixture in admitted.items()} | controls | edits
        for label, data in sources.items():
            (scratch / f"{label}.parquet").write_bytes(data)
        driver = scratch / "Check.lean"
        driver.write_text("\n".join(code) + "\n", encoding="utf-8")
        subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                        "--run", str(driver), directory], cwd=ROOT, check=True)
    return edits


def main():
    pins = json.loads(MANIFEST.read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython" and platform.python_version() == pins["producer"]["cpython"]
    assert pa.__version__ == pins["producer"]["pyarrow"] and version("thrift") == pins["producer"]["thrift"]
    admitted, controls = fixtures()
    assert fingerprints({label: fixture[2] for label, fixture in admitted.items()} | controls) == pins["genuine_parquet"]
    assert fingerprints(compare(admitted, controls)) == pins["labeled_edits"]


if __name__ == "__main__":
    main()
