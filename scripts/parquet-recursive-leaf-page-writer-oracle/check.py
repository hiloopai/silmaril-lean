"""Check actual Lean signed V1 pages and test-only PyArrow file assemblies."""

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
PREDECESSOR = HERE.parent / "parquet-recursive-repeated-chunk-oracle"
CHUNK = runpy.run_path(str(PREDECESSOR / "check.py"))
THRIFT, MIXED, FRAMES, level_section, fingerprints = (
    CHUNK[key] for key in ("THRIFT", "MIXED", "FRAMES", "level_section", "fingerprints")
)
SAMPLES = {"nested": True, "mixed_required": False, "multipage_crc": True,
           "authored_continuation": True}

LEAN = """\
module

import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Defs

open Silmaril Silmaril.Formats
open Parquet.RecursiveSchema
open Parquet.RecursiveSchema.Repeated.Chunk (bindChunk ObservedPage)
open Parquet.RecursiveSchema.Repeated.Chunk.Writer

private def take {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"unexpected refusal: {repr cause}")

private def deny {α : Type} (wanted : Parquet.RecursiveSchema.Repeated.Chunk.Writer.Error)
    (result : Except Parquet.RecursiveSchema.Repeated.Chunk.Writer.Error α) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"accepted input expecting {repr wanted}")
  | .error actual =>
    unless actual = wanted do throw (IO.userError s!"expected {repr wanted}, got {repr actual}")

private def save (folder : System.FilePath) (label : String) (out : Output) : IO Unit :=
  IO.FS.writeBinFile (folder / (label ++ ".page")) out.wire.data

private def load (folder : System.FilePath) (label : String) : IO Bytes :=
  return ⟨← IO.FS.readBinFile (folder / (label ++ ".parquet"))⟩

private def atoms (page : ObservedPage) : List Repeated.Rows.Atom :=
  List.zipWith Repeated.Rows.Atom.mk page.decoded.levels page.decoded.words

private def emitFile (folder : System.FilePath) (label : String) (checksum : Bool) : IO Unit := do
  let opened ← take (Repeated.openFile {} (← load folder label))
  for group in List.range opened.snapshot.groupCount do
    let seen ← take (Repeated.Rows.readGroup {} opened.schema group)
    let depth := ({} : Parquet.Snapshot.Limits).maxSchemaDepth - 1
    let some projected := seen.rows.mapM (Repeated.Rows.Projection.row depth opened.schema.fields)
      | throw (IO.userError "logical row projection failed")
    for column in List.range opened.schema.leaves.size do
      let binding ← take (bindChunk opened.schema group column)
      let original ← take (Parquet.RecursiveSchema.Repeated.Chunk.read {} binding)
      let columnAtoms := projected.flatMap fun row => row[column]?.getD []
      unless columnAtoms == original.pages.flatMap atoms do
        throw (IO.userError "projected atoms differ from the original addressed page slots")
      for page in original.pages do
        let input : Input := ⟨binding.leaf, page.start.state,
          (columnAtoms.drop page.start.state.slot).take page.decoded.levels.length, checksum⟩
        let emitted ← take (emit {} input)
        unless emitted.after = page.decoded.after do throw (IO.userError "next state differs")
        save folder s!"{label}-{group}-{column}-{page.start.page}" emitted

private def controls (folder : System.FilePath) : IO Unit := do
  let opened ← take (Repeated.openFile {} (← load folder "authored_continuation"))
  let binding ← take (bindChunk opened.schema 0 0)
  let original ← take (Parquet.RecursiveSchema.Repeated.Chunk.read {} binding)
  let some page := original.pages[3]? | throw (IO.userError "expected cut inside a List")
  let input : Input := ⟨binding.leaf, page.start.state, atoms page, true⟩
  let some first := input.atoms.head? | throw (IO.userError "expected a continued signed word")
  let normal ← take (emit {} input)
  let exact : Repeated.Chunk.Limits := {
    maxSlots := normal.after.slot, maxRows := normal.after.rows,
    framing.maxPages := 1, framing.maxHeaderBytes := normal.page.headerBytes.length,
    maxBodyBytes := normal.page.body.length, maxChunkBytes := normal.wire.length,
    levels.values := input.atoms.length, levels.bytes := input.atoms.length * 2 }
  let tight ← take (emit exact input)
  unless tight.wire = normal.wire do throw (IO.userError "exact budgets changed the page")
  deny (.limit .slots) (emit { exact with maxSlots := exact.maxSlots - 1 } input)
  deny (.limit .rows) (emit { exact with maxRows := exact.maxRows - 1 } input)
  deny (.limit .pages) (emit { exact with framing.maxPages := 0 } input)
  deny (.limit .header) (emit { exact with framing.maxHeaderBytes := exact.framing.maxHeaderBytes - 1 } input)
  deny (.limit .body) (emit { exact with maxBodyBytes := exact.maxBodyBytes - 1 } input)
  deny (.limit .chunk) (emit { exact with maxChunkBytes := exact.maxChunkBytes - 1 } input)
  deny (.limit .levelBytes) (emit { exact with levels.bytes := exact.levels.bytes - 1 } input)
  deny (.limit .slots) (emit { exact with levels.values := exact.levels.values - 1 } input)
  deny (.continuationWithoutList 4) (emit {} { input with start.live := false })
  deny (.classification 4) (emit {} { input with
    atoms := [{ first with levels.classified.position := .rowStart }] })
  deny (.wordPresence 4) (emit {} { input with atoms := [{ first with word := none }] })
  deny (.signedType 4) (emit {} { input with atoms := [{ first with word := some (.int64 22) }] })
  let location := input.leaf.site.location
  deny (.level (.repetition location 4 2 1)) (emit {} { input with
    atoms := [{ first with levels.repetition := 2 }] })
  deny (.level (.definition location 4 4 3)) (emit {} { input with
    atoms := [{ first with levels.definition := 4 }] })
  let changed := Bytes.ofList (normal.page.body.toList.modify 0 (· ^^^ 1))
  let corrupt := { normal with page.body := changed }
  let some crc := normal.page.header.crc | throw (IO.userError "expected a checksum")
  let observed := Compression.Checksum.crc32.digest changed.toList
  deny (.decode (.checksum (.mismatch crc observed))) (certify {} input corrupt)
  let trailing := { normal with page.body := normal.page.body.append (Bytes.ofList [0]) }
  deny .frameMismatch (certify {} input trailing)
  let empty ← take (emit exact { input with atoms := [] })
  unless empty.after = input.start do throw (IO.userError "empty page advanced the cursor state")
  save folder "empty-repeated" empty
  let nested ← take (Repeated.openFile {} (← load folder "nested"))
  let required ← take (bindChunk nested.schema 0 3)
  let emptyRequired ← take (emit {} ⟨required.leaf, {}, [], false⟩)
  save folder "empty-required" emptyRequired

public def main (args : List String) : IO Unit := do
  let [dir] := args | throw (IO.userError "expected fixture directory")
  let folder := System.FilePath.mk dir
"""


def inspect_page(wire, width, max_rep, max_def, expected, checksum):
    [(start, header, payload, body)] = list(FRAMES(wire, 0, len(wire)))
    assert start == 0 and payload + len(body) == len(wire)
    assert set(header) == ({1, 2, 3, 4, 5} if checksum else {1, 2, 3, 5})
    assert [header[i][1] for i in (1, 2, 3)] == [0, len(body), len(body)]
    if checksum:
        assert header[4][1] & 0xffffffff == zlib.crc32(body)
    assert {key: item[1] for key, item in header[5][1].items()} == {
        1: len(expected), 2: 0, 3: 3, 4: 3,
    }
    reps, tail = level_section(body, max_rep, len(expected))
    defs, tail = level_section(tail, max_def, len(expected))
    words = iter(word for word, in struct.iter_unpack("<i" if width == 32 else "<q", tail))
    assert [(rep, level, next(words) if level == max_def else None)
            for rep, level in zip(reps, defs, strict=True)] == expected
    assert next(words, None) is None


def wrap_pages(source, chunks):
    """Test-only splice using the source schema and row-group metadata."""
    footer = MIXED["metadata"](source)
    carrier = bytearray(b"PAR1")
    for group, metadata in enumerate(THRIFT["list_field"](footer, 4)):
        start = len(carrier)
        for column, chunk in enumerate(THRIFT["list_field"](metadata, 1)):
            data = chunks[group, column]
            assert not (set(chunk) & {1, 4, 5, 6, 7})
            leaf = chunk[3][1]
            assert not (set(leaf) & {10, 11, 14, 15})
            chunk[2] = leaf[9] = (TType.I64, len(carrier))
            leaf[6] = leaf[7] = (TType.I64, len(data))
            carrier.extend(data)
        metadata[2] = TType.I64, len(carrier) - start
        if 5 in metadata:
            metadata[5] = TType.I64, start
        if 6 in metadata:
            metadata[6] = metadata[2]
    encoded = THRIFT["encode"](footer)
    return bytes(carrier) + encoded + struct.pack("<I", len(encoded)) + b"PAR1"


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    upstream = json.loads((HERE / pins["source_pins"]).read_text(encoding="utf-8"))
    producer = json.loads((PREDECESSOR / upstream["producer_pins"]).read_text(encoding="utf-8"))
    assert platform.python_implementation() == "CPython"
    assert platform.python_version() == producer["producer"]["cpython"]
    assert pa.__version__ == producer["producer"]["pyarrow"]
    assert version("thrift") == producer["producer"]["thrift"]

    with tempfile.TemporaryDirectory() as directory:
        scratch = Path(directory)
        genuine, edits, samples = CHUNK["fixtures"](scratch)
        sources = genuine | edits
        upstream_pins = upstream["genuine_parquet"] | upstream["labeled_edits"]
        assert fingerprints({name: sources[name] for name in SAMPLES}) == {
            name: upstream_pins[name] for name in SAMPLES
        }
        for name in SAMPLES:
            (scratch / f"{name}.parquet").write_bytes(sources[name])
        driver = scratch / "Check.lean"
        calls = [f'  emitFile folder "{name}" {str(crc).lower()}' for name, crc in SAMPLES.items()]
        driver.write_text(LEAN + "\n".join([*calls, "  controls folder", ""]), encoding="utf-8")
        subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                        "--run", str(driver), directory], cwd=ROOT, check=True)

        carriers, page_series = {}, {}
        for name, checksum in SAMPLES.items():
            chunks = {}
            original = pq.ParquetFile(pa.BufferReader(sources[name]))
            columns = list(CHUNK["capture"](sources[name], *samples[name]))
            for column in columns:
                pages = []
                maximum = original.schema.column(column.index)
                for page in column.pages:
                    label = f"{name}-{column.group}-{column.index}-{page.index}"
                    wire = (scratch / f"{label}.page").read_bytes()
                    inspect_page(wire, column.width, maximum.max_repetition_level,
                                 maximum.max_definition_level, page.events, checksum)
                    pages.append(wire)
                chunks[column.group, column.index] = b"".join(pages)
            wrapped = wrap_pages(sources[name], chunks)
            actual = pq.ParquetFile(pa.BufferReader(wrapped), page_checksum_verification=True)
            assert actual.schema_arrow == original.schema_arrow
            assert actual.num_row_groups == original.num_row_groups
            for index in range(actual.num_row_groups):
                assert actual.read_row_group(index).to_pylist() == original.read_row_group(index).to_pylist()
            carriers[name] = wrapped
            page_series[name] = b"".join(chunks.values())
            print(f"{name}: {len(columns)} chunks, {sum(len(column.pages) for column in columns)} Lean pages")
        for name, maximum, checksum in [("empty-repeated", (1, 3), True),
                                        ("empty-required", (0, 0), False)]:
            wire = (scratch / f"{name}.page").read_bytes()
            inspect_page(wire, 32 if checksum else 64, *maximum, [], checksum)
            page_series[name] = wire
        assert fingerprints(page_series) == pins["lean_page_series"]
        assert fingerprints(carriers) == pins["test_only_containers"]
    print("Verified native page words, optional CRC, exact typed refusals and PyArrow row-group readback")


if __name__ == "__main__":
    main()
