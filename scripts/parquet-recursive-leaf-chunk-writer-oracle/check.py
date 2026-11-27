"""Check native recursive signed chunks and test-only file assemblies."""

from importlib.metadata import version
import json
from pathlib import Path
import platform
import runpy
import subprocess
import tempfile

import pyarrow as pa
import pyarrow.parquet as pq


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SCRIPTS = HERE.parent
PAGE = runpy.run_path(str(SCRIPTS / "parquet-recursive-leaf-page-writer-oracle/check.py"))
ROWS = runpy.run_path(str(SCRIPTS / "parquet-recursive-repeated-rows-oracle/check.py"))
CHUNK = PAGE["CHUNK"]
FRAMES, fingerprints, inspect_page, wrap_pages = (
    PAGE[key] for key in ("FRAMES", "fingerprints", "inspect_page", "wrap_pages")
)
CONTINUATION = "authored_continuation"
SAMPLES = {"mixed_required": False, "multipage_crc": True, CONTINUATION: True,
           "explicit_empty": True}


LEAN = """\
module

import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi.Defs
meta import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Defs

open Silmaril Silmaril.Formats
open Parquet.RecursiveSchema
open Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi

private def take {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"unexpected refusal: {repr cause}")

private def deny {ε α : Type} [DecidableEq ε] [Repr ε] (wanted : ε) (result : Except ε α) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"accepted input expecting {repr wanted}")
  | .error actual =>
    unless actual = wanted do throw (IO.userError s!"expected {repr wanted}, got {repr actual}")

private def load (folder : System.FilePath) (label : String) : IO Bytes :=
  return ⟨← IO.FS.readBinFile (folder / (label ++ ".parquet"))⟩

private def atoms (page : Repeated.Chunk.ObservedPage) : List Repeated.Rows.Atom :=
  List.zipWith Repeated.Rows.Atom.mk page.decoded.levels page.decoded.words

private def state (value : Repeated.Chunk.State) : String :=
  s!"{value.slot} {value.rows} {if value.live then 1 else 0}"

private def save (folder : System.FilePath) (label : String) (out : Output) : IO Unit := do
  IO.FS.writeBinFile (folder / (label ++ ".chunk")) out.wire.data
  let pages := out.observation.pages.map fun page =>
    let frame := page.frame
    s!"{page.start.page} {frame.header.start} {frame.header.stop} " ++
      s!"{frame.payload.start} {frame.payload.stop} {state page.start.state} {state page.decoded.after}"
  let metadata := s!"{out.numRows} {out.numValues} {out.dataPageOffset} " ++
    s!"{out.totalCompressedSize} {out.totalUncompressedSize}"
  IO.FS.writeFile (folder / (label ++ ".index")) (String.intercalate "\n" (metadata :: pages))

private def emitFile (folder : System.FilePath) (label : String) (checksum : Bool) : IO Unit := do
  let opened ← take (Repeated.openFile {} (← load folder label))
  for group in List.range opened.snapshot.groupCount do
    for column in List.range opened.schema.leaves.size do
      let binding ← take (Repeated.Chunk.bindChunk opened.schema group column)
      let source ← take (Repeated.Chunk.read {} binding)
      let input : Input := ⟨binding.leaf, binding.rowGroup.numRows.toNat,
        source.pages.map atoms, checksum, group, column⟩
      let written ← take (emit {} input)
      unless written.observation.pages.map atoms = input.pages do
        throw (IO.userError "emitted partitions differ")
      save folder s!"{label}-{group}-{column}" written

private def controls (folder : System.FilePath) : IO Unit := do
  let opened ← take (Repeated.openFile {} (← load folder "authored_continuation"))
  let binding ← take (Repeated.Chunk.bindChunk opened.schema 0 0)
  let source ← take (Repeated.Chunk.read {} binding)
  let [nullList, emptyList, prefixPage, lastPage] := source.pages.map atoms
    | throw (IO.userError "expected four authored pages")
  let input : Input := ⟨binding.leaf, 3, [nullList, emptyList, prefixPage, lastPage], true, 0, 0⟩
  let normal ← take (emit {} input)
  let exact : Repeated.Chunk.Limits := {
    maxSlots := 6, maxRows := 3, framing.maxPages := 4, maxChunkBytes := normal.wire.length }
  let bounded ← take (emit exact input)
  unless bounded.wire = normal.wire do throw (IO.userError "exact caps changed the chunk")
  deny (.pageLimit 4 3) (emit { exact with framing.maxPages := 3 } input)
  deny (.slotLimit 6 5) (emit { exact with maxSlots := 5 } input)
  deny (.rowLimit 3 2) (emit { exact with maxRows := 2 } input)
  deny (.page 3 (.limit .chunk)) (emit { exact with maxChunkBytes := exact.maxChunkBytes - 1 } input)
  deny .partition (emit {} { input with pages := [] })
  deny .partition (emit {} { input with rows := 0, pages := [] })
  deny .partition (emit {} { input with rows := 0, pages := [[], []] })
  deny .partition (emit {} { input with rows := 0, pages := [nullList] })
  deny (.page 0 (.continuationWithoutList 0)) (emit {} { input with pages := [lastPage] })
  deny (.page 1 (.continuationWithoutList 1)) (emit {} { input with pages := [emptyList, lastPage] })
  let rejected := carrier input normal.wire
  let endSpan := rejected.span
  let address := rejected.address
  deny (.readback (.chunk address endSpan (.rowCount 4 3))) (emit {} { input with rows := 4 })
  let some original ← pure normal.observation.pages[2]? | throw (IO.userError "expected third page")
  deny (.readback (.page address original.start (.rowOverrun 2 2)))
    (emit {} { input with rows := 2 })
  deny .partition (emit {} { input with pages := [nullList, emptyList, prefixPage, [], lastPage] })
  let first :: rest := lastPage | throw (IO.userError "expected a continued value")
  deny (.page 3 (.signedType 4)) (emit {} { input with
    pages := [nullList, emptyList, prefixPage, { first with word := some (.int64 22) } :: rest] })
  let zero ← take (emit {
    maxRows := 0, maxSlots := 0, framing.maxPages := 1, levels.values := 0, levels.bytes := 0 } { input with rows := 0, pages := [[]] })
  unless zero.numRows = 0 ∧ zero.numValues = 0 ∧ zero.frames.length = 1 ∧ zero.wire.length > 0 do
    throw (IO.userError "zero group lacks one real data page")

private def reread (folder : System.FilePath) (original label : String) : IO Unit := do
  let before ← take (Repeated.openFile {} (← load folder original))
  let after ← take (Repeated.openFile {} (← load folder label))
  let originalRows ← take (Repeated.Rows.readAll {} before.schema)
  let checkedRows ← take (Repeated.Rows.readAll {} after.schema)
  unless before.schema.arrow == after.schema.arrow && originalRows == checkedRows do
    throw (IO.userError "rebound checked file has different declarations or groups")

public def main (args : List String) : IO Unit := do
  let [dir, mode] := args | throw (IO.userError "expected fixture directory and mode")
  let folder := System.FilePath.mk dir
"""


def run_lean(driver, scratch, mode):
    subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
                    "--run", str(driver), str(scratch), mode], cwd=ROOT, check=True)


def check_chunk(path, column, maximum, checksum):
    wire = path.read_bytes()
    expected = [(page.before, page.after, page.events) for page in column.pages]
    index = [[int(word) for word in line.split()]
             for line in path.with_suffix(".index").read_text().splitlines()]
    assert index[0] == [column.rows, column.slots, 0, len(wire), len(wire)]
    frames = list(FRAMES(wire, 0, len(wire)))
    assert len(frames) == len(expected) == len(index) - 1
    for ordinal, ((start, _, payload, body), (before, after, events), observed) in enumerate(
            zip(frames, expected, index[1:], strict=True)):
        stop = payload + len(body)
        assert observed == [ordinal, start, payload, payload, stop, *before, *after]
        inspect_page(wire[start:stop], column.width, maximum.max_repetition_level,
                     maximum.max_definition_level, events, checksum)
    return wire, len(frames)


def main():
    pins = json.loads((HERE / "fixtures.json").read_text(encoding="utf-8"))
    parent = PAGE["PREDECESSOR"]
    upstream, rows_pins = (json.loads((HERE / path).read_text(encoding="utf-8"))
                           for path in pins["source_pins"])
    producer = json.loads((parent / upstream["producer_pins"]).read_text(encoding="utf-8"))["producer"]
    assert platform.python_implementation() == "CPython"
    assert platform.python_version() == producer["cpython"]
    assert pa.__version__ == producer["pyarrow"] and version("thrift") == producer["thrift"]

    with tempfile.TemporaryDirectory() as directory:
        scratch = Path(directory)
        genuine, edits, samples = CHUNK["fixtures"](scratch)
        sources = genuine | edits
        nested_schema, nested_rows, _ = samples["nested"]
        sources["explicit_empty"] = ROWS["explicit_empty"](sources["nested"], nested_schema, nested_rows)
        samples["explicit_empty"] = nested_schema, nested_rows, False
        source_pins = upstream["genuine_parquet"] | upstream["labeled_edits"] | rows_pins["labeled_edits"]
        assert fingerprints({name: sources[name] for name in SAMPLES}) == {
            name: source_pins[name] for name in SAMPLES
        }
        for name in SAMPLES:
            (scratch / f"{name}.parquet").write_bytes(sources[name])

        driver = scratch / "Check.lean"
        code = [LEAN, '  if mode = "emit" then']
        for name, checksum in SAMPLES.items():
            code.append(f'    emitFile folder "{name}" {str(checksum).lower()}')
        code.extend(['    controls folder', '  else'])
        for name in SAMPLES:
            code.append(f'    reread folder "{name}" "test-only-{name}"')
        driver.write_text("\n".join(code) + "\n", encoding="utf-8")
        run_lean(driver, scratch, "emit")

        carriers, chunk_files = {}, {}
        for name, checksum in SAMPLES.items():
            original = pq.ParquetFile(pa.BufferReader(sources[name]))
            columns = list(CHUNK["capture"](sources[name], *samples[name]))
            chunks, frame_count = {}, 0
            for column in columns:
                label = f"{name}-{column.group}-{column.index}"
                maximum = original.schema.column(column.index)
                wire, count = check_chunk(scratch / f"{label}.chunk", column, maximum, checksum)
                frame_count += count
                chunks[column.group, column.index] = wire
            wrapped = wrap_pages(sources[name], chunks)
            emitted = pq.ParquetFile(pa.BufferReader(wrapped), page_checksum_verification=True)
            assert emitted.schema_arrow == original.schema_arrow
            assert emitted.num_row_groups == original.num_row_groups
            row_counts = []
            for group in range(emitted.num_row_groups):
                expected = original.read_row_group(group).to_pylist()
                assert emitted.read_row_group(group).to_pylist() == expected
                row_counts.append(len(expected))
            assert name != "explicit_empty" or row_counts == [3, 0, 2]
            chunk_files[name] = b"".join(chunks.values())
            carriers[name] = wrapped
            (scratch / f"test-only-{name}.parquet").write_bytes(wrapped)
            print(f"{name}: {len(chunks)} Lean chunks, {frame_count} frames, row groups {row_counts}")
        run_lean(driver, scratch, "rebind")
        assert fingerprints(chunk_files) == pins["lean_chunk_series"]
        assert fingerprints(carriers) == pins["test_only_containers"]
    print("Checked exact chunk frames, fourteen typed refusals and strict file readback in test-only carriers")


if __name__ == "__main__":
    main()
