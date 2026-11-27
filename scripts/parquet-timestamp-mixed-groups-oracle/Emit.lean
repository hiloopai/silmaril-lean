module

import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
open Leaf.MixedGroups (Plan DictionaryLayout)

private def input (directory : System.FilePath) (name : String) : IO Bytes :=
  (IO.FS.readBinFile (directory / (name ++ ".parquet"))).map fun raw => ⟨raw⟩

private def require {α ε : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def expectError (label : String) (expected : Leaf.Events.ToIpc.Error)
    (result : Except Leaf.Events.ToIpc.Error KBytes) : IO Unit := do
  match result with
  | .error actual => unless actual == expected do
      throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: unexpected output")

private abbrev convert := Leaf.MixedGroups.convert .modernOnly

private def planMatches (plan : Plan) (codec : Int) (layout : Option DictionaryLayout) : Bool :=
  match plan, layout with
  | .plain chunk pages, none =>
    chunk.column.metadata.codec == codec && pages.map (·.params.encoding) == [0]
  | .dictionary selected actual chunk, some expected =>
    selected.id == codec && actual == expected && chunk.data.map (·.params.encoding) ==
      if expected == .references then [8] else [8, 0, 0]
  | _, _ => false

private def checkPlans (wire : Bytes) : IO Unit := do
  let bound ← require (Leaf.openLeaf {} wire 2)
  let expected : List (Int × Option DictionaryLayout) :=
    [(0, none), (1, some .references), (0, some .references), (1, none),
     (0, some .fallback), (1, some .fallback)]
  unless bound.snapshot.groupCount == expected.length do
    throw (IO.userError "unexpected group count")
  for ((codec, layout), index) in expected.zipIdx do
    let plan ← require (Leaf.MixedGroups.planGroup {} {} bound index)
    unless planMatches plan codec layout do throw (IO.userError s!"wrong original chunk classification at {index}")

private def checkLate (rows : List (List (Option Int))) (wire : Bytes) (index : Nat) (error : Leaf.Error) :
    IO Unit := do
  let expected : Leaf.Events.Error := .groupFailure index error
  let bound ← require (Leaf.openLeaf {} wire 2)
  let ⟨schema, trace⟩ ← require (Leaf.MixedGroups.readBound {} {} bound)
  if column : 0 < schema.width then
    let batches := Leaf.Events.ToIpc.batchesAt trace ⟨0, column⟩
    unless batches.map Arrow.TimestampBatch.Writer.tickCounts == rows.take index do
      throw (IO.userError s!"group {index} lost its exact earlier events")
  else throw (IO.userError "missing TIMESTAMP field")
  match trace.termination with
  | .readError actual =>
    unless actual == expected do throw (IO.userError s!"expected {repr expected}, got {repr actual}")
  | _ => throw (IO.userError "expected indexed read failure")
  expectError "source error precedes IPC emission" (.source expected)
    (convert {} {} {ipc.batches := 0} wire 2)

private def checkDefaults (wire : Bytes) : IO Unit := do
  expectError "default PLAIN codec" (.source (.groupFailure 1 (.chunkCodec 1)))
    (Leaf.Events.ToIpc.convert {} {} wire 2)
  expectError "Snappy PLAIN rejects dictionary chunk" (.source (.groupFailure 1 .chunkEncoding))
    (Leaf.Events.ToIpc.convert {leaf.allowSnappy := true} {} wire 2)
  expectError "dictionary-only profile" (.source (.groupFailure 0 .chunkEncoding))
    (Leaf.Dictionary.convert .modernOnly {} {} {} wire 2)
  expectError "uncompressed fallback profile" (.source (.groupFailure 0 .chunkEncoding))
    (Leaf.Fallback.convert .modernOnly {} {} {} wire 2)
  expectError "Snappy dictionary-only profile" (.source (.groupFailure 0 (.chunkCodec 0)))
    (Leaf.Dictionary.Snappy.convert .modernOnly {} {} {} wire 2)
  expectError "Snappy fallback profile" (.source (.groupFailure 0 (.chunkCodec 0)))
    (Leaf.Fallback.Snappy.convert .modernOnly {} {} {} wire 2)

private def parseRows (directory : System.FilePath) : IO (List (List (Option Int))) :=
  (List.range 6).mapM fun index => do
    let text ← IO.FS.readFile (directory / s!"rows-{index}.txt")
    let some rows := (text.splitOn "\n").mapM fun line =>
      if line == "null" then some none else line.toInt?.map some
      | throw (IO.userError "invalid slot golden")
    pure rows

public def main (args : List String) : IO Unit := do
  let folder :: rest := args | throw (IO.userError "expected directory and indexed error evidence")
  let some [transitionOffset, crcOffset, crc, actual] := rest.mapM String.toNat?
    | throw (IO.userError "invalid error evidence")
  let directory : System.FilePath := folder
  for name in ["utc", "local", "schema_only"] do
    let wire ← input directory name
    if name != "schema_only" then checkPlans wire
    let output ← require (convert {} {} {} wire 2)
    IO.FS.writeBinFile (directory / (name ++ ".arrows")) output.toByteArray
  let wire ← input directory "local"
  let rows ← parseRows directory
  checkDefaults wire
  checkLate rows (← input directory "unknown_codec") 2 (.chunkCodec 2)
  checkLate rows (← input directory "unknown_tag") 3 (.page 0 (.scalar (.unsupportedEncoding 5)))
  checkLate rows (← input directory "after_fallback") 4 (.dictionaryPage 3 transitionOffset .dictionaryAfterFallback)
  checkLate rows (← input directory "checksum_failure") 5
    (.dictionaryPage 3 crcOffset (.checksumFailure (.mismatch (UInt32.ofNat crc) (UInt32.ofNat actual))))
  expectError "zero-byte row group fails at snapshot" (.source (.openFailure (.snapshot (.invalidMetadata .pageInterval))))
    (convert {} {} {} (← input directory "page_less") 2)
  expectError "aggregate group cap" (.groupLimit 5 6)
    (convert {} {maxGroups := 5} {} wire 2)
  expectError "dictionary byte cap" (.source (.groupFailure 1 .dictionaryChunkLimit))
    (convert {maxChunkBytes := 1} {} {} wire 2)
  IO.println "Twelve original chunk classifications, nine admission and budget refusals, and four exact late-error prefixes passed"
