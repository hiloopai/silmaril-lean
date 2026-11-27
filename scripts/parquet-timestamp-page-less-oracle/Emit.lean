module

import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups.PageLess.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups.PageLess.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
private abbrev convert := Leaf.MixedGroups.PageLess.convert

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

private def parseRows (directory : System.FilePath) : IO (List (List (Option Int))) :=
  (List.range 6).mapM fun index => do
    let text ← IO.FS.readFile (directory / s!"rows-{index}.txt")
    if text.isEmpty then return []
    let some rows := (text.splitOn "\n").mapM fun line =>
      if line == "null" then some none else line.toInt?.map some
      | throw (IO.userError "invalid slot golden")
    pure rows

private def checkGroups (wire : Bytes) (expected : List Bool) : IO Unit := do
  let bound ← require (Leaf.MixedGroups.PageLess.openLeaf .modernOnly {} wire 2)
  unless bound.snapshot.groupCount == expected.length do
    throw (IO.userError "snapshot lost an original group")
  for (empty, index) in expected.zipIdx do
    let some group := bound.snapshot.groupAt index | throw (IO.userError s!"missing group {index}")
    unless bound.snapshot.admitsPageLessTimestamp group == empty do
      throw (IO.userError s!"incorrect no-frame predicate at {index}")
    let slots ← require (Leaf.MixedGroups.PageLess.readGroup {} {} bound index)
    unless slots.isEmpty == empty do throw (IO.userError s!"unexpected slots at {index}")
  match Leaf.MixedGroups.PageLess.readGroup {} {} bound expected.length with
  | .error (.groupIndex index) =>
    unless index == expected.length do throw (IO.userError "incorrect missing group ordinal")
  | _ => throw (IO.userError "missing group returned data")

private def checkLate (directory : System.FilePath) (offset crc actual : Nat) : IO Unit := do
  let rows ← parseRows directory
  let source ← input directory "late_crc"
  let bound ← require (Leaf.MixedGroups.PageLess.openLeaf .modernOnly {} source 2)
  let ⟨schema, trace⟩ ← require (Leaf.MixedGroups.PageLess.readBound {} {} bound)
  if column : 0 < schema.width then
    let batches := Leaf.Events.ToIpc.batchesAt trace ⟨0, column⟩
    unless batches.map Arrow.TimestampBatch.Writer.tickCounts == rows do
      throw (IO.userError "late failure lost the original complete prefix")
  else throw (IO.userError "missing TIMESTAMP field")
  let error : Leaf.Events.Error := .groupFailure 6
    (.dictionaryPage 3 offset (.checksumFailure (.mismatch (UInt32.ofNat crc) (UInt32.ofNat actual))))
  match trace.termination with
  | .readError actual => unless actual == error do throw (IO.userError s!"unexpected {repr actual}")
  | _ => throw (IO.userError "expected late Snappy CRC failure")
  expectError "source failure precedes IPC admission" (.source error)
    (convert .modernOnly {} {} {ipc.batches := 0} source 2)

public def main (args : List String) : IO Unit := do
  let folder :: rest := args | throw (IO.userError "expected directory and CRC evidence")
  let some [offset, crc, actual] := rest.mapM String.toNat? | throw (IO.userError "invalid CRC evidence")
  let directory : System.FilePath := folder
  let cases : List (String × List Bool) :=
    [("utc", [false, true, true, false]), ("local", [true, false, true, false]),
     ("all_empty", [true, true]), ("schema_only", []),
     ("assembled", [false, true, false, false, false, false, false])]
  for (name, empty) in cases do
    let wire ← input directory name
    checkGroups wire empty
    let output ← require (convert .modernOnly {} {} {} wire 2)
    IO.FS.writeBinFile (directory / (name ++ ".arrows")) output.toByteArray

  let strict : Leaf.Events.ToIpc.Error := .source (.openFailure (.snapshot (.invalidMetadata .pageInterval)))
  let noFrameError := fun cause : Parquet.Footer.PageLessTimestamp.Error =>
    Leaf.Events.ToIpc.Error.source (.openFailure (.pageLessSnapshot cause))
  let localWire ← input directory "local"
  expectError "strict mixed policy" strict (Leaf.MixedGroups.convert .modernOnly {} {} {} localWire 2)
  expectError "strict PLAIN policy" strict (Leaf.Events.ToIpc.convert {} {} localWire 2)
  for name in ["positive_missing", "nonzero_values", "empty_dictionary_frame"] do
    expectError name (noFrameError (.validation .pageInterval))
      (convert .modernOnly {} {} {} (← input directory name) 2)
  expectError "empty path" (noFrameError (.emptyColumns 0))
    (convert .modernOnly {} {} {} (← input directory "wrong_empty_path") 2)
  expectError "raw encoding stats" (noFrameError (.raw (.emptyMetadata 0)))
    (convert .modernOnly {} {} {} (← input directory "nonempty_stats") 2)
  expectError "unclaimed byte" (noFrameError .dataExtent)
    (convert .modernOnly {} {} {} (← input directory "unclaimed_byte") 2)
  expectError "group budget includes page-less ordinals" (.groupLimit 3 4)
    (convert .modernOnly {} {maxGroups := 3} {} localWire 2)
  checkLate directory offset crc actual
  IO.println "Five exact group-shape cases, nine typed refusals, and the original late CRC prefix passed"
