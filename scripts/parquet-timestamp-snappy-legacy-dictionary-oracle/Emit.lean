module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.LegacyV1.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.LegacyV1.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc

private abbrev Legacy := Leaf.Dictionary.Snappy.LegacyV1.convert

private def require {α ε : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def input (directory : System.FilePath) (name : String) : IO Bytes :=
  (IO.FS.readBinFile (directory / (name ++ ".parquet"))).map fun raw => ⟨raw⟩

private def expectError (label : String) (expected : Leaf.Events.ToIpc.Error)
    (result : Except Leaf.Events.ToIpc.Error KBytes) : IO Unit :=
  match result with
  | .error actual => unless actual == expected do
      throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: unexpected output")

private def readCounts (directory : System.FilePath) (index : Nat) : IO (List (Option Int)) := do
  let text ← IO.FS.readFile (directory / s!"prefix-{index}.txt")
  (text.splitOn "\n").mapM fun line =>
    if line == "null" then pure none
    else match line.toInt? with
      | some count => pure (some count)
      | none => throw (IO.userError s!"invalid independent count: {line}")

private def checkLate (label : String) (wire : Bytes) (expected : List (List (Option Int)))
    (cause : Leaf.Error) : IO Unit := do
  let bound ← require (openBound {} wire 1)
  let ⟨schema, trace⟩ ← require (Leaf.Dictionary.Snappy.LegacyV1.readBound {} {} bound)
  if one : 0 < schema.width then
    unless (batchesAt trace ⟨0, one⟩).map Arrow.TimestampBatch.Writer.tickCounts == expected do
      throw (IO.userError s!"{label}: lost the exact event prefix")
  else throw (IO.userError "expected one timestamp field")
  match trace.termination with
  | .readError actual =>
    unless actual == .groupFailure 2 cause do
      throw (IO.userError s!"{label}: unexpected late source error {repr actual}")
  | _ => throw (IO.userError s!"{label}: expected an indexed source error")
  expectError label (.source (.groupFailure 2 cause))
    (Legacy {} {} {ipc.batches := 0} wire 1)

private def checkAdmission (wire : Bytes) : IO Unit := do
  let bound ← require (openBound {} wire 1)
  let group ← require (Leaf.Dictionary.Snappy.LegacyV1.checkGroup {} {} bound 0)
  let dictOffset := group.dictionary.header.start
  let some first := group.data.head? | throw (IO.userError "expected first legacy data frame")
  expectError "strict codec" (.source (.groupFailure 0 (.chunkCodec 1))) (convert {} {} wire 1)
  expectError "existing Snappy dictionary policy" (.source (.groupFailure 0 .chunkEncoding))
    (Leaf.Dictionary.Snappy.convert .modernOnly {} {} {} wire 1)
  expectError "chunk cap" (.source (.groupFailure 0 .dictionaryChunkLimit))
    (Legacy {maxChunkBytes := group.chunk.span.stop - group.chunk.span.start - 1} {} {} wire 1)
  expectError "entry cap" (.source (.groupFailure 0 (.dictionaryPage 0 dictOffset .entryLimit)))
    (Legacy {maxEntries := 2} {} {} wire 1)
  expectError "expanded dictionary cap" (.source (.groupFailure 0
      (.dictionaryPage 0 dictOffset (.payload .outputLimit))))
    (Legacy {maxDictionaryBytes := group.dictionary.value.uncompressedSize - 1} {} {} wire 1)
  expectError "reference cap" (.source (.groupFailure 0
      (.dictionaryPage 1 first.frame.header.start (.references (.hybrid .valueLimit)))))
    (Legacy {indices := ⟨0, 16 * 1024 * 1024⟩} {} {} wire 1)

public def main (args : List String) : IO Unit := do
  let directory :: observations := args |
    throw (IO.userError "usage: Emit.lean DIRECTORY CRC_OFFSET DECLARED COMPUTED REFERENCE_OFFSET")
  let [some crcOffset, some declared, some computed, some refOffset] := observations.map String.toNat? |
    throw (IO.userError "invalid independent frame observations")
  let directory : System.FilePath := directory
  for name in ["local_micros", "utc_nanos"] do
    let emitted ← require (Legacy {} {} {} (← input directory name) 1)
    IO.FS.writeBinFile (directory / (name ++ ".arrows")) emitted.toByteArray
  checkAdmission (← input directory "local_micros")
  let earlier ← [0, 1].mapM (readCounts directory)
  checkLate "late CRC" (← input directory "bad_crc") earlier
    (.dictionaryPage 1 crcOffset (.checksumFailure (.mismatch declared.toUInt32 computed.toUInt32)))
  checkLate "late checked lookup" (← input directory "bad_ref") earlier
    (.dictionaryPage 2 refOffset (.references (.outOfBounds 3)))
  checkLate "optional definition tag" (← input directory "bad_level_tag") earlier
    (.dictionaryPage 2 refOffset (.references (.page .unsupportedLevelEncoding)))
  IO.println "Nine typed refusal controls and three exact prefixes passed"
