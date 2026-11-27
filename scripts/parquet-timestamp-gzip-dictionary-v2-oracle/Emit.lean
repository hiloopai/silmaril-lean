module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.V2.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Gzip.V2.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V1.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V1.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc

private abbrev convertV2 := Leaf.Dictionary.Gzip.V2.convert

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
  let text ← IO.FS.readFile (directory / s!"rows-{index}.txt")
  (text.splitOn "\n").mapM fun line =>
    if line == "null" then pure none
    else match line.toInt? with
      | some count => pure (some count)
      | none => throw (IO.userError s!"invalid independent count: {line}")

private def checkLate (label : String) (wire : Bytes) (earlierRows : List (List (Option Int)))
    (index : Nat) (cause : Leaf.Error) : IO Unit := do
  let bound ← require (openBound {} wire 2)
  let ⟨schema, trace⟩ ← require (Leaf.Dictionary.Gzip.V2.readBound {} {} bound)
  if positive : 0 < schema.width then
    unless (batchesAt trace ⟨0, positive⟩).map Arrow.TimestampBatch.Writer.tickCounts == earlierRows.take index do
      throw (IO.userError s!"{label}: lost a completed original batch")
  else throw (IO.userError "expected selected TIMESTAMP field")
  match trace.termination with
  | .readError actual =>
    unless actual == .groupFailure index cause do
      throw (IO.userError s!"{label}: unexpected source error {repr actual}")
  | _ => throw (IO.userError s!"{label}: expected indexed source error")
  expectError label (.source (.groupFailure index cause)) (convertV2 {} {} {ipc.batches := 0} wire 2)

private def checkCaps (wire : Bytes) (firstData : Nat) : IO Unit := do
  let inputLimits : Leaf.Events.ToIpc.Limits := {}
  let bound ← require (openBound inputLimits wire 2)
  let group ← require (Leaf.Dictionary.Gzip.V2.checkGroup {} inputLimits.leaf bound 0)
  let dictionary := group.dictionary
  let atDictionary := fun cause => Leaf.Events.ToIpc.Error.source
    (.groupFailure 0 (.dictionaryPage 0 dictionary.header.start cause))
  expectError "member controller cap" (atDictionary (.payload .gzipIncomplete))
    (convertV2 {gzipCalls := 0} inputLimits {} wire 2)
  expectError "dictionary stored cap" (atDictionary (.checksumFailure .byteLimit))
    (convertV2 {} {inputLimits with leaf.page.compressedBytes := dictionary.value.compressedSize - 1} {} wire 2)
  expectError "raw definition cap" (.source (.groupFailure 0 (.dictionaryPage 1 firstData
      (.references (.page (.levels .definitionByteLimit))))))
    (convertV2 {} {inputLimits with leaf.page.levels.bytes := 0} {} wire 2)
  expectError "total row cap" (.rowLimit 365 366)
    (convertV2 {} {inputLimits with maxTotalRows := 365} {} wire 2)

public def main (args : List String) : IO Unit := do
  let folder :: evidence := args | throw (IO.userError "expected fixture directory and frame observations")
  let [some outerOffset, some declared, some computed, some dictionaryOffset, some rawOffset, some firstData,
       some v1Offset, some plainOffset] := evidence.map String.toNat? |
    throw (IO.userError "invalid independent frame observations")
  let directory : System.FilePath := folder
  for name in ["utc_nanos", "local_micros"] do
    let output ← require (convertV2 {} {} {} (← input directory name) 2)
    IO.FS.writeBinFile (directory / (name ++ ".arrows")) output.toByteArray

  let good ← input directory "utc_nanos"
  expectError "strict default" (.source (.groupFailure 0 (.chunkCodec 2))) (convert {} {} good 2)
  expectError "wrong codec" (.source (.groupFailure 0 (.chunkCodec 1)))
    (convertV2 {} {} {} (← input directory "snappy") 2)
  let v1OnlyCause : Leaf.Events.ToIpc.Error :=
    .source (.groupFailure 0 (.dictionaryPage 1 firstData (.parameters .unsupportedPage)))
  expectError "V1 dictionary predecessor stays strict" v1OnlyCause
    (Leaf.Dictionary.Gzip.convert {} {} {} good 2)
  expectError "V1 dispatch predecessor stays strict" v1OnlyCause
    (Leaf.Gzip.Dispatch.V1.convert {} {} {} good 2)
  expectError "V1 data refused" (.source (.groupFailure 0 (.dictionaryPage 1 v1Offset (.parameters .unsupportedPage))))
    (convertV2 {} {} {} (← input directory "v1") 2)
  expectError "V2 fallback refused" (.source (.groupFailure 0 (.dictionaryPage 2 plainOffset (.encoding 0))))
    (convertV2 {} {} {} (← input directory "v2_fallback") 2)
  checkCaps good firstData

  let earlierRows ← [0, 1].mapM (readCounts directory)
  checkLate "raw levels in outer CRC" (← input directory "mutated_raw_level_crc") earlierRows 2
    (.dictionaryPage 1 outerOffset (.checksumFailure (.mismatch declared.toUInt32 computed.toUInt32)))
  checkLate "GZIP suffix trailer after outer CRC passes" (← input directory "mutated_member") earlierRows 2
    (.dictionaryPage 1 outerOffset (.references (.page (.payload (.malformed .gzip)))))
  checkLate "GZIP dictionary trailer" (← input directory "mutated_dictionary") earlierRows 2
    (.dictionaryPage 0 dictionaryOffset (.payload (.malformed .gzip)))
  let rawCause : Leaf.Error := .dictionaryPage 1 rawOffset (.references (.hybrid .invalidWidth))
  checkLate "raw references use their own decoder" (← input directory "mutated_raw_references") earlierRows 1 rawCause
  checkLate "earliest source group" (← input directory "mutated_two_groups") earlierRows 1 rawCause
  IO.println "Fifteen typed refusals and five exact earlier-group prefixes passed"
