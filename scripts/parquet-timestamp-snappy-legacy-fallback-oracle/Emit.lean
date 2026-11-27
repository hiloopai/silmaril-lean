module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.LegacyV1.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Snappy.LegacyV1.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc

private abbrev convertLegacy := Leaf.Fallback.Snappy.LegacyV1.convert

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

private def readPrefix (directory : System.FilePath) : IO (List (Option Int)) := do
  let text ← IO.FS.readFile (directory / "prefix.txt")
  (text.splitOn "\n").mapM fun line =>
    if line == "null" then pure none
    else match line.toInt? with
      | some count => pure (some count)
      | none => throw (IO.userError s!"invalid independent count: {line}")

private def checkLate (label : String) (wire : Bytes) (earlierRows : List (Option Int))
    (cause : Leaf.Error) : IO Unit := do
  let bound ← require (openBound {} wire 1)
  let ⟨schema, trace⟩ ← require (Leaf.Fallback.Snappy.LegacyV1.readBound {} {} bound)
  if positive : 0 < schema.width then
    unless (batchesAt trace ⟨0, positive⟩).map Arrow.TimestampBatch.Writer.tickCounts == [earlierRows] do
      throw (IO.userError s!"{label}: lost the original group prefix")
  else throw (IO.userError "expected selected field")
  match trace.termination with
  | .readError actual =>
    unless actual == .groupFailure 1 cause do
      throw (IO.userError s!"{label}: unexpected source error {repr actual}")
  | _ => throw (IO.userError s!"{label}: expected indexed source error")
  expectError label (.source (.groupFailure 1 cause))
    (convertLegacy {} {} {ipc.batches := 0} wire 1)

private def checksum (frame offset declared computed : Nat) : Leaf.Error :=
  .dictionaryPage frame offset (.checksumFailure (.mismatch declared.toUInt32 computed.toUInt32))

public def main (args : List String) : IO Unit := do
  let folder :: evidence := args | throw (IO.userError "expected a fixture directory and Thrift observations")
  let [some plainFrame, some plainOffset, some plainDeclared, some plainComputed, some dictOffset,
       some dictDeclared, some dictComputed, some reentryFrame, some reentryOffset, some firstOffset] :=
    evidence.map String.toNat? | throw (IO.userError "invalid independent frame observations")
  let directory : System.FilePath := folder
  let wire ← input directory "fallback"
  let localOutput ← require (convertLegacy {} {} {} wire 1)
  let utcOutput ← require (convertLegacy {} {} {} wire 2)
  IO.FS.writeBinFile (directory / "local_ticks.arrows") localOutput.toByteArray
  IO.FS.writeBinFile (directory / "utc_ticks.arrows") utcOutput.toByteArray
  expectError "strict codec" (.source (.groupFailure 0 (.chunkCodec 1))) (convert {} {} wire 1)
  expectError "modern fallback" (.source (.groupFailure 0 .chunkEncoding))
    (Leaf.Fallback.Snappy.convert .modernOnly {} {} {} wire 1)
  expectError "legacy dictionary-only" (.source (.groupFailure 0 .chunkEncoding))
    (Leaf.Dictionary.Snappy.LegacyV1.convert {} {} {} wire 1)
  expectError "group row bound" (.source (.groupFailure 0 .rowLimit))
    (convertLegacy {} {leaf.maxRows := 383} {} wire 1)
  expectError "file row bound" (.rowLimit 767 768) (convertLegacy {} {maxTotalRows := 767} {} wire 1)

  let earlierRows ← readPrefix directory
  let plainBad ← input directory "bad_plain"
  checkLate "later PLAIN CRC" plainBad earlierRows (checksum plainFrame plainOffset plainDeclared plainComputed)
  let unselected ← require (convertLegacy {} {} {} plainBad 2)
  unless unselected.toList == utcOutput.toList do
    throw (IO.userError "a damaged unselected leaf affected the observed native stream")
  checkLate "later dictionary CRC" (← input directory "bad_dictionary") earlierRows
    (checksum 0 dictOffset dictDeclared dictComputed)
  checkLate "return to dictionary before body decoding" (← input directory "reentered") earlierRows
    (.dictionaryPage reentryFrame reentryOffset .dictionaryAfterFallback)
  checkLate "missing PLAIN suffix" (← input directory "no_fallback") earlierRows .dictionaryMissingFallback
  checkLate "missing dictionary prefix" (← input directory "starts_plain") earlierRows
    (.dictionaryPage 1 firstOffset (.encoding 0))
  IO.println "Ten typed refusal controls, five exact prefixes, and the unselected-leaf control passed"
