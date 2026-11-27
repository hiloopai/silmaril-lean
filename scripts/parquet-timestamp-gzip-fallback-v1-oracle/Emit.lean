module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc

private abbrev convertFallback := Leaf.Fallback.Gzip.convert

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

private def readCounts (directory : System.FilePath) : IO (List (Option Int)) := do
  let text ← IO.FS.readFile (directory / "expected.txt")
  (text.splitOn "\n").mapM fun line =>
    if line == "null" then pure none
    else match line.toInt? with
      | some count => pure (some count)
      | none => throw (IO.userError s!"invalid independent count: {line}")

private def checkLate (label : String) (wire : Bytes) (earlierRows : List (Option Int))
    (cause : Leaf.Error) : IO Unit := do
  let bound ← require (openBound {} wire 2)
  let ⟨schema, trace⟩ ← require (Leaf.Fallback.Gzip.readBound {} {} bound)
  if positive : 0 < schema.width then
    unless (batchesAt trace ⟨0, positive⟩).map Arrow.TimestampBatch.Writer.tickCounts == [earlierRows] do
      throw (IO.userError s!"{label}: lost the original completed batch")
  else throw (IO.userError "expected selected TIMESTAMP field")
  match trace.termination with
  | .readError actual =>
    unless actual == .groupFailure 1 cause do
      throw (IO.userError s!"{label}: unexpected source error {repr actual}")
  | _ => throw (IO.userError s!"{label}: expected indexed source error")
  expectError label (.source (.groupFailure 1 cause))
    (convertFallback {} {} {ipc.batches := 0} wire 2)

public def main (args : List String) : IO Unit := do
  let folder :: evidence := args | throw (IO.userError "expected a fixture directory and frame observations")
  let [some crcOffset, some declared, some computed, some dictionaryOffset, some referenceOffset,
       some lastPlainOffset, some firstGroupPlainOffset, some firstGroupDictionaryOffset, some v2Offset] :=
    evidence.map String.toNat? | throw (IO.userError "invalid independent frame observations")
  let directory : System.FilePath := folder
  for name in ["utc_nanos", "local_micros", "local_millis_raw_crc_absent"] do
    let output ← require (convertFallback {} {} {} (← input directory name) 2)
    IO.FS.writeBinFile (directory / (name ++ ".arrows")) output.toByteArray
  let good ← input directory "utc_nanos"
  expectError "strict default" (.source (.groupFailure 0 (.chunkCodec 2))) (convert {} {} good 2)
  expectError "Snappy fallback default" (.source (.groupFailure 0 (.chunkCodec 2)))
    (Leaf.Fallback.Snappy.convert .modernOnly {} {} {} good 2)
  expectError "GZIP dictionary-only default"
    (.source (.groupFailure 0 (.dictionaryPage 2 firstGroupPlainOffset (.encoding 0))))
    (Leaf.Dictionary.Gzip.convert {} {} {} good 2)
  expectError "dictionary-only input refused" (.source (.groupFailure 0 .dictionaryMissingFallback))
    (convertFallback {} {} {} (← input directory "dictionary_only") 2)
  expectError "V2 refused" (.source (.groupFailure 0 (.dictionaryPage 1 v2Offset (.parameters .unsupportedPage))))
    (convertFallback {} {} {} (← input directory "v2") 2)
  expectError "per-member controller cap"
    (.source (.groupFailure 0 (.dictionaryPage 0 firstGroupDictionaryOffset (.payload .gzipIncomplete))))
    (convertFallback {gzipCalls := 0} {} {} good 2)
  expectError "group row cap" (.source (.groupFailure 0 .rowLimit))
    (convertFallback {} {leaf.maxRows := 767} {} good 2)
  expectError "file row cap" (.rowLimit 1535 1536)
    (convertFallback {} {maxTotalRows := 1535} {} good 2)

  let earlierRows ← readCounts directory
  let outer : Leaf.Error :=
    .dictionaryPage 2 crcOffset (.checksumFailure (.mismatch declared.toUInt32 computed.toUInt32))
  checkLate "outer CRC" (← input directory "bad_outer_crc") earlierRows outer
  checkLate "first indexed data error" (← input directory "double_fault") earlierRows outer
  checkLate "dictionary member CRC" (← input directory "bad_dict_member") earlierRows
    (.dictionaryPage 0 dictionaryOffset (.payload (.malformed .gzip)))
  checkLate "reference member CRC" (← input directory "bad_reference_member") earlierRows
    (.dictionaryPage 1 referenceOffset (.references (.page (.payload (.malformed .gzip)))))
  checkLate "PLAIN member CRC" (← input directory "bad_plain_member") earlierRows
    (.dictionaryPage 3 lastPlainOffset (.plain (.payload (.malformed .gzip))))
  checkLate "reentry before body decode" (← input directory "reentry") earlierRows
    (.dictionaryPage 3 lastPlainOffset .dictionaryAfterFallback)
  checkLate "missing reference prefix" (← input directory "starts_plain") earlierRows
    (.dictionaryPage 1 referenceOffset (.encoding 0))
  checkLate "missing PLAIN suffix" (← input directory "no_suffix") earlierRows .dictionaryMissingFallback
  IO.println "Sixteen typed refusals and eight exact earlier-group prefixes passed"
