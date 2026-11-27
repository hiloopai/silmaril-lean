module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.V2.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.V2.Defs

import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Gzip.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc

private abbrev convertFallback := Leaf.Fallback.Gzip.V2.convert

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
  let ⟨schema, trace⟩ ← require (Leaf.Fallback.Gzip.V2.readBound {} {} bound)
  if positive : 0 < schema.width then
    unless (batchesAt trace ⟨0, positive⟩).map Arrow.TimestampBatch.Writer.tickCounts == earlierRows.take index do
      throw (IO.userError s!"{label}: lost a completed original batch")
  else throw (IO.userError "expected selected TIMESTAMP field")
  match trace.termination with
  | .readError actual =>
    unless actual == .groupFailure index cause do
      throw (IO.userError s!"{label}: unexpected source error {repr actual}")
  | _ => throw (IO.userError s!"{label}: expected indexed source error")
  expectError label (.source (.groupFailure index cause)) (convertFallback {} {} {ipc.batches := 0} wire 2)

private def crcFailure (page offset declared computed : Nat) : Leaf.Error :=
  .dictionaryPage page offset (.checksumFailure (.mismatch declared.toUInt32 computed.toUInt32))

public def main (args : List String) : IO Unit := do
  let folder :: evidence := args | throw (IO.userError "expected fixture directory and frame observations")
  let [some refOffset, some refDeclared, some refComputed, some plainOffset, some plainDeclared,
       some plainComputed, some dictOffset, some tailReference, some tailPlain, some firstReference,
       some firstPlain, some firstDict, some v1Offset] := evidence.map String.toNat? |
    throw (IO.userError "invalid independent frame observations")
  let directory : System.FilePath := folder
  for name in ["utc_nanos", "local_micros"] do
    let output ← require (convertFallback {} {} {} (← input directory name) 2)
    IO.FS.writeBinFile (directory / (name ++ ".arrows")) output.toByteArray

  let good ← input directory "utc_nanos"
  let inputLimits : Limits := {}
  let v1 ← input directory "v1"
  let dictionaryOnly ← input directory "dictionary_only"
  expectError "strict default" (.source (.groupFailure 0 (.chunkCodec 2))) (convert {} {} good 2)
  expectError "Snappy fallback stays strict" (.source (.groupFailure 0 (.chunkCodec 2)))
    (Leaf.Fallback.Snappy.convert .modernOnly {} {} {} good 2)
  expectError "V2 dictionary predecessor stays strict"
    (.source (.groupFailure 0 (.dictionaryPage 2 firstPlain (.encoding 0))))
    (Leaf.Dictionary.Gzip.V2.convert {} {} {} good 2)
  expectError "V1 fallback predecessor stays strict"
    (.source (.groupFailure 0 (.dictionaryPage 1 firstReference (.parameters .unsupportedPage))))
    (Leaf.Fallback.Gzip.convert {} {} {} good 2)
  expectError "dictionary-only sequence" (.source (.groupFailure 0 .dictionaryMissingFallback))
    (convertFallback {} {} {} dictionaryOnly 2)
  expectError "V1 data refused" (.source (.groupFailure 0 (.dictionaryPage 1 v1Offset (.parameters .unsupportedPage))))
    (convertFallback {} {} {} v1 2)
  expectError "GZIP controller cap"
    (.source (.groupFailure 0 (.dictionaryPage 0 firstDict (.payload .gzipIncomplete))))
    (convertFallback {gzipCalls := 0} {} {} good 2)
  expectError "selected chunk cap" (.source (.groupFailure 0 .dictionaryChunkLimit))
    (convertFallback {dictionary.maxChunkBytes := 0} {} {} good 2)
  expectError "raw definitions cap"
    (.source (.groupFailure 0 (.dictionaryPage 1 firstReference (.references (.page (.levels .definitionByteLimit))))))
    (convertFallback {} {inputLimits with leaf.page.levels.bytes := 0} {} good 2)
  expectError "group row cap" (.source (.groupFailure 0 .rowLimit))
    (convertFallback {} {leaf.maxRows := 767} {} good 2)
  expectError "file row cap" (.rowLimit 2303 2304)
    (convertFallback {} {maxTotalRows := 2303} {} good 2)

  let rows ← [0, 1].mapM (readCounts directory)
  checkLate "reference outer CRC covers raw levels" (← input directory "bad_reference_outer_crc") rows 1
    (crcFailure 1 refOffset refDeclared refComputed)
  checkLate "PLAIN outer CRC covers raw levels" (← input directory "bad_plain_outer_crc") rows 1
    (crcFailure 2 plainOffset plainDeclared plainComputed)
  checkLate "dictionary member CRC" (← input directory "bad_dictionary_member") rows 1
    (.dictionaryPage 0 dictOffset (.payload (.malformed .gzip)))
  checkLate "reference suffix member CRC" (← input directory "bad_reference_member") rows 2
    (.dictionaryPage 1 tailReference (.references (.page (.payload (.malformed .gzip)))))
  checkLate "PLAIN suffix member CRC" (← input directory "bad_plain_member") rows 1
    (.dictionaryPage 3 tailPlain (.plain (.payload (.malformed .gzip))))
  checkLate "raw PLAIN extent" (← input directory "bad_raw_plain_extent") rows 1
    (.framing (.header .invalidV2Lengths))
  let rawCause : Leaf.Error := .dictionaryPage 1 refOffset (.references (.hybrid .invalidWidth))
  checkLate "raw references" (← input directory "bad_raw_reference") rows 1 rawCause
  checkLate "earliest body error after valid planning" (← input directory "two_page_faults") rows 1 rawCause
  checkLate "earliest source group" (← input directory "two_group_faults") rows 1 rawCause
  checkLate "reentry before body decode" (← input directory "reentry") rows 1
    (.dictionaryPage 3 tailPlain .dictionaryAfterFallback)
  checkLate "missing reference prefix" (← input directory "starts_plain") rows 1
    (.dictionaryPage 1 refOffset (.encoding 0))
  checkLate "missing PLAIN suffix" (← input directory "no_suffix") rows 1 .dictionaryMissingFallback
  IO.println "Twenty-three typed refusals and twelve complete earlier-group prefixes passed"
