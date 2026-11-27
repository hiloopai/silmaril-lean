module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Zstd.V2.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Zstd.V2.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc

private abbrev convertZstd := Leaf.Fallback.Zstd.V2.convert

private def require {α ε : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def input (directory : System.FilePath) (name : String) : IO Bytes :=
  (IO.FS.readBinFile (directory / (name ++ ".parquet"))).map fun raw => ⟨raw⟩

private def expectError {ε : Type} [DecidableEq ε] [Repr ε] (label : String) (expected : ε)
    (result : Except ε KBytes) : IO Unit :=
  match result with
  | .error actual => unless actual == expected do
      throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: unexpected output")

private def readCounts (directory : System.FilePath) (name : String) : IO (List (List (Option Int))) := do
  let text ← IO.FS.readFile (directory / (name ++ ".txt"))
  (text.splitOn "\n").mapM fun line =>
    (line.splitOn ",").mapM fun slot =>
      if slot == "null" then pure none
      else match slot.toInt? with
        | some count => pure (some count)
        | none => throw (IO.userError s!"invalid independent tick {slot}")

private def groupFailure (index : Nat) (cause : Leaf.Zstd.V2.GroupError) : Leaf.Zstd.V2.Error :=
  .source (.groupFailure index cause)

private def checkLate (directory : System.FilePath) (label : String)
    (expected : List (List (Option Int))) (index : Nat) (cause : Leaf.Zstd.V2.GroupError) : IO Unit := do
  let wire ← input directory label
  let bound ← require (openBound {} wire 2)
  let ⟨schema, trace⟩ ← require (Leaf.Fallback.Zstd.V2.readBound {} {} bound)
  if positive : 0 < schema.width then
    let column : Fin schema.width := ⟨0, positive⟩
    let batches := trace.batches.map fun batch =>
      Arrow.TimestampBatch.Writer.tickCounts (binding := bindingAt schema column) (batch.values column)
    unless batches == expected.take index do
      throw (IO.userError s!"{label}: lost an earlier complete batch")
  else throw (IO.userError "expected selected TIMESTAMP field")
  match trace.termination with
  | .readError actual =>
    unless actual == .groupFailure index cause do
      throw (IO.userError s!"{label}: unexpected source error {repr actual}")
  | _ => throw (IO.userError s!"{label}: expected indexed source error")
  expectError label (groupFailure index cause) (convertZstd {} {} {ipc.batches := 0} wire 2)

private def crcFailure (ordinal offset declared computed : Nat) : Leaf.Zstd.V2.GroupError :=
  .checksum ordinal offset (.mismatch declared.toUInt32 computed.toUInt32)

public def main (args : List String) : IO Unit := do
  let folder :: evidence := args | throw (IO.userError "expected fixture folder and original offsets")
  let [some dictOffset, some dictDeclared, some dictComputed, some refOffset, some refDeclared, some refComputed,
       some plainOffset, some plainDeclared, some plainComputed, some compressedPlain, some tailReference,
       some firstDictionary, some firstPlain, some v1Offset, some expandedCap] := evidence.map String.toNat? |
    throw (IO.userError "invalid independent frame observations")
  let directory : System.FilePath := folder
  for name in ["utc_nanos", "local_micros"] do
    let output ← require (convertZstd {} {} {} (← input directory name) 2)
    IO.FS.writeBinFile (directory / (name ++ ".arrows")) output.toByteArray

  let expected ← readCounts directory "utc_nanos"
  let plainFailure := crcFailure 2 plainOffset plainDeclared plainComputed
  checkLate directory "mutated_dictionary_crc" expected 1 (crcFailure 0 dictOffset dictDeclared dictComputed)
  checkLate directory "mutated_reference_crc" expected 1 (crcFailure 1 refOffset refDeclared refComputed)
  checkLate directory "mutated_plain_crc" expected 1 plainFailure
  checkLate directory "mutated_dictionary_magic" expected 1 (.decode 0 dictOffset (.frame (.frame .badMagic)))
  checkLate directory "mutated_reference_magic" expected 2 (.decode 1 tailReference (.frame (.frame .badMagic)))
  checkLate directory "mutated_plain_magic" expected 1 (.decode 3 compressedPlain (.frame (.frame .badMagic)))
  checkLate directory "mutated_two_groups" expected 1 plainFailure
  checkLate directory "mutated_raw_plain_flag_true" expected 1 (.decode 2 plainOffset (.frame (.frame .badMagic)))
  checkLate directory "mutated_frame_flag_false" expected 1 (.selection (.framing (.header .invalidV2Lengths)))
  checkLate directory "mutated_rows_before_crc" expected 1 (.selection (.rowCount 384 385))
  checkLate directory "mutated_reentry" expected 1
    (.selection (.dictionaryPage 3 compressedPlain .dictionaryAfterFallback))
  checkLate directory "mutated_unknown_before_reentry" expected 1
    (.selection (.dictionaryPage 1 refOffset (.encoding 5)))
  checkLate directory "mutated_starts_plain" expected 1 (.selection (.dictionaryPage 1 refOffset (.encoding 0)))
  let widthFailure : Leaf.Zstd.V2.GroupError := .references 1 refOffset (.hybrid .invalidWidth)
  checkLate directory "mutated_raw_width" expected 1 widthFailure
  checkLate directory "mutated_two_pages" expected 1 widthFailure

  let good ← input directory "utc_nanos"
  expectError "strict default refuses codec 6" (.source (.groupFailure 0 (.chunkCodec 6))) (convert {} {} good 2)
  expectError "strict Zstd PLAIN refuses a dictionary chunk" (groupFailure 0 (.selection .chunkEncoding))
    (Leaf.Zstd.V2.convert {} {} {} good 2)
  expectError "strict Zstd references refuse original first PLAIN page"
    (groupFailure 0 (.selection (.dictionaryPage 2 firstPlain (.encoding 0))))
    (Leaf.Dictionary.Zstd.V2.convert {} {} {} good 2)
  expectError "PLAIN-only chunk refused" (groupFailure 0 (.selection .chunkEncoding))
    (convertZstd {} {} {} (← input directory "plain_only") 2)
  expectError "dictionary-only chunk has no fallback" (groupFailure 0 (.selection .dictionaryMissingFallback))
    (convertZstd {} {} {} (← input directory "dictionary_only") 2)
  expectError "V1 pages refused" (groupFailure 0 (.selection (.dictionaryPage 1 v1Offset (.parameters .unsupportedPage))))
    (convertZstd {} {} {} (← input directory "v1") 2)
  expectError "stored chunk cap" (groupFailure 0 (.selection .dictionaryChunkLimit))
    (convertZstd {dictionary.maxChunkBytes := 0} {} {} good 2)
  expectError "expanded chunk cap includes the dictionary and both phases" (groupFailure 0 .expandedChunkLimit)
    (convertZstd {maxExpandedChunkBytes := expandedCap} {} {} good 2)
  expectError "group row cap" (groupFailure 0 (.selection .rowLimit))
    (convertZstd {} {leaf.maxRows := 383} {} good 2)
  expectError "file row cap" (.openFailure (.rowLimit 1151 1152))
    (convertZstd {} {maxTotalRows := 1151} {} good 2)
  expectError "dictionary entry cap" (groupFailure 0 (.selection (.dictionaryPage 0 firstDictionary .entryLimit)))
    (convertZstd {dictionary.maxEntries := 0} {} {} good 2)
  expectError "Zstd window cap applies to the dictionary"
    (groupFailure 0 (.decode 0 firstDictionary (.frame (.frame .windowLimit))))
    (convertZstd {compression := ⟨0, 43690⟩} {} {} good 2)
  IO.println "Twenty-seven typed refusals and fifteen exact earlier-group prefixes passed"
