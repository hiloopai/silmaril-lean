module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Uncompressed.V2.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Uncompressed.V2.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Numeric.Timestamp (Ticks)

private abbrev strict := Leaf.Fallback.Uncompressed.V2.convert
private abbrev IpcError := Leaf.Events.ToIpc.Error

private def input (directory : System.FilePath) (name : String) : IO Bytes :=
  (IO.FS.readBinFile (directory / (name ++ ".parquet"))).map fun raw => ⟨raw⟩

private def require {α ε : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def expectError (label : String) (index : Nat) (cause : Leaf.Error)
    (result : Except IpcError KBytes) : IO Unit :=
  match result with
  | .error actual =>
    let expected : IpcError := .source (.groupFailure index cause)
    unless actual == expected do
      throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: unexpected IPC output")

private def observations (directory : System.FilePath) (name : String) : IO (List (List (Option Int))) := do
  let text ← IO.FS.readFile (directory / (name ++ ".txt"))
  (text.splitOn "\n").mapM fun line => (line.splitOn ",").mapM fun word =>
    if word == "null" then pure none
    else match word.toInt? with
      | some count => pure (some count)
      | none => throw (IO.userError s!"invalid independent count {word}")

private def checkSuccess (directory : System.FilePath) (name : String) : IO Unit := do
  let wire ← input directory name
  let expected ← observations directory name
  let bound ← require (Leaf.Events.ToIpc.openBound {} wire 2)
  unless bound.snapshot.groupCount == expected.length do
    throw (IO.userError s!"{name}: original footer group count differed")
  for (counts, index) in expected.zipIdx do
    let strictSlots ← require (Leaf.Fallback.Uncompressed.V2.readGroup {} {} bound index)
    unless strictSlots.map (Option.map Ticks.ticks) == counts do
      throw (IO.userError s!"{name} group {index}: original signed nullable slots differed")
  let wire ← require (strict {} {} {} wire 2)
  IO.FS.writeBinFile (directory / (name ++ ".arrows")) wire.toByteArray

private def checkLate (directory : System.FilePath) (label : String) (index : Nat)
    (earlier : List (List (Option Int))) (cause : Leaf.Error) : IO Unit := do
  let wire ← input directory label
  let bound ← require (Leaf.Events.ToIpc.openBound {} wire 2)
  let ⟨schema, trace⟩ ← require (Leaf.Fallback.Uncompressed.V2.readBound {} {} bound)
  if present : 0 < schema.width then
    let batches := Leaf.Events.ToIpc.batchesAt trace ⟨0, present⟩
    unless batches.map Arrow.TimestampBatch.Writer.tickCounts == earlier.take index do
      throw (IO.userError s!"{label}: incorrect complete earlier batches")
  else throw (IO.userError "missing selected TIMESTAMP field")
  match trace.termination with
  | .readError actual =>
    unless actual == .groupFailure index cause do
      throw (IO.userError s!"{label}: unexpected indexed cause {repr actual}")
  | _ => throw (IO.userError s!"{label}: expected an indexed source failure")
  expectError label index cause (strict {} {} {ipc.batches := 0} wire 2)

private def crcError (ordinal offset declared computed : Nat) : Leaf.Error :=
  .dictionaryPage ordinal offset (.checksumFailure (.mismatch declared.toUInt32 computed.toUInt32))

public def main (args : List String) : IO Unit := do
  let folder :: evidence := args | throw (IO.userError "expected a fixture folder and original offsets")
  let [some dict, some dictDeclared, some dictComputed, some refs, some refsDeclared, some refsComputed,
       some plain, some plainDeclared, some plainComputed, some badRefWidth, some reentry,
       some v1, some firstDict, some firstPlain, some firstExpanded] :=
    evidence.map String.toNat? | throw (IO.userError "invalid independent frame observations")
  let directory : System.FilePath := folder
  for name in ["utc_nanos", "local_micros", "mutated_true_reference_flag", "mutated_absent_plain_flag"] do
    checkSuccess directory name
  let utc ← observations directory "utc_nanos"
  let localCounts ← observations directory "local_micros"
  checkLate directory "mutated_dictionary_crc" 1 utc (crcError 0 dict dictDeclared dictComputed)
  checkLate directory "mutated_reference_crc" 1 utc (crcError 1 refs refsDeclared refsComputed)
  checkLate directory "mutated_plain_crc" 1 utc (crcError 2 plain plainDeclared plainComputed)
  checkLate directory "mutated_competing_crc" 1 utc (crcError 2 plain plainDeclared plainComputed)
  checkLate directory "mutated_reference_size" 1 utc
    (.dictionaryPage 1 refs (.references (.page (.payload .outputSizeMismatch))))
  checkLate directory "mutated_plain_size" 1 utc
    (.dictionaryPage 2 plain (.plain (.payload .outputSizeMismatch)))
  checkLate directory "mutated_false_size" 1 utc (.framing (.header .invalidV2Lengths))
  checkLate directory "mutated_reference_width" 2 localCounts
    (.dictionaryPage 1 badRefWidth (.references (.hybrid .invalidWidth)))
  checkLate directory "mutated_reentry" 1 utc (.dictionaryPage 3 reentry .dictionaryAfterFallback)
  checkLate directory "mutated_starts_plain" 1 utc (.dictionaryPage 1 refs (.encoding 0))
  checkLate directory "assembled_late_v1" 2 localCounts (.dictionaryPage 1 v1 (.parameters .unsupportedPage))
  checkLate directory "assembled_dictionary_only" 2 localCounts .dictionaryMissingFallback

  let good ← input directory "utc_nanos"
  let settings : Leaf.Events.ToIpc.Limits := {}
  expectError "expected a dictionary" 0 .chunkEncoding
    (strict {} {} {} (← input directory "native_plain") 2)
  expectError "wrong codec" 0 (.chunkCodec 1)
    (strict {} {} {} (← input directory "native_snappy") 2)
  expectError "stored chunk cap" 0 .dictionaryChunkLimit (strict {maxChunkBytes := 0} {} {} good 2)
  expectError "dictionary entry cap" 0 (.dictionaryPage 0 firstDict .entryLimit)
    (strict {maxEntries := 2} {} {} good 2)
  expectError "PLAIN output cap" 0 (.dictionaryPage 2 firstPlain (.plain (.payload .outputLimit)))
    (strict {} {settings with leaf.page.uncompressedBytes := firstExpanded} {} good 2)
  expectError "strict dictionary-only rejects the first PLAIN page" 0 (.dictionaryPage 2 firstPlain (.encoding 0))
    (Leaf.Dictionary.Uncompressed.V2.convert {} {} {} good 2)

  let localWire ← input directory "local_micros"
  let previous ← require (Leaf.Fallback.convert .modernOnly {} {} {} localWire 2)
  let strictLocal ← require (strict {} {} {} localWire 2)
  unless previous.toByteArray == strictLocal.toByteArray do
    throw (IO.userError "checksum-free native V2 changed the original fallback observation")
  let _ ← require (Leaf.Fallback.convert .modernOnly {} {} {} (← input directory "assembled_late_v1") 2)
  let dictionaryBound ← require (Leaf.Events.ToIpc.openBound {} (← input directory "assembled_dictionary_only") 2)
  let dictionary ← require (Leaf.Dictionary.Uncompressed.V2.readGroup {} {} dictionaryBound 2)
  unless dictionary.map (Option.map Ticks.ticks) == localCounts[2]! do
    throw (IO.userError "strict dictionary-only profile changed the selected group")
  IO.println "Twelve checked groups, eighteen typed refusals and twelve complete prefixes passed"
