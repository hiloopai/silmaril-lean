module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Uncompressed.V2.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Uncompressed.V2.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Numeric.Timestamp (Ticks)

private abbrev strict := Leaf.Dictionary.Uncompressed.V2.convert
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
    let strictSlots ← require (Leaf.Dictionary.Uncompressed.V2.readGroup {} {} bound index)
    unless strictSlots.map (Option.map Ticks.ticks) == counts do
      throw (IO.userError s!"{name} group {index}: original signed nullable slots differed")
  let wire ← require (strict {} {} {} wire 2)
  IO.FS.writeBinFile (directory / (name ++ ".arrows")) wire.toByteArray

private def checkLate (directory : System.FilePath) (label : String) (index : Nat)
    (earlier : List (List (Option Int))) (cause : Leaf.Error) : IO Unit := do
  let wire ← input directory label
  let bound ← require (Leaf.Events.ToIpc.openBound {} wire 2)
  let ⟨schema, trace⟩ ← require (Leaf.Dictionary.Uncompressed.V2.readBound {} {} bound)
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
  let [some dict, some dictDeclared, some dictComputed, some levels, some levelDeclared, some levelComputed,
       some levelOrdinal, some reference, some referenceOrdinal, some v1, some plainOrdinal,
       some plainOffset, some firstDict, some firstData] :=
    evidence.map String.toNat? | throw (IO.userError "invalid independent frame observations")
  let directory : System.FilePath := folder
  for name in ["native_utc", "native_local", "mutated_true_flag", "mutated_absent_flag"] do
    checkSuccess directory name
  let utc ← observations directory "native_utc"
  let localCounts ← observations directory "native_local"
  let fallback ← observations directory "fallback"
  checkLate directory "mutated_dictionary_crc" 2 utc (crcError 0 dict dictDeclared dictComputed)
  checkLate directory "mutated_levels_crc" 2 utc (crcError levelOrdinal levels levelDeclared levelComputed)
  checkLate directory "mutated_reference" 2 localCounts
    (.dictionaryPage referenceOrdinal reference (.references (.outOfBounds 3)))
  checkLate directory "mutated_true_size" 2 utc
    (.dictionaryPage levelOrdinal levels (.references (.page (.payload .outputSizeMismatch))))
  checkLate directory "mutated_false_size" 2 utc (.framing (.header .invalidV2Lengths))
  checkLate directory "assembled_late_v1" 2 localCounts (.dictionaryPage 1 v1 (.parameters .unsupportedPage))
  checkLate directory "native_fallback" 1 fallback (.dictionaryPage plainOrdinal plainOffset (.encoding 0))

  let good ← input directory "native_utc"
  expectError "expected a dictionary" 0 .chunkEncoding (strict {} {} {} (← input directory "native_plain") 2)
  expectError "wrong codec" 0 (.chunkCodec 1) (strict {} {} {} (← input directory "native_snappy") 2)
  expectError "stored chunk cap" 0 .dictionaryChunkLimit (strict {maxChunkBytes := 0} {} {} good 2)
  expectError "dictionary entry cap" 0 (.dictionaryPage 0 firstDict .entryLimit)
    (strict {maxEntries := 2} {} {} good 2)
  expectError "dictionary byte cap" 0 (.dictionaryPage 0 firstDict (.payload .outputLimit))
    (strict {maxDictionaryBytes := 23} {} {} good 2)
  let dictionaryLimits : Leaf.Dictionary.Limits := {}
  expectError "reference byte cap" 0 (.dictionaryPage 1 firstData (.references .indexByteLimit))
    (strict {dictionaryLimits with indices.bytes := 0} {} {} good 2)

  let localWire ← input directory "native_local"
  let previous ← require (Leaf.Dictionary.convert .modernOnly {} {} {} localWire 2)
  let strictLocal ← require (strict {} {} {} localWire 2)
  unless previous.toByteArray == strictLocal.toByteArray do
    throw (IO.userError "checksum-free native V2 changed the dictionary-only observation")
  let _ ← require (Leaf.Dictionary.convert .modernOnly {} {} {} (← input directory "assembled_late_v1") 2)
  let fallbackBound ← require (Leaf.Events.ToIpc.openBound {} (← input directory "native_fallback") 2)
  let fallbackSlots ← require (Leaf.Fallback.readGroup {} {} fallbackBound 1)
  unless fallbackSlots.map (Option.map Ticks.ticks) == fallback[1]! do
    throw (IO.userError "original fallback profile changed the selected group")
  IO.println "Twelve checked groups, thirteen typed refusals and seven complete prefixes passed"
