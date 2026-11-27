module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V1.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V1.Defs
import Batteries.Data.Except

open Silmaril Silmaril.Formats Silmaril.Numeric.Timestamp
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc
open Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V1 (Profile)

private abbrev dispatch := Leaf.Gzip.Dispatch.V1.convert

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
  let text ← IO.FS.readFile (directory / s!"expected-{index}.txt")
  (text.splitOn "\n").mapM fun line =>
    if line == "null" then pure none
    else match line.toInt? with
      | some count => pure (some count)
      | none => throw (IO.userError s!"invalid independent count: {line}")

private def checkBranch (bound : Leaf.Bound) (index : Nat) (expected : Profile) : IO Unit := do
  let planned ← require (Leaf.Gzip.Dispatch.V1.planGroup {} {} bound index)
  unless planned.choice == expected do
    throw (IO.userError s!"group {index} chose {repr planned.choice}, expected {repr expected}")
  let standalone := match expected with
    | .dictionary => Leaf.Dictionary.Gzip.readGroup {} {} bound index
    | .fallback => Leaf.Fallback.Gzip.readGroup {} {} bound index
  let observe (slots : Leaf.Slots bound) := slots.map (Option.map Ticks.ticks)
  let dispatched := Leaf.Gzip.Dispatch.V1.readGroup {} {} bound index
  unless dispatched.map observe == standalone.map observe do
    throw (IO.userError s!"dispatch differs from standalone group {index}")

private def checkSharedFailure (bound : Leaf.Bound) (index : Nat)
    (limits : Leaf.Gzip.Dispatch.V1.Limits) (expected : Leaf.Error) : IO Unit := do
  for result in [Leaf.Gzip.Dispatch.V1.readGroup limits {} bound index,
                 Leaf.Dictionary.Gzip.readGroup limits {} bound index,
                 Leaf.Fallback.Gzip.readGroup limits {} bound index] do
    match result with
    | .error actual =>
      unless actual == expected do throw (IO.userError s!"unexpected common error: {repr actual}")
    | .ok _ => throw (IO.userError "expected common framing failure")

private def checkLate (label : String) (wire : Bytes) (expectedRows : List (List (Option Int)))
    (index : Nat) (choice : Option Profile) (cause : Leaf.Error) : IO Unit := do
  let bound ← require (openBound {} wire 2)
  match choice with
  | some profile => checkBranch bound index profile
  | none => checkSharedFailure bound index {} cause
  let ⟨schema, trace⟩ ← require (Leaf.Gzip.Dispatch.V1.readBound {} {} bound)
  if positive : 0 < schema.width then
    unless (batchesAt trace ⟨0, positive⟩).map Arrow.TimestampBatch.Writer.tickCounts == expectedRows.take index do
      throw (IO.userError s!"{label}: lost the complete earlier batches")
  else throw (IO.userError "expected selected timestamp field")
  match trace.termination with
  | .readError actual =>
    unless actual == .groupFailure index cause do
      throw (IO.userError s!"{label}: unexpected source error {repr actual}")
  | _ => throw (IO.userError s!"{label}: expected the original indexed source error")
  expectError label (.source (.groupFailure index cause)) (dispatch {} {} {ipc.batches := 0} wire 2)

public def main (args : List String) : IO Unit := do
  let folder :: evidence := args | throw (IO.userError "expected a fixture directory and frame observations")
  let [some outerOffset, some declared, some computed, some fallbackMemberOffset, some dictionaryOffset,
       some referenceMemberOffset, some referenceOffset, some lastFirstOffset, some v2Offset] :=
    evidence.map String.toNat? | throw (IO.userError "invalid independent frame observations")
  let directory : System.FilePath := folder
  for name in ["utc_nanos", "local_micros"] do
    let wire ← input directory name
    let bound ← require (openBound {} wire 2)
    for (index, expected) in [(0, .dictionary), (1, .fallback), (2, .dictionary)] do
      checkBranch bound index expected
    let output ← require (dispatch {} {} {} wire 2)
    IO.FS.writeBinFile (directory / (name ++ ".arrows")) output.toByteArray

  let good ← input directory "utc_nanos"
  expectError "strict default" (.source (.groupFailure 0 (.chunkCodec 2))) (convert {} {} good 2)
  expectError "Snappy fallback default" (.source (.groupFailure 0 (.chunkCodec 2)))
    (Leaf.Fallback.Snappy.convert .modernOnly {} {} {} good 2)
  expectError "dictionary-only predecessor stays strict"
    (.source (.groupFailure 1 (.dictionaryPage 2 outerOffset (.encoding 0))))
    (Leaf.Dictionary.Gzip.convert {} {} {} good 2)
  expectError "fallback predecessor stays strict" (.source (.groupFailure 0 .dictionaryMissingFallback))
    (Leaf.Fallback.Gzip.convert {} {} {} good 2)
  let v2 ← input directory "v2"
  checkBranch (← require (openBound {} v2 2)) 0 .dictionary
  expectError "V2 is outside the selection" (.source (.groupFailure 0 (.dictionaryPage 1 v2Offset
      (.parameters .unsupportedPage)))) (dispatch {} {} {} v2 2)
  checkSharedFailure (← require (openBound {} good 2)) 0 {dictionary.maxChunkBytes := 0} .dictionaryChunkLimit
  expectError "common chunk cap" (.source (.groupFailure 0 .dictionaryChunkLimit))
    (dispatch {dictionary.maxChunkBytes := 0} {} {} good 2)

  let expectedRows ← [0, 1, 2].mapM (readCounts directory)
  let outer : Leaf.Error :=
    .dictionaryPage 2 outerOffset (.checksumFailure (.mismatch declared.toUInt32 computed.toUInt32))
  checkLate "fallback outer CRC" (← input directory "mutated_fallback_outer") expectedRows 1 (some .fallback) outer
  checkLate "earliest source group" (← input directory "mutated_two_failures") expectedRows 1 (some .fallback) outer
  checkLate "PLAIN member CRC" (← input directory "mutated_fallback_member") expectedRows 1 (some .fallback)
    (.dictionaryPage 3 fallbackMemberOffset (.plain (.payload (.malformed .gzip))))
  checkLate "dictionary member CRC" (← input directory "mutated_dictionary_member") expectedRows 2 (some .dictionary)
    (.dictionaryPage 0 dictionaryOffset (.payload (.malformed .gzip)))
  checkLate "reference member CRC" (← input directory "mutated_reference_member") expectedRows 2 (some .dictionary)
    (.dictionaryPage 2 referenceMemberOffset (.references (.page (.payload (.malformed .gzip)))))
  checkLate "reentry before payload" (← input directory "mutated_reentry") expectedRows 1 (some .fallback)
    (.dictionaryPage 3 fallbackMemberOffset .dictionaryAfterFallback)
  checkLate "missing reference prefix" (← input directory "mutated_missing_prefix") expectedRows 1 (some .fallback)
    (.dictionaryPage 1 referenceOffset (.encoding 0))
  checkLate "original data offset" (← input directory "mutated_data_offset") expectedRows 2 none
    (.dictionaryPage 1 lastFirstOffset .dataOffset)
  IO.println "Fourteen typed refusals and eight checked prefixes, with exact selected branch agreement"
