module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Snappy.Dispatch.V2.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Snappy.Dispatch.V2.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc
open Silmaril.Numeric.Timestamp (Ticks)

private abbrev dispatch := Leaf.Snappy.Dispatch.V2.convert

private inductive Profile where
  | plain
  | references
  | fallback
  deriving BEq, Repr

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

private def readObservations (directory : System.FilePath) (name : String) :
    IO (List (Profile × List (Option Int))) := do
  let text ← IO.FS.readFile (directory / (name ++ ".txt"))
  (text.splitOn "\n").mapM fun line => do
    let tag :: slots := line.splitOn "," | throw (IO.userError "empty independent group observation")
    let profile ← match tag with
      | "plain" => pure Profile.plain
      | "references" => pure Profile.references
      | "fallback" => pure Profile.fallback
      | _ => throw (IO.userError s!"invalid profile {tag}")
    let counts ← slots.mapM fun slot =>
      if slot == "null" then pure none
      else match slot.toInt? with
        | some count => pure (some count)
        | none => throw (IO.userError s!"invalid signed tick {slot}")
    return (profile, counts)

private def profileAt (bound : Leaf.Bound) (index : Nat) : IO Profile := do
  if ← require (Leaf.Snappy.Dispatch.V2.hasDictionary bound index) then
    let plan ← require (Leaf.Snappy.Dispatch.V2.planDictionary {} {} bound index)
    return match plan.profile with
      | .references => .references
      | .fallback => .fallback
  else return .plain

private def strictRead (limits : Leaf.Dictionary.Limits) (leafLimits : Leaf.Limits) (profile : Profile) (bound : Leaf.Bound) (index : Nat) :
    Except Leaf.Error (Leaf.Slots bound) :=
  match profile with
  | .plain => Leaf.SnappyV2.readGroup leafLimits bound index
  | .references => Leaf.Dictionary.Snappy.V2.readGroup limits leafLimits bound index
  | .fallback => Leaf.Fallback.Snappy.V2.readGroup limits leafLimits bound index

private def readSuccess (directory : System.FilePath) (name : String) : IO Unit := do
  let wire ← input directory name
  let expected ← readObservations directory name
  let bound ← require (openBound {} wire 2)
  unless bound.snapshot.groupCount == expected.length do
    throw (IO.userError "original group count differed")
  for ((profile, counts), index) in expected.zipIdx do
    unless (← profileAt bound index) == profile do
      throw (IO.userError s!"{name} group {index}: incorrect profile")
    let slots ← require (Leaf.Snappy.Dispatch.V2.readGroup {} {} bound index)
    let reference ← require (strictRead {} {} profile bound index)
    unless slots.map (Option.map Ticks.ticks) == counts &&
        reference.map (Option.map Ticks.ticks) == counts do
      throw (IO.userError s!"{name} group {index}: strict or dispatched values differed")
  let bytes ← require (dispatch {} {} {} wire 2)
  IO.FS.writeBinFile (directory / (name ++ ".arrows")) bytes.toByteArray

private def expectGroupError {α : Type} (label : String) (expected : Leaf.Error)
    (result : Except Leaf.Error α) : IO Unit :=
  match result with
  | .error actual => unless actual == expected do
      throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly admitted the group")

private def checkPrefix (label : String) (wire : Bytes) (bound : Leaf.Bound)
    (expected : List (Profile × List (Option Int))) (limits : Leaf.Dictionary.Limits)
    (index : Nat) (cause : Leaf.Error) : IO Unit := do
  let ⟨schema, trace⟩ ← require (Leaf.Snappy.Dispatch.V2.readBound limits {} bound)
  if positive : 0 < schema.width then
    let batches := batchesAt trace ⟨0, positive⟩
    unless batches.map Arrow.TimestampBatch.Writer.tickCounts == (expected.take index).map Prod.snd do
      throw (IO.userError s!"{label}: lost an earlier complete group")
  else throw (IO.userError "expected selected TIMESTAMP field")
  match trace.termination with
  | .readError actual =>
    unless actual == .groupFailure index cause do
      throw (IO.userError s!"{label}: indexed cause {repr actual}")
  | _ => throw (IO.userError s!"{label}: expected indexed source error")
  expectError label (.source (.groupFailure index cause)) (dispatch limits {} {ipc.batches := 0} wire 2)

private def checkLate (directory : System.FilePath) (label : String)
    (expected : List (Profile × List (Option Int))) (index : Nat) (profile : Profile) (cause : Leaf.Error) : IO Unit := do
  let wire ← input directory label
  let bound ← require (openBound {} wire 2)
  unless (← profileAt bound index) == profile do
    throw (IO.userError s!"{label}: unexpected profile")
  expectGroupError label cause (strictRead {} {} profile bound index)
  checkPrefix label wire bound expected {} index cause

private def checkSetup (directory : System.FilePath) (label : String)
    (expected : List (Profile × List (Option Int))) (limits : Leaf.Dictionary.Limits)
    (index : Nat) (cause : Leaf.Error) : IO Unit := do
  let wire ← input directory label
  let bound ← require (openBound {} wire 2)
  unless ← require (Leaf.Snappy.Dispatch.V2.hasDictionary bound index) do
    throw (IO.userError s!"{label}: expected a dictionary offset")
  expectGroupError label cause (Leaf.Snappy.Dispatch.V2.planDictionary limits {} bound index)
  expectGroupError label cause (strictRead limits {} .references bound index)
  expectGroupError label cause (strictRead limits {} .fallback bound index)
  checkPrefix label wire bound expected limits index cause

private def checksum (declared computed : Nat) : Parquet.Page.Checksum.Error :=
  .mismatch declared.toUInt32 computed.toUInt32

private def dictionaryCRC (ordinal offset declared computed : Nat) : Leaf.Error :=
  .dictionaryPage ordinal offset (.checksumFailure (checksum declared computed))

public def main (args : List String) : IO Unit := do
  let folder :: evidence := args | throw (IO.userError "expected a fixture folder and original offsets")
  let [some plain, some plainDeclared, some plainComputed, some dictionary, some dictDeclared, some dictComputed,
       some references, some refsDeclared, some refsComputed, some fallback, some fallbackDeclared,
       some fallbackComputed, some reentry, some offset, some v1, some chunkCap] := evidence.map String.toNat? |
    throw (IO.userError "invalid independent frame observations")
  let directory : System.FilePath := folder
  for name in ["native_utc", "native_local", "assembled_utc", "assembled_local"] do
    readSuccess directory name
  let utc ← readObservations directory "assembled_utc"
  let plainCRC := Leaf.Error.pageChecksum 0 plain (checksum plainDeclared plainComputed)
  checkLate directory "mutated_plain_crc" utc 1 .plain plainCRC
  checkLate directory "mutated_dictionary_crc" utc 3 .references (dictionaryCRC 0 dictionary dictDeclared dictComputed)
  checkLate directory "mutated_reference_crc" utc 3 .references (dictionaryCRC 1 references refsDeclared refsComputed)
  checkLate directory "mutated_fallback_crc" utc 2 .fallback (dictionaryCRC 2 fallback fallbackDeclared fallbackComputed)
  checkLate directory "mutated_competing_crc" utc 1 .plain plainCRC
  checkLate directory "mutated_reentry" utc 2 .fallback (.dictionaryPage 3 reentry .dictionaryAfterFallback)
  checkLate directory "assembled_v1" utc 2 .references (.dictionaryPage 1 v1 (.parameters .unsupportedPage))
  checkSetup directory "mutated_data_offset" utc {} 2 (.dictionaryPage 1 offset .dataOffset)
  checkSetup directory "assembled_utc" utc {maxChunkBytes := chunkCap} 2 .dictionaryChunkLimit
  checkSetup directory "wrong_codec" utc {} 0 (.chunkCodec 0)

  let good ← input directory "assembled_utc"
  expectError "source file cap" (.fileByteLimit 0 good.length)
    (dispatch {} {maxFileBytes := 0} {ipc.batches := 0} good 2)
  expectError "the default rejects codec 1" (.source (.groupFailure 0 (.chunkCodec 1))) (convert {} {} good 2)
  let bound ← require (openBound {} good 2)
  let absent := bound.snapshot.groupCount
  expectGroupError "group lookup" (.groupIndex absent) (Leaf.Snappy.Dispatch.V2.readGroup {} {} bound absent)
  for profile in [Profile.plain, .references, .fallback] do
    expectGroupError "standalone group lookup" (.groupIndex absent) (strictRead {} {} profile bound absent)
  IO.println "Twenty original group decisions, thirteen typed refusal controls and ten complete prefixes passed"
