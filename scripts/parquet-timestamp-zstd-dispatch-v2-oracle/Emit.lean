module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc
open Silmaril.Numeric.Timestamp (Ticks)

private abbrev dispatch := Leaf.Zstd.Dispatch.V2.convert

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

private def expectError {ε : Type} [DecidableEq ε] [Repr ε] (label : String) (expected : ε)
    (result : Except ε KBytes) : IO Unit :=
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
  if ← require (Leaf.Zstd.Dispatch.V2.hasDictionary bound index) then
    let plan ← require (Leaf.Zstd.Dispatch.V2.planDictionary {} {} bound index)
    return match plan.profile with
      | .references => .references
      | .fallback => .fallback
  else return .plain

private def strictRead (profile : Profile) (bound : Leaf.Bound) (index : Nat) :
    Except Leaf.Zstd.V2.GroupError (Leaf.Slots bound) :=
  match profile with
  | .plain => Leaf.Zstd.V2.readGroup (Leaf.Dictionary.Zstd.V2.scalarLimits {}) {} bound index
  | .references => Leaf.Dictionary.Zstd.V2.readGroup {} {} bound index
  | .fallback => Leaf.Fallback.Zstd.V2.readGroup {} {} bound index

private def readSuccess (directory : System.FilePath) (name : String) : IO Unit := do
  let wire ← input directory name
  let expected ← readObservations directory name
  let bound ← require (openBound {} wire 2)
  unless bound.snapshot.groupCount == expected.length do
    throw (IO.userError "original group count differed")
  for ((profile, counts), index) in expected.zipIdx do
    unless (← profileAt bound index) == profile do
      throw (IO.userError s!"{name} group {index}: incorrect profile")
    let slots ← require (Leaf.Zstd.Dispatch.V2.readGroup {} {} bound index)
    let reference ← require (strictRead profile bound index)
    unless slots.map (Option.map Ticks.ticks) == counts &&
        reference.map (Option.map Ticks.ticks) == counts do
      throw (IO.userError s!"{name} group {index}: strict or dispatched values differed")
  let bytes ← require (dispatch {} {} {} wire 2)
  IO.FS.writeBinFile (directory / (name ++ ".arrows")) bytes.toByteArray

private def checkLate (directory : System.FilePath) (label : String)
    (expected : List (Profile × List (Option Int))) (index : Nat) (cause : Leaf.Zstd.V2.GroupError) : IO Unit := do
  let wire ← input directory label
  let bound ← require (openBound {} wire 2)
  let profile ← profileAt bound index
  unless expected[index]?.map Prod.fst == some profile do
    throw (IO.userError s!"{label}: unexpected profile")
  match strictRead profile bound index with
  | .error strict =>
    unless strict == cause do throw (IO.userError s!"{label}: strict cause {repr strict}")
  | .ok _ => throw (IO.userError s!"{label}: strict reader admitted the group")
  let ⟨schema, trace⟩ ← require (Leaf.Zstd.Dispatch.V2.readBound {} {} bound)
  if positive : 0 < schema.width then
    let column : Fin schema.width := ⟨0, positive⟩
    let batches := trace.batches.map fun batch =>
      Arrow.TimestampBatch.Writer.tickCounts (binding := bindingAt schema column) (batch.values column)
    unless batches == (expected.take index).map Prod.snd do
      throw (IO.userError s!"{label}: lost an earlier complete group")
  else throw (IO.userError "expected selected TIMESTAMP field")
  match trace.termination with
  | .readError actual =>
    unless actual == .groupFailure index cause do
      throw (IO.userError s!"{label}: indexed cause {repr actual}")
  | _ => throw (IO.userError s!"{label}: expected indexed source error")
  expectError label (.source (.groupFailure index cause)) (dispatch {} {} {ipc.batches := 0} wire 2)

private def groupFailure (index : Nat) (cause : Leaf.Zstd.V2.GroupError) : Leaf.Zstd.V2.Error :=
  .source (.groupFailure index cause)

private def crcFailure (ordinal offset declared computed : Nat) : Leaf.Zstd.V2.GroupError :=
  .checksum ordinal offset (.mismatch declared.toUInt32 computed.toUInt32)

public def main (args : List String) : IO Unit := do
  let folder :: evidence := args | throw (IO.userError "expected fixture folder and original offsets")
  let [some plainOffset, some plainDeclared, some plainActual, some dictionaryOffset, some dictDeclared,
       some dictActual, some fallbackRefOffset, some fallbackDeclared, some fallbackActual,
       some compressedPlain, some fallbackPlain, some rawPlain, some reentry, some reference,
       some refsCap, some plainCap, some plainV1Offset, some dictionaryV1Offset] := evidence.map String.toNat? |
    throw (IO.userError "invalid independent frame observations")
  let directory : System.FilePath := folder
  for name in ["native_utc", "native_local", "assembled_utc", "assembled_local"] do
    readSuccess directory name

  let expected ← readObservations directory "assembled_utc"
  let plainFailure := crcFailure 0 plainOffset plainDeclared plainActual
  checkLate directory "bad_plain_crc" expected 1 plainFailure
  checkLate directory "bad_dictionary_crc" expected 3 (crcFailure 0 dictionaryOffset dictDeclared dictActual)
  checkLate directory "bad_fallback_crc" expected 2 (crcFailure 1 fallbackRefOffset fallbackDeclared fallbackActual)
  checkLate directory "bad_plain_magic" expected 1 (.decode 2 compressedPlain (.frame (.frame .badMagic)))
  checkLate directory "bad_fallback_magic" expected 2 (.decode 2 fallbackPlain (.frame (.frame .badMagic)))
  checkLate directory "bad_dictionary_magic" expected 3 (.decode 0 dictionaryOffset (.frame (.frame .badMagic)))
  checkLate directory "two_bad_groups" expected 1 plainFailure
  checkLate directory "bad_plain_flag" expected 4 (.decode 0 rawPlain (.frame (.frame .badMagic)))
  checkLate directory "bad_reentry" expected 5 (.selection (.dictionaryPage 3 reentry .dictionaryAfterFallback))
  checkLate directory "bad_reference_width" expected 3 (.references 1 reference (.hybrid .invalidWidth))

  let good ← input directory "assembled_utc"
  let plain ← input directory "plain_utc_producer"
  let refs ← input directory "native_utc"
  expectError "strict default refuses codec 6" (.source (.groupFailure 0 (.chunkCodec 6))) (convert {} {} good 2)
  expectError "strict PLAIN rejects a dictionary group" (groupFailure 0 (.selection .chunkEncoding))
    (Leaf.Zstd.V2.convert {} {} {} good 2)
  expectError "strict references reject a PLAIN group" (groupFailure 1 (.selection .chunkEncoding))
    (Leaf.Dictionary.Zstd.V2.convert {} {} {} good 2)
  expectError "strict fallback requires a PLAIN suffix" (groupFailure 0 (.selection .dictionaryMissingFallback))
    (Leaf.Fallback.Zstd.V2.convert {} {} {} good 2)
  expectError "wrong codec" (groupFailure 0 (.selection (.chunkCodec 1)))
    (dispatch {} {} {} (← input directory "snappy") 2)
  expectError "V1 PLAIN refused" (groupFailure 0 (.expectedV2 0 plainV1Offset))
    (dispatch {} {} {} (← input directory "plain_v1") 2)
  expectError "V1 dictionary-backed page refused"
    (groupFailure 0 (.selection (.dictionaryPage 1 dictionaryV1Offset (.parameters .unsupportedPage))))
    (dispatch {} {} {} (← input directory "dictionary_v1") 2)
  expectError "PLAIN stored chunk cap" (groupFailure 0 (.selection .chunkByteLimit))
    (dispatch {dictionary.maxChunkBytes := 0} {} {} plain 2)
  expectError "dictionary stored chunk cap" (groupFailure 0 (.selection .dictionaryChunkLimit))
    (dispatch {dictionary.maxChunkBytes := 0} {} {} refs 2)
  expectError "PLAIN expanded chunk cap" (groupFailure 0 .expandedChunkLimit)
    (dispatch {maxExpandedChunkBytes := plainCap} {} {} plain 2)
  expectError "dictionary expanded chunk cap" (groupFailure 0 .expandedChunkLimit)
    (dispatch {maxExpandedChunkBytes := refsCap} {} {} refs 2)
  expectError "file row cap" (.openFailure (.rowLimit 1599 1600))
    (dispatch {} {maxTotalRows := 1599} {} good 2)
  IO.println "Twenty original group classifications, twenty-two typed refusals and ten exact prefixes passed"
