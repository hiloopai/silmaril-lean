module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc
open Silmaril.Numeric.Timestamp (Ticks)

private abbrev dispatch := Leaf.Gzip.Dispatch.V2.convert

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
  if ← require (Leaf.Gzip.Dispatch.V2.hasDictionary bound index) then
    let plan ← require (Leaf.Gzip.Dispatch.V2.planDictionary {} {} bound index)
    return match plan.profile with
      | .references => .references
      | .fallback => .fallback
  else return .plain

private def strictRead (profile : Profile) (bound : Leaf.Bound) (index : Nat) :
    Except Leaf.Error (Leaf.Slots bound) :=
  match profile with
  | .plain => Leaf.Gzip.V2.readGroup {} {} bound index
  | .references => Leaf.Dictionary.Gzip.V2.readGroup {} {} bound index
  | .fallback => Leaf.Fallback.Gzip.V2.readGroup {} {} bound index

private def readSuccess (directory : System.FilePath) (name : String) : IO Unit := do
  let wire ← input directory name
  let expected ← readObservations directory name
  let bound ← require (openBound {} wire 2)
  unless bound.snapshot.groupCount == expected.length do
    throw (IO.userError "original group count differed")
  for ((profile, counts), index) in expected.zipIdx do
    unless (← profileAt bound index) == profile do
      throw (IO.userError s!"{name} group {index}: incorrect profile")
    let slots ← require (Leaf.Gzip.Dispatch.V2.readGroup {} {} bound index)
    let reference ← require (strictRead profile bound index)
    unless slots.map (Option.map Ticks.ticks) == counts &&
        reference.map (Option.map Ticks.ticks) == counts do
      throw (IO.userError s!"{name} group {index}: strict or dispatched values differed")
  let bytes ← require (dispatch {} {} {} wire 2)
  IO.FS.writeBinFile (directory / (name ++ ".arrows")) bytes.toByteArray

private def checkLate (directory : System.FilePath) (label : String)
    (expected : List (Profile × List (Option Int))) (index : Nat) (cause : Leaf.Error) : IO Unit := do
  let wire ← input directory label
  let bound ← require (openBound {} wire 2)
  let profile ← profileAt bound index
  unless expected[index]?.map Prod.fst == some profile do
    throw (IO.userError s!"{label}: unexpected profile")
  match strictRead profile bound index with
  | .error strict =>
    unless strict == cause do throw (IO.userError s!"{label}: strict cause {repr strict}")
  | .ok _ => throw (IO.userError s!"{label}: strict reader admitted the group")
  let ⟨schema, trace⟩ ← require (Leaf.Gzip.Dispatch.V2.readBound {} {} bound)
  if positive : 0 < schema.width then
    unless (batchesAt trace ⟨0, positive⟩).map Arrow.TimestampBatch.Writer.tickCounts ==
        (expected.take index).map Prod.snd do
      throw (IO.userError s!"{label}: lost an earlier complete group")
  else throw (IO.userError "expected selected TIMESTAMP field")
  match trace.termination with
  | .readError actual =>
    unless actual == .groupFailure index cause do
      throw (IO.userError s!"{label}: indexed cause {repr actual}")
  | _ => throw (IO.userError s!"{label}: expected indexed source error")
  expectError label (.source (.groupFailure index cause)) (dispatch {} {} {ipc.batches := 0} wire 2)

public def main (args : List String) : IO Unit := do
  let folder :: evidence := args | throw (IO.userError "expected a fixture folder and original offsets")
  let [some plainOffset, some plainCRC, some plainActual, some refOffset, some refCRC, some refActual,
       some dictionary, some fallbackReference, some fallbackPlain, some fallbackLast, some firstDictionary,
       some laterPlain, some plainV1Offset] := evidence.map String.toNat? |
    throw (IO.userError "bad original frame observations")
  let directory : System.FilePath := folder
  for name in ["native_utc", "native_local", "assembled_utc", "assembled_local"] do
    readSuccess directory name

  let expected ← readObservations directory "assembled_utc"
  let firstPlainCRC : Leaf.Error :=
    .pageChecksum 0 plainOffset (.mismatch plainCRC.toUInt32 plainActual.toUInt32)
  checkLate directory "bad_plain_outer" expected 1 firstPlainCRC
  checkLate directory "bad_plain_inner" expected 1 (.page 1 (.scalar (.payload (.malformed .gzip))))
  checkLate directory "bad_fallback_inner" expected 2
    (.dictionaryPage 2 fallbackPlain (.plain (.payload (.malformed .gzip))))
  checkLate directory "bad_reference_outer" expected 5
    (.dictionaryPage 2 refOffset (.checksumFailure (.mismatch refCRC.toUInt32 refActual.toUInt32)))
  checkLate directory "bad_dictionary_inner" expected 5
    (.dictionaryPage 0 dictionary (.payload (.malformed .gzip)))
  checkLate directory "two_bad_groups" expected 1 firstPlainCRC
  checkLate directory "bad_fallback_reentry" expected 2
    (.dictionaryPage 3 fallbackLast .dictionaryAfterFallback)
  checkLate directory "bad_tag_before_reentry" expected 2 (.dictionaryPage 1 fallbackReference (.encoding 5))

  let good ← input directory "assembled_utc"
  let plain ← input directory "plain_utc_producer"
  let v1 ← input directory "plain_v1"
  let snappy ← input directory "snappy"
  let assembledBound ← require (openBound {} good 2)
  let plainGroup ← require (Leaf.Gzip.V2.checkGroup {} {} assembledBound 1)
  unless plainGroup.frames[1]?.map (·.header.start) == some laterPlain do
    throw (IO.userError "original second PLAIN header offset differed")
  expectError "strict default" (.source (.groupFailure 0 (.chunkCodec 2))) (convert {} {} good 2)
  expectError "PLAIN-only rejects a dictionary group" (.source (.groupFailure 0 .chunkEncoding))
    (Leaf.Gzip.V2.convert {} {} {} good 2)
  expectError "dictionary-only rejects a PLAIN group" (.source (.groupFailure 1 .chunkEncoding))
    (Leaf.Dictionary.Gzip.V2.convert {} {} {} good 2)
  expectError "fallback-only requires a PLAIN suffix" (.source (.groupFailure 0 .dictionaryMissingFallback))
    (Leaf.Fallback.Gzip.V2.convert {} {} {} good 2)
  expectError "wrong codec" (.source (.groupFailure 0 (.chunkCodec 1))) (dispatch {} {} {} snappy 2)
  expectError "V1 page refused" (.source (.groupFailure 0
      (.dictionaryPage 0 plainV1Offset (.parameters .unsupportedPage))))
    (dispatch {} {} {} v1 2)
  expectError "PLAIN chunk cap" (.source (.groupFailure 0 .chunkByteLimit))
    (dispatch {dictionary.maxChunkBytes := 0} {} {} plain 2)
  expectError "dictionary chunk cap" (.source (.groupFailure 0 .dictionaryChunkLimit))
    (dispatch {dictionary.maxChunkBytes := 0} {} {} good 2)
  expectError "dictionary GZIP fuel" (.source (.groupFailure 0
      (.dictionaryPage 0 firstDictionary (.payload .gzipIncomplete))))
    (dispatch {gzipCalls := 0} {} {} good 2)
  expectError "PLAIN GZIP fuel" (.source (.groupFailure 0 (.page 0 (.scalar (.payload .gzipIncomplete)))))
    (dispatch {gzipCalls := 0} {} {} plain 2)
  IO.println "Twenty original group classifications, eighteen typed refusals and eight exact prefixes passed"
