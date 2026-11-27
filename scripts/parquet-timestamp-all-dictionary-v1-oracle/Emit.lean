module

import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.AllCodecs
open Silmaril.Numeric.Timestamp (Ticks)

private def input (directory : System.FilePath) (name : String) : IO Bytes :=
  (IO.FS.readBinFile (directory / (name ++ ".parquet"))).map fun raw => ⟨raw⟩

private def require {α ε : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def observations (directory : System.FilePath) (name : String) :
    IO (List (String × List (Option Int))) := do
  let text ← IO.FS.readFile (directory / (name ++ ".txt"))
  (text.splitOn "\n").mapM fun line => do
    let mode :: slots := line.splitOn "," | throw (IO.userError "missing mode")
    let ticks ← slots.mapM fun word =>
      if word == "null" then pure none
      else match word.toInt? with
        | some tick => pure (some tick)
        | none => throw (IO.userError s!"invalid tick {word}")
    return (mode, ticks)

private def checkSuccess (directory : System.FilePath) (name : String) : IO Unit := do
  let wire ← input directory name
  let expected ← observations directory name
  let bound ← require (Leaf.Events.ToIpc.openBound {} wire 2)
  unless bound.snapshot.groupCount == expected.length do
    throw (IO.userError s!"{name}: original group count differed")
  let mut allExisting := true
  for ((mode, counts), index) in expected.zipIdx do
    let slots ← require (readGroup {} {} bound index)
    unless slots.map (Option.map Ticks.ticks) == counts do
      throw (IO.userError s!"{name} group {index}: original nullable signed ticks differed")
    match mode.splitOn "_" with
    | [codecName, "1", layout] =>
      if codecName == "none" || codecName == "zstd" then
        allExisting := false
        let codec := if codecName == "none" then Codec.uncompressed else Codec.zstd
        let chosen ← require (Leaf.ScalarAndDictionary.route bound index)
        let framed ← require (frameGroup codec {} {} bound index)
        let profile ← require (Leaf.ScalarAndDictionary.WithV1.classifyFrames framed)
        unless chosen == codec.branch && profile == ⟨.v1, layout == "fallback"⟩ do
          throw (IO.userError s!"{name} group {index}: wrong original V1 branch")
      else
        let previous ← require (Leaf.ScalarAndDictionary.WithV1.readGroup {} {} bound index)
        unless previous.map (Option.map Ticks.ticks) == counts do
          throw (IO.userError s!"{name} group {index}: original V1 branch changed")
    | _ =>
      let previous ← require (Leaf.ScalarAndDictionary.WithV1.readGroup {} {} bound index)
      unless previous.map (Option.map Ticks.ticks) == counts do
        throw (IO.userError s!"{name} group {index}: original scalar or V2 branch changed")
  let output ← require (convert {} {} {} wire 2)
  if allExisting then
    let previous ← require (Leaf.ScalarAndDictionary.WithV1.convert {} {} {} wire 2)
    unless previous.toByteArray == output.toByteArray do
      throw (IO.userError s!"{name}: predecessor IPC changed")
  IO.FS.writeBinFile (directory / (name ++ ".arrows")) output.toByteArray

private def checkLate (directory : System.FilePath) (name : String) (index : Nat)
    (expected : List (String × List (Option Int))) (cause : GroupError)
    (limits : Leaf.ScalarAndDictionary.Limits := {}) : IO Unit := do
  let wire ← input directory name
  let bound ← require (Leaf.Events.ToIpc.openBound {} wire 2)
  if let .existing (.existing previous) := cause then
    match Leaf.ScalarAndDictionary.WithV1.readGroup limits {} bound index with
    | .error actual =>
      unless actual == .existing previous do
        throw (IO.userError s!"{name}: predecessor cause {repr actual}")
    | .ok _ => throw (IO.userError s!"{name}: predecessor admitted the faulty group")
  let events := trace limits {} bound
  let batches := events.batches.map fun batch =>
    Arrow.TimestampBatch.Writer.tickCounts (binding := Leaf.Events.ToIpc.selectedBinding bound)
      (batch.values ⟨0, Nat.zero_lt_one⟩)
  unless batches == (expected.take index).map Prod.snd do
    throw (IO.userError s!"{name}: complete earlier batches differed")
  match events.termination with
  | .readError actual =>
    unless actual == .groupFailure index cause do
      throw (IO.userError s!"{name}: actual {repr actual}, expected {repr cause} at {index}")
  | _ => throw (IO.userError s!"{name}: expected a source failure")
  match convert limits {} {ipc.batches := 0} wire 2 with
  | .error actual =>
    unless actual == .source (.groupFailure index cause) do
      throw (IO.userError s!"{name}: source error did not precede writer limit, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{name}: unexpected IPC output")

private def crc (declared actual : Nat) : Parquet.Page.Checksum.Error :=
  .mismatch declared.toUInt32 actual.toUInt32

public def main (args : List String) : IO Unit := do
  let folder :: evidence := args | throw (IO.userError "expected fixture folder and original offsets")
  let [some rawOffset, some rawDeclared, some rawActual, some zstdOffset, some zstdDeclared, some zstdActual,
       some dictOffset, some dictDeclared, some dictActual, some tagOffset, some mixedOffset, some expandedCap,
       some rawDictOffset, some rawCap] :=
    evidence.map String.toNat? | throw (IO.userError "invalid independent Thrift offsets")
  let directory : System.FilePath := folder
  for codec in ["none", "zstd"] do
    for mode in ["references", "fallback"] do
      checkSuccess directory s!"native_{codec}_{mode}"
  for name in ["native_local_zstd_fallback", "native_none_v2", "native_zstd_v2", "native_snappy_v1",
               "native_gzip_v1", "native_scalar", "assembled_mixed"] do
    checkSuccess directory name

  let expected ← observations directory "assembled_mixed"
  let literal := GroupError.v1 .uncompressed (.checksum 2 rawOffset (crc rawDeclared rawActual))
  let compressed := GroupError.v1 .zstd (.checksum 2 zstdOffset (crc zstdDeclared zstdActual))
  checkLate directory "mutated_late_literal_crc" 7 expected literal
  checkLate directory "mutated_late_zstd_crc" 8 expected compressed
  checkLate directory "mutated_late_zstd_dictionary_crc" 8 expected
    (.v1 .zstd (.checksum 0 dictOffset (crc dictDeclared dictActual)))
  checkLate directory "mutated_competing_crc" 7 expected literal
  checkLate directory "mutated_actual_tag_2" 7 expected
    (.v1 .uncompressed (.selection (.dictionaryPage 1 tagOffset (.encoding 2))))
  checkLate directory "assembled_mixed_versions" 6 expected (.existing (.mixedVersions 2 mixedOffset))
  checkLate directory "assembled_mixed" 8 expected (.v1 .zstd .expandedChunkLimit)
    {dictionary.threeCodec.twoCodec.zstd.maxExpandedChunkBytes := expandedCap}
  checkLate directory "assembled_mixed" 1 expected
    (.existing (.existing (.uncompressedDictionary .dictionaryChunkLimit)))
    {dictionary.uncompressed.maxChunkBytes := 0}
  checkLate directory "assembled_mixed" 4 expected
    (.v1 .uncompressed (.selection (.dictionaryPage 0 rawDictOffset (.payload .outputLimit))))
    {dictionary.uncompressed.maxDictionaryBytes := rawCap}
  IO.println "24 checked groups, 5 byte-identical predecessor comparisons, 9 typed refusals and 9 complete prefixes passed"
