module

import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1
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
        | none => throw (IO.userError s!"invalid independent tick {word}")
    return (mode, ticks)

private def parseMode (mode : String) : IO (Codec × Profile) := do
  let [word, page, layout] := mode.splitOn "_" | throw (IO.userError s!"invalid mode {mode}")
  let codec ← match word with
    | "snappy" => pure Codec.snappy
    | "gzip" => pure Codec.gzip
    | _ => throw (IO.userError s!"invalid codec {word}")
  let version ← match page with
    | "1" => pure Version.v1
    | "2" => pure Version.v2
    | _ => throw (IO.userError s!"invalid page version {page}")
  unless layout == "references" || layout == "fallback" do
    throw (IO.userError s!"invalid layout {layout}")
  return (codec, ⟨version, layout == "fallback"⟩)

private def checkSuccess (directory : System.FilePath) (name : String) : IO Unit := do
  let wire ← input directory name
  let expected ← observations directory name
  let bound ← require (Leaf.Events.ToIpc.openBound {} wire 2)
  unless bound.snapshot.groupCount == expected.length do
    throw (IO.userError s!"{name}: original group count differed")
  for ((mode, counts), index) in expected.zipIdx do
    let selected ← require (Leaf.ScalarAndDictionary.route bound index)
    let strict ←
      if mode == "scalar" then
        unless selected == .scalar .snappy do
          throw (IO.userError s!"{name}: wrong scalar route")
        require (Leaf.ScalarDispatch.readGroup {} {} bound index)
      else do
        let (codec, profile) ← parseMode mode
        let framed ← require (frameGroup codec {} {} bound index)
        let actual ← require (classifyFrames framed)
        unless selected == codec.branch && actual == profile do
          throw (IO.userError s!"{name} group {index}: wrong physical dictionary profile {repr actual}")
        require (standalone codec profile {} {} bound index)
    let slots ← require (readGroup {} {} bound index)
    unless slots.map (Option.map Ticks.ticks) == counts && strict.map (Option.map Ticks.ticks) == counts do
      throw (IO.userError s!"{name} group {index}: original or standalone ticks differed")
  let output ← require (convert {} {} {} wire 2)
  if name.endsWith "_v2" || name == "native_scalar" then
    let previous ← require (Leaf.ScalarAndDictionary.convert {} {} {} wire 2)
    unless previous.toByteArray == output.toByteArray do
      throw (IO.userError s!"{name}: predecessor IPC differed")
  else if name.startsWith "native_" then
    let (mode, _) :: _ := expected | throw (IO.userError "missing native mode")
    let (codec, profile) ← parseMode mode
    let standaloneOutput ←
      match codec, profile.fallback with
      | .snappy, false => require (Leaf.Dictionary.Snappy.convert .modernOnly {} {} {} wire 2)
      | .snappy, true => require (Leaf.Fallback.Snappy.convert .modernOnly {} {} {} wire 2)
      | .gzip, false => require (Leaf.Dictionary.Gzip.convert {} {} {} wire 2)
      | .gzip, true => require (Leaf.Fallback.Gzip.convert {} {} {} wire 2)
    unless standaloneOutput.toByteArray == output.toByteArray do
      throw (IO.userError s!"{name}: V1 standalone IPC differed")
  IO.FS.writeBinFile (directory / (name ++ ".arrows")) output.toByteArray

private def checkLate (directory : System.FilePath) (name : String) (index : Nat)
    (expected : List (String × List (Option Int))) (cause : GroupError)
    (limits : Leaf.ScalarAndDictionary.Limits := {}) : IO Unit := do
  let wire ← input directory name
  let bound ← require (Leaf.Events.ToIpc.openBound {} wire 2)
  match cause with
  | .snappyV1 expectedError | .gzipV1 expectedError =>
    let some (mode, _) := expected[index]? | throw (IO.userError "missing strict mode")
    let (codec, profile) ← parseMode mode
    match standalone codec profile limits {} bound index with
    | .error actual =>
      unless actual == expectedError do
        throw (IO.userError s!"{name}: standalone cause {repr actual}")
    | .ok _ => throw (IO.userError s!"{name}: standalone admitted the faulty group")
  | _ => pure ()
  let events := trace limits {} bound
  let batches := events.batches.map fun batch =>
    Arrow.TimestampBatch.Writer.tickCounts (binding := Leaf.Events.ToIpc.selectedBinding bound)
      (batch.values ⟨0, Nat.zero_lt_one⟩)
  unless batches == (expected.take index).map Prod.snd do
    throw (IO.userError s!"{name}: complete earlier batches differed")
  match events.termination with
  | .readError actual =>
    unless actual == .groupFailure index cause do
      throw (IO.userError s!"{name}: original indexed cause {repr actual}, expected {repr cause}")
  | _ => throw (IO.userError s!"{name}: expected a source failure")
  match convert limits {} {ipc.batches := 0} wire 2 with
  | .error actual =>
    unless actual == .source (.groupFailure index cause) do
      throw (IO.userError s!"{name}: source failure did not precede writer limit, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{name}: unexpected IPC output")

private def crc (declared actual : Nat) : Leaf.DictionaryPageError :=
  .checksumFailure (.mismatch declared.toUInt32 actual.toUInt32)

public def main (args : List String) : IO Unit := do
  let folder :: evidence := args | throw (IO.userError "expected fixture folder and original offsets")
  let [some bodyOffset, some bodyDeclared, some bodyActual, some dictOffset, some dictDeclared, some dictActual,
       some mixedOffset] := evidence.map String.toNat? |
    throw (IO.userError "invalid independent Thrift offsets")
  let directory : System.FilePath := folder
  for codec in ["snappy", "gzip"] do
    for mode in ["references", "fallback"] do
      checkSuccess directory s!"native_{codec}_{mode}"
  for name in ["native_local_gzip_fallback", "native_gzip_v2", "native_snappy_v2", "native_scalar",
               "assembled_mixed"] do
    checkSuccess directory name

  let expected ← observations directory "assembled_mixed"
  let bodyCause := GroupError.snappyV1 (.dictionaryPage 2 bodyOffset (crc bodyDeclared bodyActual))
  checkLate directory "mutated_v1_crc" 5 expected bodyCause
  checkLate directory "mutated_competing_crc" 5 expected bodyCause
  checkLate directory "mutated_dictionary_crc" 6 expected
    (.gzipV1 (.dictionaryPage 0 dictOffset (crc dictDeclared dictActual)))
  checkLate directory "mutated_advertised_tag_2" 5 expected
    (.existing (.unsupported (.dictionaryEncodings [0, 2, 3, 8])))
  checkLate directory "assembled_mixed_versions" 5 expected (.mixedVersions 2 mixedOffset)
  checkLate directory "assembled_mixed" 1 expected
    (.existing (.snappyDictionary .dictionaryChunkLimit)) {dictionary.threeCodec.snappy.maxChunkBytes := 0}
  IO.println "22 checked groups, 8 byte-identical native comparisons, 6 typed refusals and 6 complete prefixes passed"
