module

import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary
open Silmaril.Numeric.Timestamp (Ticks)

private def input (directory : System.FilePath) (name : String) : IO Bytes :=
  (IO.FS.readBinFile (directory / (name ++ ".parquet"))).map fun raw => ⟨raw⟩

private def require {α ε : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private abbrev IpcError := Leaf.ScalarAndDictionary.Error

private def expectError (label : String) (expected : IpcError) (result : Except IpcError KBytes) : IO Unit :=
  match result with
  | .error actual =>
    unless actual == expected do
      throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: unexpected IPC output")

private def parseBranch (word : String) : IO Branch := do
  let [profile, codec] := word.splitOn "_" | throw (IO.userError s!"invalid route {word}")
  let codec : Codec ← match codec with
    | "none" => pure .uncompressed
    | "snappy" => pure .snappy
    | "gzip" => pure .gzip
    | "zstd" => pure .zstd
    | _ => throw (IO.userError s!"invalid codec {codec}")
  match profile with
  | "scalar" => pure (.scalar codec)
  | "dictionary" => pure (.dictionary codec)
  | _ => throw (IO.userError s!"invalid route {word}")

private def observations (directory : System.FilePath) (name : String) :
    IO (List (Branch × List (Option Int))) := do
  let text ← IO.FS.readFile (directory / (name ++ ".txt"))
  (text.splitOn "\n").mapM fun line => do
    let kind :: slots := line.splitOn "," | throw (IO.userError "missing route")
    let branch ← parseBranch kind
    let ticks ← slots.mapM fun word =>
      if word == "null" then pure none
      else match word.toInt? with
        | some tick => pure (some tick)
        | none => throw (IO.userError s!"invalid independent tick {word}")
    return (branch, ticks)

private def strictGroup (limits : Limits) (bound : Leaf.Bound) (index : Nat) :
    Branch → Except GroupError (Leaf.Slots bound)
  | .scalar _ =>
    (Leaf.ScalarDispatch.readGroup limits.scalar {} bound index).mapError .scalar
  | .dictionary .uncompressed =>
    (Leaf.Uncompressed.Dispatch.V2.readGroup limits.dictionary.uncompressed {} bound index).mapError
      .uncompressedDictionary
  | .dictionary .snappy =>
    (Leaf.Snappy.Dispatch.V2.readGroup limits.dictionary.threeCodec.snappy {} bound index).mapError
      .snappyDictionary
  | .dictionary .gzip =>
    (Leaf.Gzip.Dispatch.V2.readGroup limits.dictionary.threeCodec.twoCodec.gzip {} bound index).mapError
      .gzipDictionary
  | .dictionary .zstd =>
    (Leaf.Zstd.Dispatch.V2.readGroup limits.dictionary.threeCodec.twoCodec.zstd {} bound index).mapError
      .zstdDictionary

private def checkSuccess (directory : System.FilePath) (name : String) : IO Unit := do
  let wire ← input directory name
  let expected ← observations directory name
  let bound ← require (Leaf.Events.ToIpc.openBound {} wire 2)
  unless bound.snapshot.groupCount == expected.length do
    throw (IO.userError s!"{name}: original group count differed")
  for ((branch, counts), index) in expected.zipIdx do
    let selected ← require (route bound index)
    let slots ← require (readGroup {} {} bound index)
    let strict ← require (strictGroup {} bound index branch)
    unless selected == branch && slots.map (Option.map Ticks.ticks) == counts &&
        strict.map (Option.map Ticks.ticks) == counts do
      throw (IO.userError s!"{name} group {index}: original branch or nullable signed ticks differed")
  let output ← require (convert {} {} {} wire 2)
  if name.startsWith "native_" then
    let previous ←
      if name.startsWith "native_scalar_" then require (Leaf.ScalarDispatch.convert {} {} {} wire 2)
      else require (Leaf.MixedCodec.V2.WithUncompressed.convert {} {} {} wire 2)
    unless previous.toByteArray == output.toByteArray do
      throw (IO.userError s!"{name}: standalone IPC differed")
  IO.FS.writeBinFile (directory / (name ++ ".arrows")) output.toByteArray

private def checkLate (directory : System.FilePath) (name : String) (index : Nat)
    (expected : List (Branch × List (Option Int))) (branch : Option Branch) (cause : GroupError)
    (limits : Limits := {}) : IO Unit := do
  let wire ← input directory name
  let bound ← require (Leaf.Events.ToIpc.openBound {} wire 2)
  match branch, route bound index with
  | none, .error actual =>
    unless actual == cause do
      throw (IO.userError s!"{name}: unsupported profile did not fail at routing")
  | some chosen, .ok selected =>
    unless selected == chosen do
      throw (IO.userError s!"{name}: wrong original branch")
    match strictGroup limits bound index chosen with
    | .ok _ => throw (IO.userError s!"{name}: standalone reader admitted the faulty group")
    | .error actual =>
      unless actual == cause do
        throw (IO.userError s!"{name}: standalone cause {repr actual}, expected {repr cause}")
  | _, result => throw (IO.userError s!"{name}: unexpected route {repr result}")
  let events := trace limits {} bound
  let batches := events.batches.map fun batch =>
    Arrow.TimestampBatch.Writer.tickCounts (binding := Leaf.Events.ToIpc.selectedBinding bound)
      (batch.values ⟨0, Nat.zero_lt_one⟩)
  unless batches == (expected.take index).map Prod.snd do
    throw (IO.userError s!"{name}: complete earlier batches differed")
  match events.termination with
  | .readError actual =>
    unless actual == .groupFailure index cause do
      throw (IO.userError s!"{name}: original indexed cause {repr actual}")
  | _ => throw (IO.userError s!"{name}: expected a source failure")
  expectError name (.source (.groupFailure index cause)) (convert limits {} {ipc.batches := 0} wire 2)

private def crc (declared actual : Nat) : Parquet.Page.Checksum.Error :=
  .mismatch declared.toUInt32 actual.toUInt32

public def main (args : List String) : IO Unit := do
  let folder :: evidence := args | throw (IO.userError "expected fixture folder and original offsets")
  let [some zstdOffset, some zstdDeclared, some zstdActual, some gzipOffset, some gzipDeclared, some gzipActual,
       some unexpectedTag, some v1Offset] := evidence.map String.toNat? |
    throw (IO.userError "invalid independent Thrift offsets")
  let directory : System.FilePath := folder
  for codec in ["none", "snappy", "gzip", "zstd"] do
    for mode in ["references", "fallback"] do
      checkSuccess directory s!"native_{codec}_{mode}"
  for name in ["native_local_snappy_references", "native_scalar_delta", "native_scalar_split",
               "native_scalar_plain", "assembled_mixed"] do
    checkSuccess directory name

  let expected ← observations directory "assembled_mixed"
  let zstdCause := GroupError.zstdDictionary (.checksum 0 zstdOffset (crc zstdDeclared zstdActual))
  checkLate directory "mutated_late_zstd_crc" 7 expected (.some (.dictionary .zstd)) zstdCause
  checkLate directory "mutated_competing_crc" 7 expected (.some (.dictionary .zstd)) zstdCause
  checkLate directory "mutated_late_gzip_crc" 8 expected (.some (.dictionary .gzip))
    (.gzipDictionary (.dictionaryPage 1 gzipOffset (.checksumFailure (crc gzipDeclared gzipActual))))
  checkLate directory "mutated_unsupported_codec" 5 expected none (.unsupported (.codec 7))
  checkLate directory "mutated_dictionary_encodings" 5 expected none
    (.unsupported (.dictionaryEncodings [0, 3, 8, 5, 9]))
  checkLate directory "mutated_dictionary_data_tag" 3 expected (.some (.dictionary .snappy))
    (.snappyDictionary (.dictionaryPage 1 unexpectedTag (.encoding 9)))
  checkLate directory "assembled_late_dictionary_v1" 5 expected (.some (.dictionary .snappy))
    (.snappyDictionary (.dictionaryPage 1 v1Offset (.parameters .unsupportedPage)))
  checkLate directory "assembled_mixed" 1 expected (.some (.dictionary .uncompressed))
    (.uncompressedDictionary .dictionaryChunkLimit) {dictionary.uncompressed.maxChunkBytes := 0}
  IO.println "32 checked groups, 12 byte-identical standalone comparisons, 8 typed refusals and 8 complete prefixes passed"
