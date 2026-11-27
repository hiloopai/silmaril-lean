module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Delta.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Delta.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Numeric.Timestamp (Ticks)

private abbrev convert := Leaf.Delta.convert
private abbrev packed := Leaf.Delta.defaultLimits
private abbrev IpcError := Leaf.Events.ToIpc.Error

private def input (directory : System.FilePath) (name : String) : IO Bytes :=
  (IO.FS.readBinFile (directory / (name ++ ".parquet"))).map fun raw => ⟨raw⟩

private def require {α ε : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def expectError (label : String) (expected : IpcError) (result : Except IpcError KBytes) : IO Unit :=
  match result with
  | .error actual =>
    unless actual == expected do
      throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: unexpected IPC output")

private def observations (directory : System.FilePath) (name : String) : IO (List (List (Option Int))) := do
  let text ← IO.FS.readFile (directory / (name ++ ".txt"))
  (text.splitOn "\n").mapM fun line => (line.splitOn ",").mapM fun word =>
    if word == "null" then pure none
    else match word.toInt? with
      | some tick => pure (some tick)
      | none => throw (IO.userError s!"invalid independent tick {word}")

private def checkSuccess (directory : System.FilePath) (name : String) : IO Unit := do
  let wire ← input directory name
  let expected ← observations directory name
  let bound ← require (Leaf.Events.ToIpc.openBound {} wire 2)
  unless bound.snapshot.groupCount == expected.length do
    throw (IO.userError s!"{name}: original footer group count differed")
  for (counts, index) in expected.zipIdx do
    let slots ← require (Leaf.Delta.readGroup packed {} bound index)
    unless slots.map (Option.map Ticks.ticks) == counts do
      throw (IO.userError s!"{name} group {index}: original signed nullable ticks differed")
  let output ← require (convert packed {} {} wire 2)
  IO.FS.writeBinFile (directory / (name ++ ".arrows")) output.toByteArray

private def checkLate (directory : System.FilePath) (name : String)
    (earlier : List (List (Option Int))) (cause : Leaf.Error) : IO Unit := do
  let wire ← input directory name
  let bound ← require (Leaf.Events.ToIpc.openBound {} wire 2)
  let ⟨schema, trace⟩ ← require (Leaf.Delta.readBound packed {} bound)
  if present : 0 < schema.width then
    let batches := Leaf.Events.ToIpc.batchesAt trace ⟨0, present⟩
    unless batches.map Arrow.TimestampBatch.Writer.tickCounts == earlier.take 2 do
      throw (IO.userError s!"{name}: incorrect complete earlier batches")
  else throw (IO.userError "missing selected TIMESTAMP field")
  let original : Leaf.Events.Error := .groupFailure 2 cause
  match trace.termination with
  | .readError actual =>
    unless actual == original do
      throw (IO.userError s!"{name}: expected {repr original}, got {repr actual}")
  | _ => throw (IO.userError s!"{name}: expected an indexed source failure")
  expectError name (.source original) (convert packed {} {ipc.batches := 0} wire 2)

private def crcError (ordinal offset declared computed : Nat) : Leaf.Error :=
  .pageChecksum ordinal offset (.mismatch declared.toUInt32 computed.toUInt32)

public def main (args : List String) : IO Unit := do
  let folder :: evidence := args | throw (IO.userError "expected a fixture folder and original offsets")
  let [some crcV1, some declaredV1, some computedV1, some crcV2, some declaredV2, some computedV2,
       some tagV1, some tagV2, some geometry, some first, some stored, some expanded] :=
    evidence.map String.toNat? | throw (IO.userError "invalid independent frame observations")
  let directory : System.FilePath := folder
  for descriptor in ["utc", "local"] do
    for page in ["v1", "v2"] do
      for codec in ["none", "snappy"] do
        checkSuccess directory s!"native_{descriptor}_{page}_{codec}"
  checkSuccess directory "assembled_versions_codecs"

  let utc ← observations directory "native_utc_v1_snappy"
  let localRows ← observations directory "native_local_v2_none"
  checkLate directory "mutated_v1_crc" utc (crcError 0 crcV1 declaredV1 computedV1)
  checkLate directory "mutated_v2_crc" utc (crcError 1 crcV2 declaredV2 computedV2)
  checkLate directory "mutated_v1_level_encoding" utc
    (.deltaPage 0 tagV1 (.decode (.page .unsupportedLevelEncoding)))
  let wrongTag : Leaf.DeltaPageError := .decode (.unsupportedEncoding (.signed .int64) 0)
  checkLate directory "mutated_v1_tag" utc (.deltaPage 0 tagV1 wrongTag)
  checkLate directory "mutated_v2_tag" utc (.deltaPage 0 tagV2 wrongTag)
  checkLate directory "mutated_delta_geometry" localRows
    (.deltaPage 0 geometry (.decode (.binaryPacked .invalidGeometry)))

  let good ← input directory "native_utc_v2_none"
  let settings : Leaf.Events.ToIpc.Limits := {}
  expectError "require tag 5 in the original footer" (.source (.groupFailure 0 .chunkEncoding))
    (convert packed {} {} (← input directory "native_plain_control") 2)
  expectError "reject original codec 2" (.source (.groupFailure 0 (.chunkCodec 2)))
    (convert packed {} {} (← input directory "native_gzip_control") 2)
  expectError "original PLAIN API still rejects tag 5" (.source (.groupFailure 0 .chunkEncoding))
    (Leaf.Events.ToIpc.convert {} {} good 2)
  expectError "framed page cap" (.source (.groupFailure 0 (.framing .pageLimit)))
    (convert packed {settings with leaf.framing.maxPages := 1} {} good 2)
  expectError "stored page cap" (.source (.groupFailure 0 (.pageChecksum 0 first .byteLimit)))
    (convert packed {settings with leaf.page.compressedBytes := stored - 1} {} good 2)
  expectError "expanded page cap"
    (.source (.groupFailure 0 (.deltaPage 0 first (.decode (.page (.payload .outputLimit))))))
    (convert packed {settings with leaf.page.uncompressedBytes := expanded - 1} {} good 2)
  expectError "packed stream cap"
    (.source (.groupFailure 0 (.deltaPage 0 first (.decode (.binaryPacked .byteLimit)))))
    (convert {packed with bytes := 0} {} {} good 2)
  IO.println "28 selected groups, 13 typed refusals and 6 retained complete prefixes passed"
