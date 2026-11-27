module

import Silmaril.Formats.Parquet.Timestamp.Leaf.SnappyV2.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.SnappyV2.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc

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
  let text ← IO.FS.readFile (directory / s!"rows-{index}.txt")
  (text.splitOn "\n").mapM fun line =>
    if line == "null" then pure none
    else match line.toInt? with
      | some count => pure (some count)
      | none => throw (IO.userError s!"invalid independent tick: {line}")

private def checkLate (wire : Bytes) (expected : List (List (Option Int)))
    (cause : Leaf.Error) : IO Unit := do
  let bound ← require (openBound {} wire 1)
  let ⟨schema, trace⟩ ← require (Leaf.SnappyV2.readBound {} bound)
  if one : 0 < schema.width then
    unless (batchesAt trace ⟨0, one⟩).map Arrow.TimestampBatch.Writer.tickCounts == expected do
      throw (IO.userError "late failure lost the independent tick prefix")
  else throw (IO.userError "expected one timestamp field")
  match trace.termination with
  | .readError actual =>
    unless actual == .groupFailure 2 cause do
      throw (IO.userError s!"unexpected late source error: {repr actual}")
  | _ => throw (IO.userError "expected the original indexed source error")
  expectError "source error precedes exhausted writer cap" (.source (.groupFailure 2 cause))
    (Leaf.SnappyV2.convert {} {ipc.batches := 0} wire 1)

private def checkCaps (wire : Bytes) : IO Unit := do
  let limits : Leaf.Events.ToIpc.Limits := {}
  let bound ← require (openBound limits wire 1)
  let group ← require (Leaf.SnappyV2.checkGroup {} bound 0)
  let first :: _ := group.frames | throw (IO.userError "expected first V2 frame")
  expectError "stored page cap" (.source (.groupFailure 0
      (.pageChecksum 0 first.header.start .byteLimit)))
    (Leaf.SnappyV2.convert {limits with leaf.page.compressedBytes := first.value.compressedSize - 1} {} wire 1)
  expectError "expanded page cap" (.source (.groupFailure 0
      (.page 0 (.scalar (.payload .outputLimit)))))
    (Leaf.SnappyV2.convert {limits with leaf.page.uncompressedBytes := first.value.uncompressedSize - 1} {} wire 1)
  expectError "group row cap" (.source (.groupFailure 0 .rowLimit))
    (Leaf.SnappyV2.convert {leaf.maxRows := 31} {} wire 1)
  expectError "file row cap" (.rowLimit 95 96)
    (Leaf.SnappyV2.convert {maxTotalRows := 95} {} wire 1)

private def checksumError (ordinal : Nat) (offset declared actual : String) : IO Leaf.Error := do
  let [some atByte, some expected, some observed] := [offset, declared, actual].map String.toNat? |
    throw (IO.userError "expected independent checksum and header offset")
  return .pageChecksum ordinal atByte (.mismatch expected.toUInt32 observed.toUInt32)

public def main (args : List String) : IO Unit := do
  let [folder, levelOffset, levelDeclared, levelActual, suffixOffset, suffixDeclared, suffixActual] := args |
    throw (IO.userError "usage: Emit.lean DIRECTORY LEVEL_OFFSET LEVEL_CRC LEVEL_ACTUAL SUFFIX_OFFSET SUFFIX_CRC SUFFIX_ACTUAL")
  let directory : System.FilePath := folder
  for name in ["utc_nanos", "local_micros", "required_millis", "checksum_free"] do
    let wire ← input directory name
    let output ← require (Leaf.SnappyV2.convert {} {} wire 1)
    IO.FS.writeBinFile (directory / (name ++ ".arrows")) output.toByteArray
  let valid ← input directory "utc_nanos"
  expectError "strict default codec refusal" (.source (.groupFailure 0 (.chunkCodec 1)))
    (convert {} {} valid 1)
  expectError "original Snappy PLAIN checksum refusal" (.source (.groupFailure 0 (.crcUnsupported 0)))
    (convert {leaf.allowSnappy := true} {} valid 1)
  expectError "V1 refusal" (.source (.groupFailure 0 (.page 0 .unsupportedPage)))
    (Leaf.SnappyV2.convert {} {} (← input directory "v1") 1)
  expectError "wrong codec refusal" (.source (.groupFailure 0 (.chunkCodec 0)))
    (Leaf.SnappyV2.convert {} {} (← input directory "wrong_codec") 1)
  expectError "dictionary chunk refusal" (.source (.groupFailure 0 .chunkEncoding))
    (Leaf.SnappyV2.convert {} {} (← input directory "dictionary") 2)
  checkCaps valid
  let prior ← [0, 1].mapM (readCounts directory)
  checkLate (← input directory "bad_levels") prior
    (← checksumError 0 levelOffset levelDeclared levelActual)
  checkLate (← input directory "bad_suffix") prior
    (← checksumError 1 suffixOffset suffixDeclared suffixActual)
  checkLate (← input directory "bad_size") prior (.page 1 (.scalar (.payload .outputSizeMismatch)))
  IO.println "Twelve typed refusal controls and three exact late prefixes passed"
