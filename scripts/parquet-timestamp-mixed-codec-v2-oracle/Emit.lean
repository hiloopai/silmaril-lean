module

import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc
open Silmaril.Numeric.Timestamp (Ticks)

private abbrev MixedLimits := Leaf.MixedCodec.V2.Limits

private abbrev GroupError := Leaf.MixedCodec.V2.GroupError

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
  | .ok _ => throw (IO.userError s!"{label}: unexpected IPC output")

private def observations (directory : System.FilePath) (name : String) :
    IO (List (Int × List (Option Int))) := do
  let text ← IO.FS.readFile (directory / (name ++ ".txt"))
  (text.splitOn "\n").mapM fun line => do
    let code :: words := line.splitOn "," | throw (IO.userError "missing original codec")
    let some codec := code.toInt? | throw (IO.userError s!"invalid original codec {code}")
    let ticks ← words.mapM fun word =>
      if word == "null" then pure none
      else match word.toInt? with
        | some tick => pure (some tick)
        | none => throw (IO.userError s!"invalid signed tick {word}")
    return (codec, ticks)

private def strictRead (limits : MixedLimits) (codec : Int) (bound : Leaf.Bound) (index : Nat) :
    Except GroupError (Leaf.Slots bound) :=
  match codec with
  | 2 => (Leaf.Gzip.Dispatch.V2.readGroup limits.gzip {} bound index).mapError .gzip
  | 6 => (Leaf.Zstd.Dispatch.V2.readGroup limits.zstd {} bound index).mapError .zstd
  | other => .error (.unsupportedCodec other)

private def readSuccess (directory : System.FilePath) (name : String) : IO Unit := do
  let wire ← input directory name
  let expected ← observations directory name
  let bound ← require (openBound {} wire 2)
  unless bound.snapshot.groupCount == expected.length do
    throw (IO.userError s!"{name}: original footer group count differed")
  for ((codec, counts), index) in expected.zipIdx do
    let selected ← require (Leaf.MixedCodec.V2.selectedCodec bound index)
    let slots ← require (Leaf.MixedCodec.V2.readGroup {} {} bound index)
    let strict ← require (strictRead {} codec bound index)
    unless selected == codec && slots.map (Option.map Ticks.ticks) == counts &&
        strict.map (Option.map Ticks.ticks) == counts do
      throw (IO.userError s!"{name} group {index}: source codec or exact slots differed")
  let emitted ← require (Leaf.MixedCodec.V2.convert {} {} {} wire 2)
  IO.FS.writeBinFile (directory / (name ++ ".arrows")) emitted.toByteArray

private def checkLate (directory : System.FilePath) (label : String) (limits : MixedLimits)
    (earlier : List (Int × List (Option Int))) (index : Nat) (codec : Int) (cause : GroupError) : IO Unit := do
  let wire ← input directory label
  let bound ← require (openBound {} wire 2)
  unless (← require (Leaf.MixedCodec.V2.selectedCodec bound index)) == codec do
    throw (IO.userError s!"{label}: wrong original codec")
  match strictRead limits codec bound index with
  | .error strict =>
    unless strict == cause do throw (IO.userError s!"{label}: strict cause {repr strict}")
  | .ok _ => throw (IO.userError s!"{label}: strict reader admitted the source group")
  let events := Leaf.MixedCodec.V2.trace limits {} bound
  let batches := events.batches.map fun batch =>
    Arrow.TimestampBatch.Writer.tickCounts (binding := selectedBinding bound) (batch.values ⟨0, Nat.zero_lt_one⟩)
  unless batches == (earlier.take index).map Prod.snd do
    throw (IO.userError s!"{label}: first failure lost an earlier complete group")
  match events.termination with
  | .readError actual =>
    unless actual == .groupFailure index cause do
      throw (IO.userError s!"{label}: original indexed cause {repr actual}")
  | _ => throw (IO.userError s!"{label}: expected a source group failure")
  expectError label (Leaf.MixedCodec.V2.Error.source (.groupFailure index cause))
    (Leaf.MixedCodec.V2.convert limits {} {ipc.batches := 0} wire 2)

public def main (args : List String) : IO Unit := do
  let folder :: observationsArgs := args | throw (IO.userError "expected a fixture folder and original offsets")
  let [some gzipOffset, some gzipDeclared, some gzipActual, some zstdOffset, some zstdDeclared, some zstdActual,
       some gzipV1, some zstdV1] := observationsArgs.map String.toNat? |
    throw (IO.userError "bad independent Thrift offsets")
  let directory : System.FilePath := folder
  for label in ["mixed_utc", "mixed_local", "damaged_decoy"] do
    readSuccess directory label

  let utc ← observations directory "mixed_utc"
  let localCounts ← observations directory "mixed_local"
  let gzipCRC : GroupError := .gzip (.dictionaryPage 1 gzipOffset
    (.checksumFailure (.mismatch gzipDeclared.toUInt32 gzipActual.toUInt32)))
  let zstdCRC : GroupError := .zstd (.checksum 0 zstdOffset (.mismatch zstdDeclared.toUInt32 zstdActual.toUInt32))
  checkLate directory "bad_gzip_crc" {} utc 2 2 gzipCRC
  checkLate directory "bad_zstd_crc" {} utc 3 6 zstdCRC
  checkLate directory "competing_crc" {} utc 2 2 gzipCRC
  checkLate directory "late_snappy" {} utc 2 1 (.unsupportedCodec 1)
  checkLate directory "late_gzip_v1" {} utc 2 2 (.gzip (.dictionaryPage 0 gzipV1 (.parameters .unsupportedPage)))
  checkLate directory "late_zstd_v1" {} utc 2 6 (.zstd (.expectedV2 0 zstdV1))
  checkLate directory "mixed_utc" {zstd.dictionary.maxChunkBytes := 0} utc 1 6
    (.zstd (.selection .chunkByteLimit))
  checkLate directory "mixed_local" {gzip.dictionary.maxChunkBytes := 0} localCounts 1 2 (.gzip .chunkByteLimit)

  let originalUTC ← input directory "mixed_utc"
  let originalLocal ← input directory "mixed_local"
  expectError "strict default rejects GZIP" (.source (.groupFailure 0 (.chunkCodec 2)))
    (convert {} {} originalUTC 2)
  expectError "standalone GZIP rejects Zstandard" (.source (.groupFailure 1 (.chunkCodec 6)))
    (Leaf.Gzip.Dispatch.V2.convert {} {} {} originalUTC 2)
  expectError "standalone Zstandard rejects GZIP" (.source (.groupFailure 1 (.selection (.chunkCodec 2))))
    (Leaf.Zstd.Dispatch.V2.convert {} {} {} originalLocal 2)
  IO.println "Eighteen selected group reads, eleven typed refusals and eight exact prefixes passed"
