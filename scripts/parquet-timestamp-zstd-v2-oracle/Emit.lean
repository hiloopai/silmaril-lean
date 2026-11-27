module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.V2.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.V2.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.V2.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.V2.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc

private abbrev convertZstd := Leaf.Zstd.V2.convert

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

private def readCounts (directory : System.FilePath) (name : String) : IO (List (List (Option Int))) := do
  let text ← IO.FS.readFile (directory / (name ++ ".txt"))
  (text.splitOn "\n").mapM fun line =>
    (line.splitOn ",").mapM fun slot =>
      if slot == "null" then pure none
      else match slot.toInt? with
        | some count => pure (some count)
        | none => throw (IO.userError s!"invalid independent tick {slot}")

private def groupFailure (index : Nat) (cause : Leaf.Zstd.V2.GroupError) : Leaf.Zstd.V2.Error :=
  .source (.groupFailure index cause)

private def checkLate (directory : System.FilePath) (label : String)
    (expected : List (List (Option Int))) (index : Nat) (cause : Leaf.Zstd.V2.GroupError) : IO Unit := do
  let wire ← input directory label
  let bound ← require (openBound {} wire 2)
  let ⟨schema, trace⟩ ← require (Leaf.Zstd.V2.readBound {} {} bound)
  if positive : 0 < schema.width then
    let column : Fin schema.width := ⟨0, positive⟩
    let batches := trace.batches.map fun batch =>
      Arrow.TimestampBatch.Writer.tickCounts (binding := bindingAt schema column) (batch.values column)
    unless batches == expected.take index do
      throw (IO.userError s!"{label}: lost an earlier complete batch")
  else throw (IO.userError "expected selected TIMESTAMP field")
  match trace.termination with
  | .readError actual =>
    unless actual == .groupFailure index cause do
      throw (IO.userError s!"{label}: unexpected source error {repr actual}")
  | _ => throw (IO.userError s!"{label}: expected indexed source error")
  expectError label (groupFailure index cause) (convertZstd {} {} {ipc.batches := 0} wire 2)

public def main (args : List String) : IO Unit := do
  let folder :: evidence := args | throw (IO.userError "expected fixture directory and original frame observations")
  let [some crcOffset, some declared, some computed, some firstOffset, some firstDeclared, some firstComputed,
       some malformedOffset, some rawOffset, some v1Offset, some stored, some expanded] := evidence.map String.toNat? |
    throw (IO.userError "invalid independent frame observations")
  let directory : System.FilePath := folder
  for name in ["utc_nanos", "local_micros", "raw_local_millis"] do
    let limits : Leaf.Zstd.V2.Limits :=
      if name == "raw_local_millis" then {compression := ⟨0, 0⟩} else {}
    let output ← require (convertZstd limits {} {} (← input directory name) 2)
    IO.FS.writeBinFile (directory / (name ++ ".arrows")) output.toByteArray

  let expected ← readCounts directory "utc_nanos"
  let lateCRC := Leaf.Zstd.V2.GroupError.checksum 2 crcOffset (.mismatch declared.toUInt32 computed.toUInt32)
  let wrongMagic := Leaf.Zstd.V2.GroupError.decode 2 malformedOffset (.frame (.frame .badMagic))
  let invalidExtent := Leaf.Zstd.V2.GroupError.selection (.framing (.header .invalidV2Lengths))
  checkLate directory "mutated_late_crc" expected 1 lateCRC
  checkLate directory "mutated_late_magic" expected 1 wrongMagic
  checkLate directory "mutated_two_groups" expected 1 wrongMagic
  checkLate directory "mutated_raw_flag_true" expected 1 (.decode 0 rawOffset (.frame (.frame .badMagic)))
  checkLate directory "mutated_frame_flag_false" expected 1 invalidExtent
  checkLate directory "mutated_level_extent" expected 1 invalidExtent
  checkLate directory "mutated_null_count" expected 1
    (.decode 2 malformedOffset (.scalar (.levels .presentCountMismatch)))

  let good ← input directory "utc_nanos"
  let earlyDamage ← input directory "mutated_early_crc"
  let inputLimits : Leaf.Events.ToIpc.Limits := {}
  let firstError := groupFailure 0 (.checksum 0 firstOffset (.mismatch firstDeclared.toUInt32 firstComputed.toUInt32))
  expectError "default stays strict" (.source (.groupFailure 0 (.chunkCodec 6))) (convert {} {} good 2)
  expectError "GZIP stays strict" (.source (.groupFailure 0 (.chunkCodec 6)))
    (Leaf.Gzip.V2.convert {} {} {} good 2)
  expectError "non-Zstd codec" (groupFailure 0 (.selection (.chunkCodec 1)))
    (convertZstd {} {} {} (← input directory "snappy_v2") 2)
  expectError "V1 data refused" (groupFailure 0 (.expectedV2 0 v1Offset))
    (convertZstd {} {} {} (← input directory "v1") 2)
  expectError "dictionary refused" (groupFailure 0 (.selection .chunkEncoding))
    (convertZstd {} {} {} (← input directory "dictionary_v2") 2)
  expectError "stored chunk cap" (groupFailure 0 (.selection .chunkByteLimit))
    (convertZstd {maxStoredChunkBytes := 0} {} {} good 2)
  expectError "expanded chunk cap" (groupFailure 0 .expandedChunkLimit)
    (convertZstd {maxExpandedChunkBytes := 0} {} {} good 2)
  expectError "stored page cap precedes CRC" (groupFailure 0 (.checksum 0 firstOffset .byteLimit))
    (convertZstd {} {inputLimits with leaf.page.compressedBytes := stored - 1} {} earlyDamage 2)
  expectError "CRC precedes expanded page cap" firstError
    (convertZstd {} {inputLimits with leaf.page.uncompressedBytes := expanded - 1} {} earlyDamage 2)
  expectError "expanded page cap" (groupFailure 0 (.decode 0 firstOffset (.scalar (.payload .outputLimit))))
    (convertZstd {} {inputLimits with leaf.page.uncompressedBytes := expanded - 1} {} good 2)
  expectError "Zstd window cap" (groupFailure 0 (.decode 0 firstOffset (.frame (.frame .windowLimit))))
    (convertZstd {compression := ⟨0, 43690⟩} {} {} good 2)
  expectError "file row cap" (.openFailure (.rowLimit 1023 1024))
    (convertZstd {} {inputLimits with maxTotalRows := 1023} {} good 2)
  IO.println "Nineteen typed refusals and seven exact earlier-group prefixes passed"
