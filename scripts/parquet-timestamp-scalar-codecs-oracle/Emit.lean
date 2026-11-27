module

import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.V2.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.V2.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.V2.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.V2.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Numeric.Timestamp (Ticks)

private abbrev convert := Leaf.ScalarDispatch.convert
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

private def checkSuccess (directory : System.FilePath) (name : String)
    (compare : Option (Bytes → IO KBytes) := none) : IO Unit := do
  let wire ← input directory name
  let expected ← observations directory name
  let bound ← require (Leaf.Events.ToIpc.openBound {} wire 2)
  unless bound.snapshot.groupCount == expected.length do
    throw (IO.userError s!"{name}: original footer group count differed")
  for (counts, index) in expected.zipIdx do
    let slots ← require (Leaf.ScalarDispatch.readGroup {} {} bound index)
    unless slots.map (Option.map Ticks.ticks) == counts do
      throw (IO.userError s!"{name} group {index}: original signed nullable ticks differed")
  let output ← require (convert {} {} {} wire 2)
  if let some strict := compare then
    let previous ← strict wire
    unless previous.toByteArray == output.toByteArray do
      throw (IO.userError s!"{name}: original homogeneous IPC differed")
  IO.FS.writeBinFile (directory / (name ++ ".arrows")) output.toByteArray

private def checkLate (directory : System.FilePath) (name : String) (index : Nat)
    (earlier : List (List (Option Int))) (cause : Leaf.Error)
    (scalars : Leaf.ScalarDispatch.Limits := {}) : IO Unit := do
  let wire ← input directory name
  let bound ← require (Leaf.Events.ToIpc.openBound {} wire 2)
  let ⟨schema, trace⟩ ← require (Leaf.ScalarDispatch.readBound scalars {} bound)
  if present : 0 < schema.width then
    let batches := Leaf.Events.ToIpc.batchesAt trace ⟨0, present⟩
    unless batches.map Arrow.TimestampBatch.Writer.tickCounts == earlier.take index do
      throw (IO.userError s!"{name}: incorrect complete earlier batches")
  else throw (IO.userError "missing selected TIMESTAMP field")
  let original : Leaf.Events.Error := .groupFailure index cause
  match trace.termination with
  | .readError actual =>
    unless actual == original do
      throw (IO.userError s!"{name}: expected {repr original}, got {repr actual}")
  | _ => throw (IO.userError s!"{name}: expected an indexed source failure")
  expectError name (.source original) (convert scalars {} {ipc.batches := 0} wire 2)

private def crcError (ordinal offset declared computed : Nat) : Leaf.Error :=
  .pageChecksum ordinal offset (.mismatch declared.toUInt32 computed.toUInt32)

public def main (args : List String) : IO Unit := do
  let folder :: evidence := args | throw (IO.userError "expected a fixture folder and original offsets")
  let [some gzip, some declared, some computed, some zstd] :=
    evidence.map String.toNat? | throw (IO.userError "invalid independent frame observations")
  let directory : System.FilePath := folder
  for codec in ["gzip", "zstd"] do
    for page in ["v1", "v2"] do
      for encoding in ["plain", "delta", "split"] do
        let name := s!"native_{codec}_{encoding}_{page}"
        let compare :=
          if encoding == "plain" && page == "v2" then
            if codec == "gzip" then some fun wire => require (Leaf.Gzip.V2.convert {} {} {} wire 2)
            else some fun wire => require (Leaf.Zstd.V2.convert {} {} {} wire 2)
          else none
        checkSuccess directory name compare
  checkSuccess directory "native_local_gzip_split_v1"
  checkSuccess directory "native_local_zstd_plain_v2"
    (some fun wire => require (Leaf.Zstd.V2.convert {} {} {} wire 2))
  checkSuccess directory "assembled_chunk_gzip"
  checkSuccess directory "assembled_chunk_zstd"
  checkSuccess directory "assembled_mixed_codecs"

  let expected ← observations directory "assembled_mixed_codecs"
  checkLate directory "mutated_gzip_outer_crc" 2 expected (crcError 0 gzip declared computed)
  checkLate directory "mutated_gzip_member_crc" 2 expected
    (.scalarDispatchPage 0 gzip (.plain (.scalar (.payload (.malformed .gzip)))))
  checkLate directory "mutated_zstd_magic" 3 expected
    (.scalarDispatchPage 0 zstd (.zstd (.frame (.frame .badMagic))))
  checkLate directory "mutated_zstd_null_count" 3 expected
    (.scalarDispatchPage 0 zstd (.zstd (.scalar (.levels .presentCountMismatch))))
  checkLate directory "assembled_mixed_codecs" 2 expected
    (.scalarDispatchPage 0 gzip (.plain (.scalar (.payload .gzipIncomplete)))) {gzipCalls := 0}
  let settings : Leaf.ScalarDispatch.Limits := {}
  checkLate directory "assembled_mixed_codecs" 3 expected
    (.scalarDispatchPage 0 zstd (.zstd (.frame (.frame .windowLimit))))
    {settings with zstd.window := 0}

  expectError "standalone delta refuses GZIP" (.source (.groupFailure 0 (.chunkCodec 2)))
    (Leaf.Delta.convert Leaf.Delta.defaultLimits {} {} (← input directory "native_gzip_delta_v1") 2)
  expectError "standalone split refuses Zstandard" (.source (.groupFailure 0 (.chunkCodec 6)))
    (Leaf.ByteStreamSplit.convert Leaf.ByteStreamSplit.defaultLimits {} {}
      (← input directory "native_zstd_split_v2") 2)
  IO.println "50 checked groups, 3 byte-identical PLAIN comparisons, 8 typed refusals and 6 complete prefixes passed"
