module

import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Uncompressed.V2.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.SnappyV2.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Uncompressed.V2.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.SnappyV2.Defs

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
    (compare : Option (Bytes → Except IpcError KBytes) := none) : IO Unit := do
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
    let previous ← require (strict wire)
    unless previous.toByteArray == output.toByteArray do
      throw (IO.userError s!"{name}: original homogeneous IPC differed")
  IO.FS.writeBinFile (directory / (name ++ ".arrows")) output.toByteArray

private def checkLate (directory : System.FilePath) (name : String)
    (earlier : List (List (Option Int))) (cause : Leaf.Error)
    (scalars : Leaf.ScalarDispatch.Limits := {}) : IO Unit := do
  let wire ← input directory name
  let bound ← require (Leaf.Events.ToIpc.openBound {} wire 2)
  let ⟨schema, trace⟩ ← require (Leaf.ScalarDispatch.readBound scalars {} bound)
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
  expectError name (.source original) (convert scalars {} {ipc.batches := 0} wire 2)

private def crcError (ordinal offset declared computed : Nat) : Leaf.Error :=
  .pageChecksum ordinal offset (.mismatch declared.toUInt32 computed.toUInt32)

public def main (args : List String) : IO Unit := do
  let folder :: evidence := args | throw (IO.userError "expected a fixture folder and original offsets")
  let [some crc, some declared, some computed, some split] :=
    evidence.map String.toNat? | throw (IO.userError "invalid independent frame observations")
  let directory : System.FilePath := folder
  for page in ["v1", "v2"] do
    for codec in ["none", "snappy"] do
      let plain :=
        if page == "v1" then fun wire => Leaf.Events.ToIpc.convert {leaf.allowSnappy := true} {} wire 2
        else if codec == "none" then fun wire => Leaf.Uncompressed.V2.convert {} {} wire 2
        else fun wire => Leaf.SnappyV2.convert {} {} wire 2
      checkSuccess directory s!"native_plain_{page}_{codec}" (some plain)
      checkSuccess directory s!"native_delta_{page}_{codec}"
        (some fun wire => Leaf.Delta.convert Leaf.Delta.defaultLimits {} {} wire 2)
      checkSuccess directory s!"native_split_{page}_{codec}"
        (some fun wire => Leaf.ByteStreamSplit.convert Leaf.ByteStreamSplit.defaultLimits {} {} wire 2)
  for name in ["assembled_chunk_none", "assembled_chunk_snappy", "assembled_groups"] do
    checkSuccess directory name
  let expected ← observations directory "assembled_groups"
  checkLate directory "mutated_late_crc" expected (crcError 1 crc declared computed)
  checkLate directory "mutated_undeclared_split" expected
    (.scalarDispatchPage 2 split (.undeclaredEncoding 9))
  checkLate directory "mutated_unsupported_tag" expected
    (.scalarDispatchPage 2 split (.unsupportedEncoding 7))
  checkLate directory "mutated_footer_tag" expected .chunkEncoding
  checkLate directory "assembled_groups" expected
    (.byteStreamSplitPage 2 split (.decode (.scalar .byteLimit)))
    {split := {Leaf.ByteStreamSplit.defaultLimits with bytes := 0}}
  expectError "unsupported codec" (.source (.groupFailure 0 (.chunkCodec 4)))
    (convert {} {} {} (← input directory "native_unsupported_codec") 2)
  expectError "dictionary profile" (.source (.groupFailure 0 .chunkEncoding))
    (convert {} {} {} (← input directory "native_dictionary") 2)

  let mixed ← input directory "assembled_chunk_none"
  let encodingError : IpcError := .source (.groupFailure 0 .chunkEncoding)
  expectError "standalone PLAIN admission" encodingError (Leaf.Events.ToIpc.convert {} {} mixed 2)
  expectError "standalone delta admission" encodingError
    (Leaf.Delta.convert Leaf.Delta.defaultLimits {} {} mixed 2)
  expectError "standalone split admission" encodingError
    (Leaf.ByteStreamSplit.convert Leaf.ByteStreamSplit.defaultLimits {} {} mixed 2)
  IO.println "42 original groups, 12 byte-identical homogeneous outputs, 10 typed refusals and 5 complete prefixes passed"
