module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Uncompressed.V2.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Uncompressed.V2.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Numeric.Timestamp (Ticks)

private abbrev strict := Leaf.Uncompressed.V2.convert
private abbrev IpcError := Leaf.Events.ToIpc.Error

private def input (directory : System.FilePath) (name : String) : IO Bytes :=
  (IO.FS.readBinFile (directory / (name ++ ".parquet"))).map fun raw => ⟨raw⟩

private def require {α ε : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def expectError (label : String) (index : Nat) (cause : Leaf.Error)
    (result : Except IpcError KBytes) : IO Unit :=
  match result with
  | .error actual =>
    let expected : IpcError := .source (.groupFailure index cause)
    unless actual == expected do
      throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: unexpected IPC output")

private def observations (directory : System.FilePath) (name : String) : IO (List (List (Option Int))) := do
  let text ← IO.FS.readFile (directory / (name ++ ".txt"))
  (text.splitOn "\n").mapM fun line => (line.splitOn ",").mapM fun word =>
    if word == "null" then pure none
    else match word.toInt? with
      | some count => pure (some count)
      | none => throw (IO.userError s!"invalid independent count {word}")

private def checkSuccess (directory : System.FilePath) (name : String) : IO Unit := do
  let wire ← input directory name
  let expected ← observations directory name
  let bound ← require (Leaf.Events.ToIpc.openBound {} wire 2)
  unless bound.snapshot.groupCount == expected.length do
    throw (IO.userError s!"{name}: original footer group count differed")
  for (counts, index) in expected.zipIdx do
    let strictSlots ← require (Leaf.Uncompressed.V2.readGroup {} bound index)
    unless strictSlots.map (Option.map Ticks.ticks) == counts do
      throw (IO.userError s!"{name} group {index}: original signed nullable slots differed")
  let wire ← require (strict {} {} wire 2)
  IO.FS.writeBinFile (directory / (name ++ ".arrows")) wire.toByteArray

private def checkLate (directory : System.FilePath) (label : String) (index : Nat)
    (earlier : List (List (Option Int))) (cause : Leaf.Error) : IO Unit := do
  let wire ← input directory label
  let bound ← require (Leaf.Events.ToIpc.openBound {} wire 2)
  let ⟨schema, trace⟩ ← require (Leaf.Uncompressed.V2.readBound {} bound)
  if present : 0 < schema.width then
    let batches := Leaf.Events.ToIpc.batchesAt trace ⟨0, present⟩
    unless batches.map Arrow.TimestampBatch.Writer.tickCounts == earlier.take index do
      throw (IO.userError s!"{label}: incorrect complete earlier batches")
  else throw (IO.userError "missing selected TIMESTAMP field")
  match trace.termination with
  | .readError actual =>
    unless actual == .groupFailure index cause do
      throw (IO.userError s!"{label}: unexpected indexed cause {repr actual}")
  | _ => throw (IO.userError s!"{label}: expected an indexed source failure")
  expectError label index cause (strict {} {ipc.batches := 0} wire 2)

private def crc (ordinal offset declared computed : Nat) : Leaf.Error :=
  .pageChecksum ordinal offset (.mismatch declared.toUInt32 computed.toUInt32)

private def checkFlag (directory : System.FilePath) (label : String) (expected : Bool) : IO Unit := do
  let bound ← require (Leaf.Events.ToIpc.openBound {} (← input directory label) 2)
  let group ← require (Leaf.Uncompressed.V2.checkGroup {} bound 2)
  let some frame := group.frames.getLast? | throw (IO.userError s!"{label}: missing V2 page")
  let .dataV2 info := frame.value.kind | throw (IO.userError s!"{label}: incorrect page version")
  unless info.isCompressed == expected do
    throw (IO.userError s!"{label}: incorrect resolved storage flag")

public def main (args : List String) : IO Unit := do
  let folder :: evidence := args | throw (IO.userError "expected a fixture folder and original offsets")
  let [some levelOffset, some levelDeclared, some levelComputed, some suffixOffset, some suffixDeclared,
       some suffixComputed, some first, some firstSize, some rows] := evidence.map String.toNat? |
    throw (IO.userError "invalid independent frame observations")
  let directory : System.FilePath := folder
  for name in ["native_utc", "native_local", "mutated_true_flag", "mutated_absent_flag"] do
    checkSuccess directory name

  checkFlag directory "native_utc" false
  checkFlag directory "mutated_true_flag" true
  checkFlag directory "mutated_absent_flag" true
  let originalIPC ← IO.FS.readBinFile (directory / "native_utc.arrows")
  for label in ["mutated_true_flag", "mutated_absent_flag"] do
    unless (← IO.FS.readBinFile (directory / (label ++ ".arrows"))) == originalIPC do
      throw (IO.userError s!"{label}: flag mutation changed the literal IPC values")

  let utc ← observations directory "native_utc"
  let localCounts ← observations directory "native_local"
  checkLate directory "mutated_level_crc" 2 utc (crc 0 levelOffset levelDeclared levelComputed)
  checkLate directory "mutated_suffix_crc" 2 utc (crc 1 suffixOffset suffixDeclared suffixComputed)
  checkLate directory "mutated_declared_size" 2 utc (.framing (.header .invalidV2Lengths))
  checkLate directory "mutated_true_size" 2 utc (.page 1 (.scalar (.payload .outputSizeMismatch)))
  checkLate directory "mutated_page_encoding" 2 utc (.page 1 (.scalar (.unsupportedEncoding 5)))
  checkLate directory "mutated_row_count" 2 utc (.rowCount rows (rows + 1))
  checkLate directory "assembled_late_v1" 2 localCounts (.page 0 .unsupportedPage)

  let good ← input directory "native_utc"
  let settings : Leaf.Events.ToIpc.Limits := {}
  expectError "dictionary profile has separate admission" 0 .chunkEncoding
    (strict {} {} (← input directory "dictionary") 2)
  expectError "codec 1 stays outside codec 0" 0 (.chunkCodec 1)
    (strict {leaf.allowSnappy := true} {} (← input directory "wrong_codec") 2)
  expectError "stored frame cap" 0 (.pageChecksum 0 first .byteLimit)
    (strict {settings with leaf.page.compressedBytes := firstSize - 1} {} good 2)
  expectError "original default CRC policy" 0 (.crcUnsupported 0)
    (Leaf.Events.ToIpc.convert {} {} good 2)
  let _ ← require (Leaf.Events.ToIpc.convert {} {} (← input directory "assembled_late_v1") 2)
  let prior ← require (Leaf.Events.ToIpc.convert {} {} (← input directory "native_local") 2)
  unless prior.toByteArray == (← IO.FS.readBinFile (directory / "native_local.arrows")) do
    throw (IO.userError "checksum-free strict V2 and previous IPC differed")
  IO.println "Twelve checked groups, eleven typed refusals and seven complete prefixes passed"
