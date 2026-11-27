module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Existence.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Existence.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp

private abbrev convert := Leaf.Events.ToIpc.Seconds.convert
private abbrev ConversionError := Leaf.Events.ToIpc.Seconds.Error

private def require {α ε : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def input (path : System.FilePath) : IO KBytes := do
  let raw ← IO.FS.readBinFile path
  return KBytes.ofChunks 1 raw.size (raw.data.toList.map UInt8.toNat)

private def expectError (expected : ConversionError) (actual : Except ConversionError KBytes) : IO Unit :=
  match actual with
  | .ok _ => throw (IO.userError "independently insufficient cap unexpectedly admitted")
  | .error cause => unless cause == expected do
      throw (IO.userError s!"expected {repr expected}, got {repr cause}")

private def probe (directory : System.FilePath) (name : String) : IO Unit := do
  let source ← input (directory / (name ++ ".input.arrows"))
  let original ← require (Arrow.TimestampStream.read {} source)
  let native ← require (Arrow.TimestampStream.Writer.Internal.serialize {} original.binding original.batches)
  IO.FS.writeBinFile (directory / (name ++ ".probe.arrows")) native.toByteArray

private def exercise (directory : System.FilePath) (name : String) : IO Unit := do
  let caps ← IO.FS.readFile (directory / (name ++ ".caps"))
  let some [batches, rows, body, metadata, total, firstRows, firstBody, metadataFrame] :=
    (caps.splitOn " ").mapM String.toNat? | throw (IO.userError "invalid independent IPC measurements")
  let outputLimits : Arrow.ObservationLimits :=
    { ipc := { fields := 1, batches := batches, rows := rows, bodyBytes := body, metadataBytes := metadata }
      totalRows := total
      totalCells := total }
  let source ← input (directory / (name ++ ".input.arrows"))
  let original ← require (Arrow.TimestampStream.read {} source)
  let native ← require (Arrow.TimestampStream.Writer.Internal.serialize outputLimits original.binding original.batches)
  let checked ← require (Arrow.TimestampStream.read outputLimits.ipc native)
  unless Arrow.TimestampStream.Writer.descriptor checked.binding =
        Arrow.TimestampStream.Writer.descriptor original.binding ∧
      checked.batches.map Arrow.TimestampBatch.Writer.tickCounts =
        original.batches.map Arrow.TimestampBatch.Writer.tickCounts do
    throw (IO.userError "independent sink readback differs from source")
  let middle ← require (FromIpc.Seconds.convert {} {} source)
  let readLimits : Leaf.Events.ToIpc.Limits :=
    { maxFileBytes := middle.length, maxGroups := batches, maxTotalRows := total }
  let output ← require (convert readLimits outputLimits middle)
  unless output.toByteArray.data == native.toByteArray.data do
    throw (IO.userError "inverse bytes differ from the independently admitted sink")
  IO.FS.writeBinFile (directory / (name ++ ".parquet")) middle.data
  IO.FS.writeBinFile (directory / (name ++ ".result.arrows")) output.toByteArray

  let writeRejected (reason : Arrow.Resource) : ConversionError := .writer (.writer (.limit reason))
  let recordRejected (index : Nat) (reason : Arrow.Resource) : ConversionError := .writer (.record index (.writer (.limit reason)))
  expectError (writeRejected .fields) (convert readLimits {outputLimits with ipc.fields := 0} middle)
  let metadataRejected := if metadataFrame = 0 then writeRejected .metadataBytes
    else recordRejected (metadataFrame - 1) .metadataBytes
  expectError metadataRejected (convert readLimits {outputLimits with ipc.metadataBytes := metadata - 1} middle)
  if batches > 0 then
    expectError (writeRejected .batches) (convert readLimits {outputLimits with ipc.batches := batches - 1} middle)
  if rows > 0 then
    expectError (recordRejected firstRows .rows) (convert readLimits {outputLimits with ipc.rows := rows - 1} middle)
  if body > 0 then
    expectError (recordRejected firstBody .bodyBytes)
      (convert readLimits {outputLimits with ipc.bodyBytes := body - 1} middle)
  if total > 0 then
    expectError (writeRejected .totalRows) (convert readLimits {outputLimits with totalRows := total - 1} middle)
    expectError (writeRejected .totalCells) (convert readLimits {outputLimits with totalCells := total - 1} middle)

public def main (args : List String) : IO Unit := do
  let [command, folder] := args | throw (IO.userError "expected probe or exercise and fixture directory")
  let directory : System.FilePath := folder
  for name in ["utc_optional", "local_required", "all_empty", "schema_only"] do
    if command == "probe" then probe directory name
    else if command == "exercise" then exercise directory name
    else throw (IO.userError "unknown command")
