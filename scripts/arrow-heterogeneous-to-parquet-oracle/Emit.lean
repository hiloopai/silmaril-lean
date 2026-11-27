module

import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp.Defs
meta import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp
open Arrow.MixedFlat.Timestamp (Stream Field)

private def load (directory : System.FilePath) (name : String) : IO KBytes := do
  let raw ← IO.FS.readBinFile (directory / (name ++ ".arrow"))
  return KBytes.ofChunks 1 raw.size (raw.data.toList.map UInt8.toNat)

private def require {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def expect {α : Type} (label : String) (cause : Error) (result : Except Error α) : IO Unit :=
  match result with
  | .error actual =>
    unless actual = cause do
      throw (IO.userError s!"{label}: expected {repr cause}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: invalid input was accepted")

private def emitCase (dir : System.FilePath) (name : String) (rows : List Nat) : IO Unit := do
  let wire ← load dir name
  let original ← require (Arrow.MixedFlat.Timestamp.read {} wire)
  let output ← require (convert {} {} wire)
  let ⟨_, trace⟩ ← require (Parquet.FlatProjection.Events.readAll {} output (ordinals original))
  unless trace.termination = .eos &&
      decide (Parquet.FlatProjection.Events.ToIpc.observation trace = original) &&
      trace.batches.map (·.rowCount) == rows do
    throw (IO.userError s!"{name}: projected observation or group counts differed")
  IO.FS.writeBinFile (dir / (name ++ ".parquet")) output.data

private def standalone : IO Unit := do
  let code : Field := ⟨"code", false, .int32⟩
  let label : Field := ⟨"label", false, .utf8⟩
  let ticks : Field := ⟨"ticks", false, .timestamp ⟨.nanosecond, none⟩⟩
  expect "required integer" (.requiredNull 0 0)
    (emit {} ⟨[code, label], [⟨1, [.int32 [none], .utf8 [some ""]]⟩]⟩)
  expect "required string" (.requiredNull 0 1)
    (emit {} ⟨[code, label], [⟨1, [.int32 [some 0], .utf8 [none]]⟩]⟩)
  expect "required timestamp" (.requiredNull 0 1)
    (emit {} ⟨[code, ticks], [⟨1, [.int32 [some 0], .timestamp [none]]⟩]⟩)
  expect "column type" (.columnType 0 1)
    (emit {} ⟨[code, label], [⟨1, [.int32 [some 0], .timestamp [some 0]]⟩]⟩)
  expect "batch width" (.columnCount 0 2 1)
    (emit {} ⟨[code, label], [⟨1, [.int32 [some 0]]⟩]⟩)
  expect "column row count" (.rowCount 0 1 1 0)
    (emit {} ⟨[code, label], [⟨1, [.int32 [some 0], .utf8 []]⟩]⟩)

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "expected fixture folder")
  let dir : System.FilePath := folder
  emitCase dir "native_mixed" [5, 0, 3]
  emitCase dir "native_reordered" [3, 0]
  emitCase dir "native_schema_only" []
  let refuse := fun name cause => do
    let input ← load dir name
    expect name cause (convert {} {} input)
  refuse "native_zero_width" .emptySchema
  refuse "native_seconds" (.annotation 1 .seconds)
  refuse "native_duplicate" (.duplicateName 1 "label")
  refuse "native_empty_name" (.invalidName 0 "")
  refuse "native_nul_name" (.invalidName 0 ("a" ++ String.singleton (Char.ofNat 0) ++ "b"))
  refuse "native_required_null" (.source (.batch 0 (.layout (.plan (.field 1 .invalidNode)))))
  refuse "native_named_timezone" (.source (.timezone 1 (some "Europe/Berlin")))
  let bad ← load dir "mutated_late_trailing"
  let seconds ← load dir "mutated_seconds_trailing"
  let blocked : Limits := {readback.primitive.maxFields := 0, readback.primitive.column.maxFileBytes := 0}
  expect "late source failure before writer caps" (.source (.batch 3 .trailingBytes)) (convert {} blocked bad)
  expect "late source failure before unsupported unit" (.source (.batch 1 .trailingBytes)) (convert {} {} seconds)
  expect "input byte cap" .inputByteLimit (convert {} {maxInputBytes := 0} bad)
  let clean ← load dir "native_mixed"
  expect "file cap" .fileLimit (convert {} {readback.primitive.column.maxFileBytes := 0} clean)
  expect "footer cap" (.footer .byteLimit)
    (convert {} {readback.primitive.column.snapshot.footer.maxFooterBytes := 0} clean)
  expect "group cap" .groupLimit (convert {} {readback.maxGroups := 0} clean)
  expect "field cap" (.fieldLimit 1 6) (convert {} {readback.primitive.maxFields := 1} clean)
  standalone
  IO.println "Verified three mixed Parquet files and 20 typed refusals"
