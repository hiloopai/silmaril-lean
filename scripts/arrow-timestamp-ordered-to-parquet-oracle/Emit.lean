module

import Silmaril.Formats.Parquet.Timestamp.FromIpc.Ordered.Defs
meta import Silmaril.Formats.Parquet.Timestamp.FromIpc.Ordered.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp.FromIpc.Ordered

private def load (directory : System.FilePath) (name : String) : IO KBytes := do
  let bytes ← IO.FS.readBinFile (directory / (name ++ ".arrow"))
  return KBytes.ofChunks 1 bytes.size (bytes.data.toList.map UInt8.toNat)

private def require {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def expectError (label : String) (expected : Error) (result : Except Error Bytes) : IO Unit :=
  match result with
  | .error actual =>
    unless actual = expected do
      throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: invalid input was accepted")

private def refuse (directory : System.FilePath) (name : String) (cause : Error) (limits : Limits := {}) :
    IO Unit := do
  expectError name cause (convert {} limits (← load directory name))

private def writerControls : IO Unit := do
  let field : Arrow.TimestampBatch.Binding := ⟨"t", false, ⟨.nanosecond, none⟩⟩
  expectError "wrong column count" (.columnCount 0 1 0)
    (emit {} ⟨[field], [⟨1, []⟩]⟩)
  expectError "misaligned column" (.rowCount 0 0 1 0)
    (emit {} ⟨[field], [⟨1, [[]]⟩]⟩)
  expectError "required null at writer" (.page 0 0 (.requiredNull 0))
    (emit {} ⟨[field], [⟨1, [[none]]⟩]⟩)

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "expected fixture directory")
  let directory : System.FilePath := folder
  for name in ["native_ordered", "native_reordered", "native_schema_only"] do
    let wire ← require (convert {} {} (← load directory name))
    IO.FS.writeBinFile (directory / (name ++ ".parquet")) wire.data
  refuse directory "native_seconds" (.annotation 0 .seconds)
  refuse directory "native_named_timezone" (.source (.timezone 1 (some "Europe/Berlin")))
  refuse directory "native_required_null" (.source (.batch 0 (.values (.malformed .validityBitmap))))
  refuse directory "native_duplicate" (.duplicateName 1 "utc_ms")
  refuse directory "native_empty_name" (.invalidName 0 "")
  refuse directory "native_nul_name" (.invalidName 0 "a\x00b")
  refuse directory "native_zero_width" .emptySchema
  refuse directory "native_other_type" (.source (.fieldType 1 (.primitive .int32)))
  refuse directory "mutated_seconds_trailing" (.source (.batch 1 .trailingBytes))
    {writer.maxFileBytes := 0}
  refuse directory "mutated_late_trailing" (.source (.batch 4 .trailingBytes))
    {maxFields := 0, writer.maxFileBytes := 0}
  refuse directory "native_ordered" (.fieldLimit 2 3) {maxFields := 2}
  refuse directory "native_ordered" .groupLimit {writer.maxGroups := 1}
  refuse directory "native_ordered" .fileLimit {writer.maxFileBytes := 0}
  refuse directory "native_ordered" .inputByteLimit {writer.maxInputBytes := 0}
  writerControls
  IO.println "Verified three Lean Parquet files and 17 typed refusals including original IPC error precedence"
