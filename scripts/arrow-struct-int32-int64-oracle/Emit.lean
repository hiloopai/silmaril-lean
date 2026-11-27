module

import Silmaril.Formats.Arrow.StructInt32.Stream.Writer.Defs
meta import Silmaril.Formats.Arrow.StructInt32.Stream.Writer.Defs

open Silmaril Silmaril.Formats
open Arrow.StructInt32 (Field)
open Arrow.StructInt32.Stream
open Arrow.StructInt32.Stream.Writer (emitFor)

private def nestedPoint : Field := ⟨"point", ⟨"signed", false⟩, ⟨"wide", true⟩⟩
private def requiredWide : Field := ⟨"点", ⟨"同", true⟩, ⟨"同", false⟩⟩

private def pointRows : List (List (RowFor Int64)) :=
  [[none, some (some (-2147483648), some (-9223372036854775808)), some (some 0, none),
    none, some (some 2147483647, some 9223372036854775807)], [],
    [some (some (-1), some 4398046511104), some (some 7, some (-4398046511105))]]

private def requiredRows : List (List (RowFor Int64)) :=
  [[none, some (none, some 2147483648), some (some (-17), some (-2147483649)), none], []]

private def load (dir : System.FilePath) (name : String) : IO KBytes := do
  let raw ← IO.FS.readBinFile (dir / (name ++ ".arrow"))
  return KBytes.ofChunks 1 raw.size (raw.data.toList.map UInt8.toNat)

private def require {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def expect {ε α : Type} [DecidableEq ε] [Repr ε] (label : String)
    (cause : ε) (result : Except ε α) : IO Unit :=
  match result with
  | .error actual =>
    unless cause = actual do throw (IO.userError s!"{label}: expected {repr cause}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: invalid input was accepted")

private def emitCase (dir : System.FilePath) (name : String) (field : Field)
    (rows : List (List (RowFor Int64))) : IO Unit := do
  let wire ← load dir name
  let observed ← require (readFor .int64 {} wire)
  unless observed.field = field ∧ observed.batches.map Batch.rows = rows do
    throw (IO.userError s!"{name}: schema or original signed rows differed")
  let emitted ← require (emitFor .int64 {} field rows)
  IO.FS.writeBinFile (dir / (name ++ ".lean.arrow")) emitted.toByteArray

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "expected fixture folder")
  let dir : System.FilePath := folder
  emitCase dir "nested_point_shape" nestedPoint pointRows
  emitCase dir "required_wide" requiredWide requiredRows
  emitCase dir "schema_only" nestedPoint []
  let refuse := fun name cause => do
    let wire ← load dir name
    expect name cause (readFor .int64 {} wire)
  refuse "unsigned" (.schemaMetadata (.unsupported .fieldInteger))
  refuse "float" (.schemaMetadata (.unsupported (.fieldType 3)))
  refuse "timestamp" (.schemaMetadata (.unsupported (.fieldType 10)))
  refuse "swapped" (.schemaMetadata (.unsupported .fieldInteger))
  refuse "required_visible" (.batch 0 (.requiredChild 1 0))
  refuse "edited_short_wide" (.batch 0 (.child 1 (.malformed .bodyValues)))
  refuse "edited_wide_null_count" (.batch 0 (.child 1 (.malformed .validityBitmap)))
  refuse "edited_trailing" (.batch 3 .trailingBytes)
  let wide ← load dir "nested_point_shape"
  expect "original reader keeps Int64 excluded" (.schemaMetadata (.unsupported .fieldInteger))
    (Arrow.StructInt32.Stream.read {} wide)
  refuse "legacy/mixed" (.schemaMetadata (.unsupported .fieldInteger))
  expect "empty batch consumes fuel" (.batch 1 .batchLimit)
    (readFor .int64 {ipc.batches := 1} wide)
  expect "writer accounts for eight-byte child extent" (.record 0 (.ipc (.limit .bodyBytes)))
    (emitFor .int64 {ipc.bodyBytes := 80} nestedPoint pointRows)
  expect "writer required wide column" (.record 1 (.requiredChild 1 0))
    (emitFor .int64 {} requiredWide [[], [some (none, none)]])
  IO.println "Verified three signed INT32/INT64 streams and 13 typed refusals"
