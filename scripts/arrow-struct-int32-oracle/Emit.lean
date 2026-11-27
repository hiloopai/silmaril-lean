module

import Silmaril.Formats.Arrow.StructInt32.Stream.Writer.Defs
meta import Silmaril.Formats.Arrow.StructInt32.Stream.Writer.Defs

open Silmaril Silmaril.Formats
open Arrow.StructInt32 (Field)
open Arrow.StructInt32.Stream
open Arrow.StructInt32.Stream.Writer (emit)

private def mixed : Field := ⟨"点", ⟨"signed", false⟩, ⟨"北", true⟩⟩
private def repeated : Field := ⟨"pair", ⟨"same", true⟩, ⟨"same", true⟩⟩

private def mixedRows : List (List Row) :=
  [[none, some (some (-2147483648), none), some (some 7, some 0), none, some (some 0, some 2147483647)],
    [], [some (some 2147483647, some (-2147483648)), some (some 5, none)]]

private def repeatedRows : List (List Row) :=
  [[some (none, none), none, some (none, some (-1)), some (some 2, none), some (some (-3), some 4)], []]

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

private def emitCase (dir : System.FilePath) (name : String) (field : Field) (rows : List (List Row)) : IO Unit := do
  let wire ← load dir name
  let observed ← require (Arrow.StructInt32.Stream.read {} wire)
  unless observed.field = field ∧ observed.batches.map Batch.rows = rows do
    throw (IO.userError s!"{name}: schema or original rows differed")
  let emitted ← require (emit {} field rows)
  IO.FS.writeBinFile (dir / (name ++ ".lean.arrow")) emitted.toByteArray

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "expected fixture folder")
  let dir : System.FilePath := folder
  emitCase dir "mixed" mixed mixedRows
  emitCase dir "repeated" repeated repeatedRows
  emitCase dir "schema_only" mixed []
  let refuse := fun name cause => do
    let wire ← load dir name
    expect name cause (Arrow.StructInt32.Stream.read {} wire)
  refuse "required_parent" (.schemaMetadata (.unsupported .nested))
  refuse "wrong_integer" (.schemaMetadata (.unsupported .fieldInteger))
  refuse "one_child" (.schemaMetadata (.unsupported .nested))
  refuse "flat" (.schemaMetadata (.unsupported (.fieldType 2)))
  refuse "required_visible" (.batch 0 (.requiredChild 0 0))
  refuse "compressed" (.batch 0 (.metadata (.unsupported .compression)))
  refuse "edited_trailing" (.batch 3 .trailingBytes)
  refuse "edited_missing_eos" (.batch 3 (.envelope (.malformed .truncated)))
  refuse "edited_late_child_length" (.batch 2 .layout)
  refuse "edited_body_extent" (.batch 0 .layout)
  refuse "edited_parent_bitmap" (.batch 0 .parentValidity)
  refuse "edited_child_null_count" (.batch 0 (.child 0 (.malformed .validityBitmap)))
  let wire ← load dir "mixed"
  expect "three-node schema cap" (.schemaMetadata (.limit .fields))
    (Arrow.StructInt32.Stream.read {ipc.fields := 2} wire)
  expect "empty batch still consumes fuel" (.batch 1 .batchLimit)
    (Arrow.StructInt32.Stream.read {ipc.batches := 1} wire)
  expect "late total row cap" (.batch 2 (.budget (.limit .totalRows)))
    (Arrow.StructInt32.Stream.read {totalRows := 5} wire)
  expect "total cell cap" (.batch 0 (.budget (.limit .totalCells)))
    (Arrow.StructInt32.Stream.read {totalCells := 14} wire)
  expect "late required writer refusal" (.record 1 (.requiredChild 0 0))
    (emit {} mixed [[none], [some (none, some 5)]])
  expect "writer stream cell cap" (.ipc (.limit .totalCells))
    (emit {totalCells := 20} mixed mixedRows)
  expect "writer body cap" (.record 0 (.ipc (.limit .bodyBytes)))
    (emit {ipc.bodyBytes := 0} mixed mixedRows)
  IO.println "Verified three native reads, three Lean streams, and 19 typed refusals"
