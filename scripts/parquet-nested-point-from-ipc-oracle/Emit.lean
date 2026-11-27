module

import Silmaril.Formats.Parquet.NestedPoint.Multi.Writer.FromIpc.Defs
meta import Silmaril.Formats.Parquet.NestedPoint.Multi.Writer.FromIpc.Defs

open Silmaril Silmaril.Formats
open Parquet.NestedPoint.Multi.Writer.FromIpc
open Parquet.NestedPoint.Multi.Writer (Encoded GroupPlan)

private def load (folder : System.FilePath) (name : String) : IO KBytes := do
  let raw ← IO.FS.readBinFile (folder / (name ++ ".arrow"))
  return KBytes.ofChunks 1 raw.size (raw.data.toList.map UInt8.toNat)

private def require {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def expect (label : String) (cause : Error) (result : Except Error Encoded) : IO Unit :=
  match result with
  | .error actual =>
    unless actual = cause do throw (IO.userError s!"{label}: expected {repr cause}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: invalid input was accepted")

private def emitCase (folder : System.FilePath) (name : String) (counts : List Nat) : IO Unit := do
  let input ← load folder name
  let original ← require (Arrow.StructInt32.Stream.readFor .int64 {} input)
  let emitted ← require (convert {} input)
  unless emitted.groups.map GroupPlan.rowCount = counts do
    throw (IO.userError s!"{name}: output group plan counts differed")
  let carrier ← require (Parquet.NestedPoint.Multi.ToIpc.convert {} emitted.bytes).wire
  let restored ← require (Arrow.StructInt32.Stream.readFor .int64 {} carrier)
  unless restored.field = original.field ∧
      restored.batches.map (·.rows) = original.batches.map (·.rows) ∧
      restored.batches.map (·.rows.length) = counts do
    throw (IO.userError s!"{name}: exact native observations differed")
  IO.FS.writeBinFile (folder / (name ++ ".parquet")) emitted.bytes.data
  IO.FS.writeBinFile (folder / (name ++ ".returned.arrow")) carrier.toByteArray

public def main (args : List String) : IO Unit := do
  let [dir] := args | throw (IO.userError "expected fixture folder")
  let folder : System.FilePath := dir
  emitCase folder "native" [5, 0, 0, 2]
  emitCase folder "schema_only" []
  emitCase folder "framed_empty" [0]
  let refuse := fun name cause => do
    expect name cause (convert {} (← load folder name))
  refuse "left_nullable" (.requiredness 0 true)
  refuse "right_required" (.requiredness 1 false)
  refuse "duplicate" (.writer (.duplicateChild "wide"))
  refuse "empty_name" (.writer (.name 0 ""))
  refuse "narrow" (.source (.schemaMetadata (.unsupported .fieldInteger)))
  refuse "required_null" (.source (.batch 0 (.requiredChild 0 0)))
  let blocked : Limits := {parquet.maxGroups := 0, parquet.maxFileBytes := 0}
  expect "late source before output caps" (.source (.batch 4 .trailingBytes))
    (convert blocked (← load folder "edited_late"))
  expect "late source before unsupported field flag" (.source (.batch 1 .trailingBytes))
    (convert blocked (← load folder "edited_right_required"))
  let valid ← load folder "native"
  expect "output group cap" (.writer .groupLimit) (convert blocked valid)
  expect "output row cap" (.writer .totalRows) (convert {parquet.maxTotalRows := 0} valid)
  expect "output body cap" (.writer (.measure 0 0 .budget))
    (convert {parquet.readback.group.leaf.presence.maxBodyBytes := 0} valid)
  expect "output footer cap" (.writer (.footer .byteLimit))
    (convert {parquet.readback.snapshot.footer.maxFooterBytes := 0} valid)
  expect "output file cap" (.writer .fileLimit) (convert {parquet.maxFileBytes := 0} valid)
  IO.println "Verified three native NestedPoint files, three native round trips, and 13 typed refusals"
