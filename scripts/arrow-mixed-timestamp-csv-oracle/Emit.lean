module

import Silmaril.Formats.Csv.Typed.Utf8.MixedTimestamp.Defs
import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp.Defs
meta import Silmaril.Formats.Csv.Typed.Utf8.MixedTimestamp.Defs
meta import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp.Defs

open Silmaril Silmaril.Formats
open Csv.Typed.Utf8.MixedTimestamp

private def fields : List Field :=
  [⟨"local_ns", true, .timestamp ⟨.nanosecond, none⟩⟩, ⟨"説明", true, .utf8⟩,
    ⟨"code", false, .int32⟩, ⟨"utc_ms", false, .timestamp ⟨.millisecond, some "UTC"⟩⟩,
    ⟨"local_us", true, .timestamp ⟨.microsecond, none⟩⟩]

private def csvBytes (text : String) : Csv.Bytes := text.toByteArray.data.toList

private def require {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def expect {ε α : Type} [DecidableEq ε] [Repr ε] (label : String)
    (cause : ε) (result : Except ε α) : IO Unit :=
  match result with
  | .error actual =>
    unless actual = cause do
      throw (IO.userError s!"{label}: expected {repr cause}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: invalid input was accepted")

private def expectNamed {α : Type} (label : String)
    (cause : Relational.NamedTable.ImportError Error)
    (result : Except (Relational.NamedTable.ImportError Error) α) : IO Unit :=
  match result with
  | .error actual => unless actual = cause do throw (IO.userError s!"{label}: wrong named error")
  | .ok _ => throw (IO.userError s!"{label}: invalid named input was accepted")

private def loadIpc (dir : System.FilePath) (name : String) : IO KBytes := do
  let raw ← IO.FS.readBinFile (dir / (name ++ ".arrow"))
  return KBytes.ofChunks 1 raw.size (raw.data.toList.map UInt8.toNat)

private def emitCase (dir : System.FilePath) (name : String) (declaration : List Field)
    (batches : List Nat) : IO Unit := do
  let ipc ← loadIpc dir name
  let importedCsv ← IO.FS.readBinFile (dir / (name ++ ".csv"))
  let original ← require (Arrow.MixedFlat.Timestamp.read {} ipc)
  unless original.fields = declaration ∧ original.batches.map (·.rowCount) = batches do
    throw (IO.userError s!"{name}: source declaration or batch count differed")
  let exported ← require (fromIpc {} {} ipc)
  unless exported.fields = declaration do throw (IO.userError s!"{name}: exported declaration differed")
  IO.FS.writeBinFile (dir / (name ++ ".lean.csv")) ⟨exported.wire.toArray⟩
  let fromCsv ← require (toIpc {} {} declaration importedCsv.data.toList)
  let fromLeanCsv ← require (toIpc {} {} exported.fields exported.wire)
  unless fromCsv.toByteArray = fromLeanCsv.toByteArray do throw (IO.userError s!"{name}: distinct IPC output from equivalent CSV")
  IO.FS.writeBinFile (dir / (name ++ ".lean.arrow")) fromCsv.toByteArray
  if !declaration.isEmpty then
    let parquet ← require (Parquet.MixedV1Writer.FromIpc.WithTimestamp.convert {} {} fromCsv)
    IO.FS.writeBinFile (dir / (name ++ ".lean.parquet")) parquet.data

private def nameCases (dir : System.FilePath) : IO Unit := do
  let db : NamedTable.Database String := fun _ => none
  let input ← IO.FS.readBinFile (dir / "mixed.csv")
  let wire := input.data.toList
  let .ok next := NamedTable.importCsv db "mixed" fields fields {} wire
    | throw (IO.userError "native CSV did not insert")
  let restored ← require (NamedTable.exportCsv next "mixed" fields {})
  let expected ← require (fromIpc {} {} (← loadIpc dir "mixed"))
  unless restored.fields = fields ∧ restored.wire = expected.wire do
    throw (IO.userError "named table returned a different declaration or CSV")
  let timezoneChanged := [⟨"local_ns", true, .timestamp ⟨.nanosecond, some "UTC"⟩⟩] ++ fields.drop 1
  expectNamed "same headers with different timestamp descriptor" .schemaMismatch
    (NamedTable.importCsv db "mixed" timezoneChanged fields {} wire)
  expectNamed "occupied name" .nameConflict (NamedTable.importCsv next "mixed" fields fields {} [])
  expectNamed "invalid CSV before schema mismatch" (.openError (.csv .missingHeader))
    (NamedTable.importCsv db "mixed" timezoneChanged fields {} [])
  expect "named export mismatch" .schemaMismatch (NamedTable.exportCsv next "mixed" timezoneChanged {})
  expect "missing name" .missingName (NamedTable.exportCsv db "missing" fields {})

private def failures (dir : System.FilePath) : IO Unit := do
  let header := "local_ns,説明,code,utc_ms,local_us\r\n"
  let good := "T-1,T,T0,T0,N\r\n"
  let badNull := "N,T,N,T0,N\r\n"
  let broken := "\"unfinished"
  let schema := schemaOf fields
  let refused := fun label suffix cause =>
    expect label cause (decode {} schema (csvBytes (header ++ good ++ suffix)))
  refused "required null before later malformed quote" (badNull ++ broken) (.requiredNull 1 2)
  refused "invalid tag before next record" ("T0,x,N,T0,N\r\n" ++ badNull) (.row 1 (.invalidTag 1))
  refused "typed range before requiredness in same record"
    "T0,T,N,T9223372036854775808,N\r\n" (.row 1 (.parseCell 3))
  refused "signed INT32 range" "N,T,T-2147483649,T0,N\r\n" (.row 1 (.parseCell 2))
  refused "malformed quote" broken (.row 1 .malformedWire)
  refused "wrong width" "T0,T\r\n" (.row 1 (.width 5 2))
  expect "header order" (.csv .headerMismatch) (decode {} schema (csvBytes ("code,説明,local_ns,utc_ms,local_us\r\n" ++ good)))
  expect "row cap before malformed record" (.rowLimit 1)
    (decode {maxRows := 1} schema (csvBytes (header ++ good ++ broken)))
  let csvWire := csvBytes (header ++ good ++ badNull)
  expect "byte cap" (.byteLimit 0 csvWire.length) (decode {maxBytes := 0} schema csvWire)
  expect "CSV failure precedes IPC writer" (.csv (.requiredNull 1 2))
    (toIpc {} {ipc.fields := 0} fields csvWire)
  let late ← loadIpc dir "mutated_late"
  expect "late IPC trailing byte before CSV limits" (.source (.batch 3 .trailingBytes))
    (fromIpc {} {maxBytes := 0, maxRows := 0} late)
  let control ← loadIpc dir "control_byte"
  expect "unsupported output control byte" (.csv (.csv .unrepresentableWire)) (fromIpc {} {} control)
  let badTimezone : List Field := [⟨"x", true, .timestamp ⟨.microsecond, some "Europe/Berlin"⟩⟩]
  expect "explicit timezone refusal" (.timezone 0 (some "Europe/Berlin"))
    (decode {} (schemaOf badTimezone) (csvBytes "x\r\n"))

public def main (args : List String) : IO Unit := do
  let [folder] := args | throw (IO.userError "expected fixture folder")
  let dir : System.FilePath := folder
  emitCase dir "mixed" fields [3, 0, 3]
  emitCase dir "header_only" fields.reverse []
  emitCase dir "zero_width" [] [2, 0, 1]
  nameCases dir
  failures dir
  IO.println "Verified three CSV and IPC pairs, two Parquet outputs and 18 typed refusals"
