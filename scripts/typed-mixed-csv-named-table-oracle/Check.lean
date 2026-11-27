module

import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.NamedTable.Defs
import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc.Defs
meta import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.NamedTable.Defs
meta import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc.Defs

open Silmaril Silmaril.Formats Silmaril.Relational
open Silmaril.Formats.Csv.Typed.Utf8
open Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc
open Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.NamedTable

private def initial : MixedIpc.NamedTable.Database String :=
  fun name => if name == "keep" then some ⟨Rows.schema [], []⟩ else none

private def expectError {α ε : Type} [DecidableEq ε] (label : String)
    (result : Except ε α) (expected : ε) : IO Unit := do
  let .error cause := result | throw (IO.userError s!"{label}: unexpected success")
  unless cause == expected do
    throw (IO.userError s!"{label}: wrong typed error")

private def observe (table : Rows.Table) : List Arrow.MixedFlat.Field × List (List (Option Cell)) :=
  (MixedIpc.ToIpc.fields table.schema, table.rows.map fun row => List.ofFn row)

private def checkRefusals (db : MixedIpc.NamedTable.Database String) (csv : MixedIpc.Output) : IO Unit := do
  let fields := MixedIpc.ToIpc.fields csv.schema
  let reordered := Rows.schema fields.reverse
  let required := Rows.schema (fields.modify 0 fun field => { field with nullable := false })
  let otherKind := Rows.schema (fields.modify 0 fun field => { field with kind := .primitive .utf8 })
  expectError "missing export name" (exportCsv db "missing" csv.schema {}) .missingName
  expectError "export field order" (exportCsv db "source" reordered {}) .schemaMismatch
  expectError "export nullability before row cap" (exportCsv db "source" required ⟨0, 0⟩) .schemaMismatch
  expectError "export logical kind" (exportCsv db "source" otherKind {}) .schemaMismatch
  expectError "export row cap" (exportCsv db "source" csv.schema { maxRows := 3 }) (.encodeError (.rowLimit 3))
  expectError "import field order" (importCsv db "copy" reordered csv.schema {} csv.wire) .schemaMismatch
  expectError "import nullability" (importCsv db "copy" required csv.schema {} csv.wire) .schemaMismatch
  expectError "import logical kind" (importCsv db "copy" otherKind csv.schema {} csv.wire) .schemaMismatch
  expectError "occupied before malformed wire" (importCsv db "source" csv.schema csv.schema {} [255]) .nameConflict
  expectError "malformed wire before descriptor mismatch" (importCsv db "copy" reordered csv.schema {} [255])
    (.openError (.csv .malformedWire))
  expectError "import row cap" (importCsv db "copy" csv.schema csv.schema { maxRows := 3 } csv.wire)
    (.openError (.rowLimit 3))

private def check (directory : System.FilePath) (name : String) (rowCount : Nat) : IO Unit := do
  let input ← IO.FS.readBinFile (directory / "producer" / (name ++ ".arrows"))
  let input := KBytes.ofChunks 1 input.size (input.data.toList.map UInt8.toNat)
  let .ok csv := MixedIpc.convert {} { maxRows := rowCount + 1 } input
    | throw (IO.userError s!"{name}: source IPC conversion failed")
  let csvLimits : MixedIpc.Limits := ⟨csv.wire.length, rowCount⟩
  let .ok inserted := importCsv initial "source" csv.schema csv.schema csvLimits csv.wire
    | throw (IO.userError s!"{name}: named import failed")
  if name == "mixed" then checkRefusals inserted csv
  let .ok exported := exportCsv inserted "source" csv.schema csvLimits
    | throw (IO.userError s!"{name}: named export failed")
  let .ok copied := importCsv inserted "copy" csv.schema exported.schema csvLimits exported.wire
    | throw (IO.userError s!"{name}: named copy failed")
  let some original := Rows.readRows {} input | throw (IO.userError "source IPC observation failed")
  let some source := Scan.observePacked copied "source" | throw (IO.userError "source entry disappeared")
  let some copy := Scan.observePacked copied "copy" | throw (IO.userError "copy entry missing")
  let some keep := Scan.observePacked copied "keep" | throw (IO.userError "unrelated entry disappeared")

  let ipc : Arrow.MixedFlat.Limits := { observation := {
    ipc := { fields := csv.schema.width, rows := rowCount, batches := 1 },
    totalRows := rowCount, totalCells := rowCount * csv.schema.width } }
  let .ok emitted := MixedIpc.ToIpc.convert csvLimits ipc exported.schema exported.wire
    | throw (IO.userError s!"{name}: IPC output failed")
  let some reopened := Rows.readRows ipc emitted | throw (IO.userError "output IPC observation failed")
  let some events := readEvents ipc emitted | throw (IO.userError "output IPC exhaustion failed")
  unless observe source == observe original && observe copy == observe original &&
      observe keep == ([], []) && observe reopened == observe original &&
      events.batches.map Prod.fst == [rowCount] do
    throw (IO.userError s!"{name}: changed descriptor, rows, unrelated entry, or batch count")
  IO.FS.writeBinFile (directory / (name ++ ".csv")) ⟨exported.wire.toArray⟩
  IO.FS.writeBinFile (directory / (name ++ ".arrows")) emitted.toByteArray

public def main (args : List String) : IO Unit := do
  let [root] := args | throw (IO.userError "expected fixture directory")
  let directory := System.FilePath.mk root
  check directory "mixed" 4
  check directory "schema-only" 0
  check directory "zero-width" 2
  IO.println "Three exact named copies through IPC and eleven typed refusal controls passed."
