module

import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc.Defs
meta import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Csv.Typed.Utf8
open Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc

private def declared : Rows.Schema := Rows.schema [
  ⟨"téxt", true, .view .utf8⟩,
  ⟨"amount", true, .primitive .int32⟩,
  ⟨"téxt", true, .primitive .utf8⟩,
  ⟨"required", false, .primitive .int32⟩
]

private def loadCsv (directory : System.FilePath) (name : String) : IO Csv.Bytes :=
  (IO.FS.readBinFile (directory / (name ++ ".csv"))).map (·.data.toList)

private def cells (table : Rows.Table) : List (List (Option Cell)) :=
  table.rows.map fun row => List.ofFn row

private def check
    (directory : System.FilePath) (name : String) (schema : Rows.Schema) (rowCount : Nat) : IO Unit := do
  let input ← loadCsv directory name
  let csv : MixedIpc.Limits := ⟨input.length, rowCount⟩
  let ipc : Arrow.MixedFlat.Limits := { observation := {
    ipc := { fields := schema.width, rows := rowCount, batches := 1 },
    totalRows := rowCount, totalCells := rowCount * schema.width } }
  let .ok source := MixedIpc.decode csv schema input
    | throw (IO.userError s!"{name}: checked CSV input failed")
  let wire ← match MixedIpc.ToIpc.convert csv ipc schema input with
    | .ok wire => pure wire
    | .error cause => throw (IO.userError s!"{name}: conversion failed: {repr cause}")
  let some events := readEvents ipc wire | throw (IO.userError s!"{name}: IPC events failed")
  let some reopened := Rows.readRows ipc wire | throw (IO.userError s!"{name}: IPC table failed")
  unless events.fields == MixedIpc.ToIpc.fields schema && events.batches.map Prod.fst == [rowCount] &&
      MixedIpc.ToIpc.fields reopened.schema == MixedIpc.ToIpc.fields schema &&
      cells source == cells reopened do
    throw (IO.userError s!"{name}: fields, slots or explicit record count changed")
  IO.FS.writeBinFile (directory / (name ++ ".arrows")) wire.toByteArray

private def expectError (label : String) (result : Except MixedIpc.ToIpc.Error KBytes)
    (expected : MixedIpc.ToIpc.Error) : IO Unit := do
  let .error cause := result | throw (IO.userError s!"{label}: unexpected stream")
  unless cause == expected do
    throw (IO.userError s!"{label}: got {repr cause}, expected {repr expected}")

public def main (args : List String) : IO Unit := do
  let [root] := args | throw (IO.userError "expected fixture directory")
  let directory := System.FilePath.mk root
  check directory "mixed" declared 4
  check directory "header-only" declared 0
  check directory "zero-width" (Rows.schema []) 2
  check directory "zero-width-header-only" (Rows.schema []) 0

  let mixed ← loadCsv directory "mixed"
  let headerOnly ← loadCsv directory "header-only"
  let wrong ← loadCsv directory "wrong-header"
  let bad ← loadCsv directory "bad-integer"
  let required ← loadCsv directory "required-null"
  let opaqueField : Arrow.MixedFlat.Field := ⟨"raw", true, .view .binary⟩
  expectError "opaque descriptor" (MixedIpc.ToIpc.convert {} {} (Rows.schema [opaqueField]) mixed)
    (.source (.unsupportedField 0 opaqueField))
  expectError "malformed UTF-8" (MixedIpc.ToIpc.convert {} {} declared [255]) (.source (.csv .malformedWire))
  expectError "wrong header" (MixedIpc.ToIpc.convert {} {} declared wrong) (.source (.csv .headerMismatch))
  expectError "bad integer" (MixedIpc.ToIpc.convert {} {} declared bad) (.source (.csv (.parseCell 1)))
  expectError "required null" (MixedIpc.ToIpc.convert {} {} declared required) (.source (.requiredNull 1 3))
  expectError "source row cap" (MixedIpc.ToIpc.convert { maxRows := 3 } {} declared mixed) (.source (.rowLimit 3))
  let fewerBytes := mixed.length - 1
  expectError "source byte cap" (MixedIpc.ToIpc.convert { maxBytes := fewerBytes } {} declared mixed)
    (.source (.byteLimit fewerBytes mixed.length))
  expectError "writer field cap"
    (MixedIpc.ToIpc.convert {} { observation := { ipc := { fields := 3 } } } declared mixed)
    (.writer (.ipc (.limit .fields)))
  expectError "header-only still emits a batch"
    (MixedIpc.ToIpc.convert {} { observation := { ipc := { batches := 0 } } } declared headerOnly)
    (.writer (.ipc (.limit .batches)))
  IO.println "Four exact single-batch native readbacks and nine typed source/writer refusals checked."
