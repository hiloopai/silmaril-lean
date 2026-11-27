module

import Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Rows.Defs
import Lean.Data.Json
meta import Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Rows.Defs
meta import Lean.Data.Json

open Lean Silmaril Silmaril.Relational Silmaril.Formats
open Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc

private def readWire (directory : System.FilePath) (name : String) : IO KBytes := do
  let wire ← IO.FS.readBinFile (directory / (name ++ ".arrows"))
  return KBytes.ofChunks 1 wire.size (wire.data.toList.map UInt8.toNat)

private def fieldJson (field : Arrow.MixedFlat.Field) : Json :=
  let kind := match field.kind with
    | .primitive .int32 => "int32"
    | .view .binary => "binary_view"
    | _ => "outside-fixture"
  Json.arr #[toJson field.name, toJson field.nullable, toJson kind]

private def cellJson : Option Cell → Json
  | none => .null
  | some (.primitive (.int32 signed)) => toJson signed.toInt
  | some (.binaryView octets) => toJson (octets.map UInt8.toNat)
  | some _ => .str "outside-fixture"

private def tableJson (table : Rows.Table) : Json :=
  let fields := List.ofFn fun i => fieldJson (table.schema.kind i).1
  let rows := table.rows.map fun row => List.ofFn fun i => cellJson (row i)
  Json.mkObj [("fields", toJson fields), ("rows", toJson rows)]

private def loadTable (directory : System.FilePath) (name : String) : IO Rows.Table := do
  let wire ← readWire directory name
  let some table := Rows.readRows {} wire | throw (IO.userError s!"table read failed for {name}")
  IO.FS.writeFile (directory / (name ++ ".rows.json")) (tableJson table).compress
  return table

public def main (args : List String) : IO Unit := do
  let [root] := args | throw (IO.userError "expected fixture directory")
  let directory := System.FilePath.mk root
  let wide ← loadTable directory "empty-middle-wide"
  let repeated ← loadTable directory "empty-middle-repeat"
  let zero ← loadTable directory "empty-middle-zero-width"
  let pyarrow ← loadTable directory "pyarrow-wide"
  let moved ← loadTable directory "pyarrow-empty-first"
  unless tableJson wide == tableJson pyarrow && tableJson wide == tableJson moved do
    throw (IO.userError "row equivalence changed under encoding or a moved empty batch")
  unless zero.schema.width == 0 && zero.rowCount == 18 do
    throw (IO.userError "zero-width rows were lost")
  let projection : Scan.Projection wide.schema ←
    if width : wide.schema.width = 4 then
      pure (Scan.Projection.ofArray #[⟨2, by omega⟩, ⟨1, by omega⟩,
        ⟨2, by omega⟩, ⟨3, by omega⟩, ⟨0, by omega⟩])
    else throw (IO.userError "unexpected source width")
  let empty : Scan.Projection wide.schema := Scan.Projection.ofArray #[]
  unless tableJson ⟨projection.schema, projection.project wide.rows⟩ == tableJson repeated &&
      tableJson ⟨empty.schema, empty.project wide.rows⟩ == tableJson zero do
    throw (IO.userError "typed row projection and projected IPC disagree")

  let schemaOnly ← loadTable directory "pyarrow-schema-only"
  let withEmpty ← loadTable directory "pyarrow-one-empty"
  let left ← readWire directory "pyarrow-schema-only"
  let right ← readWire directory "pyarrow-one-empty"
  let some leftEvents := readEvents {} left | throw (IO.userError "schema-only events failed")
  let some rightEvents := readEvents {} right | throw (IO.userError "empty-batch events failed")
  unless leftEvents.batches.isEmpty &&
      rightEvents.batches == [(0, leftEvents.fields.map fun _ => [])] &&
      leftEvents.fields == rightEvents.fields && tableJson schemaOnly == tableJson withEmpty do
    throw (IO.userError "empty-batch counterexample did not have equal tables and unequal events")
  unless (Rows.readRows {} (right.slice 0 (right.len - 8))).isNone do
    throw (IO.userError "missing EOS produced a relational table")
  IO.println "Typed repeated and zero-width projection, row equivalence, empty-batch counterexample and exact EOS checked."
