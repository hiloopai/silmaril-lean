module

import Silmaril.Formats.Parquet.FlatProjection.ToScan.Thms
import Lean.Data.Json
meta import Silmaril.Formats.Parquet.FlatProjection.ToScan.Defs
meta import Lean.Data.Json

open Lean Silmaril Silmaril.Relational Silmaril.Formats
open Silmaril.Formats.Parquet.FlatProjection
open Silmaril.Formats.Parquet.FlatProjection.Composition
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

private def checkParquet (directory : System.FilePath) (source stream : String)
    (ordinals expectedCounts : List Nat) : IO Unit := do
  let input := Bytes.mk (← IO.FS.readBinFile (directory / (source ++ ".parquet")))
  let limits : Limits :=
    { maxFields := ordinals.length, maxFileRows := expectedCounts.sum, column := { maxFileBytes := input.length } }
  let .ok checked := openFile limits input ordinals | throw (IO.userError s!"Parquet open failed for {source}")
  match exhausted : checked.readAll limits with
  | .error error => throw (IO.userError s!"Parquet exhaustion failed: {repr error}")
  | .ok batches =>
    let observed := ToScan.observeGroups checked batches
    let direct := Rows.materialize observed (ToScan.observeGroups_aligned exhausted)
    let wire ← readWire directory stream
    let viaIpc ← loadTable directory stream
    unless readEvents {} wire == some observed && observed.batches.map Prod.fst == expectedCounts &&
        tableJson direct == tableJson viaIpc do
      throw (IO.userError s!"direct Parquet and native IPC observations differ for {stream}")
    IO.FS.writeFile (directory / (stream ++ ".direct.rows.json")) (tableJson direct).compress

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
  let input := Bytes.mk (← IO.FS.readBinFile (directory / "empty-middle.parquet"))
  for (selection, expectedOrdinals, pinned) in [(projection, [1, 0, 1, 2, 3], repeated), (empty, [], zero)] do
    let some composed := composeOrdinals [3, 0, 1, 2] (Rows.positions selection)
      | throw (IO.userError "typed Scan positions could not be composed")
    unless composed == expectedOrdinals do
      throw (IO.userError "wrong composed physical ordinals")
    let sourceLimits : Limits :=
      { maxFields := composed.length, maxFileRows := 18, column := { maxFileBytes := input.length } }
    let ipcLimits : Arrow.MixedFlat.Limits := { observation := {
      ipc := { fields := composed.length, batches := 3 }, totalRows := 18,
      totalCells := composed.length * 18 } }
    let .ok wire := convert sourceLimits ipcLimits input composed
      | throw (IO.userError "the composed physical projection did not emit IPC")
    let some direct := Rows.readRows ipcLimits wire
      | throw (IO.userError "the composed physical projection did not materialize")
    let staged : Rows.Table := ⟨selection.schema, selection.project wide.rows⟩
    unless tableJson staged == tableJson direct && tableJson direct == tableJson pinned do
      throw (IO.userError "staged Scan projection and composed physical IPC disagree")
  IO.println "Staged and composed IPC tables agree under separate exact caps for repeats and zero width."

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
  checkParquet directory "wide" "wide-wide" [3, 0, 1, 2] [12, 6]
  checkParquet directory "empty-middle" "empty-middle-repeat" [1, 0, 1, 2, 3] [12, 0, 6]
  checkParquet directory "empty-middle" "empty-middle-zero-width" [] [12, 0, 6]
  checkParquet directory "schema-only" "schema-only-repeat" [1, 0, 1, 2, 3] []
  IO.println "Direct checked Parquet groups and native IPC agree on four materialized tables."
