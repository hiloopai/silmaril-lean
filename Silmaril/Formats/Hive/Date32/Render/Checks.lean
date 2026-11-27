module

import Silmaril.Formats.Hive.Date32.Render.Thms
import Silmaril.Formats.Hive.Date32.Thms
meta import Silmaril.Formats.Hive.Date32.Render.Defs

namespace Silmaril.Formats.Hive.Date32

open Silmaril.Relational Silmaril.Formats.Parquet
open Snapshot.FlatInt32 (Cell)
open WritePlan.FlatInt32 (Database physical)
open WritePlan.FlatInt32.RowGroups (File Policy)

private def leaf := "payload"
private def policy : Policy := ⟨2, 3, 5⟩
private def limits : FlatInt32Writer.Limits := ⟨16, 4096, {}, ⟨{}, 32, ⟨64, 64, ⟨16, 32⟩, 0⟩⟩⟩
private def specialKey := "d/é=%"
private def specialMarker : PartitionPath.Options := {nullMarker := "null/=%", requiredKeys := [specialKey]}
private def dateMarker : PartitionPath.Options := {nullMarker := "2000-02-29"}

private instance {α : Type} [BEq α] : BEq (Except RenderError α) where
  beq
    | .ok actual, .ok expected => actual == expected
    | .error actual, .error expected => actual == expected
    | _, _ => false

#guard ([(-719528), -1, 0, 11016, 19782, 2932896] : List Int32).map encodeText ==
  [.ok "0000-01-01", .ok "1969-12-31", .ok "1970-01-01", .ok "2000-02-29", .ok "2024-02-29", .ok "9999-12-31"]

#guard encodeText (-719529) == .error (.outsideDateProfile (-719529)) &&
  encodeText 2932897 == .error (.outsideDateProfile 2932897)

#guard renderDirectory "day" {} (some 19782) == .ok "day=2024-02-29" &&
  renderDirectory "day" {} none == .ok "day=__HIVE_DEFAULT_PARTITION__"

#guard renderDirectory specialKey specialMarker (some (-1)) == .ok "d%2F%C3%A9%3D%25=1969-12-31" &&
  renderDirectory specialKey specialMarker none == .ok "d%2F%C3%A9%3D%25=null%2F%3D%25"

#guard renderDirectory "day" dateMarker (some 11016) == .error (.path (.nullMarkerCollision "day")) &&
  renderDirectory "day" dateMarker none == .ok "day=2000-02-29"

#guard renderDirectory "day" {} (some 11016) == .ok "day=2000-02-29" &&
  renderDirectory "day" {nullMarker := "2000%2D02%2D29"} (some 11016) == .ok "day=2000-02-29" &&
  renderDirectory "day" {nullMarker := "2000%2D02%2D29"} none == .ok "day=2000%252D02%252D29"

#guard renderDirectory "day" {nullMarker := ""} none == .error (.path .emptyNullMarker) &&
  renderDirectory "" {} none == .error (.path .emptyKey) &&
  renderDirectory "day" {requiredKeys := ["other"]} (some 0) == .error (.path (.missingKey "other"))

private abbrev Row := Option Int32 × Option Int32

private def dbOf (key : String) (rows : List Row) : Database String := fun name =>
  if name == "source" then
    some ⟨(partition key).extend (physical leaf), rows.map fun (payload, day) =>
      TypedPartitions.extendRow (fun _ => payload) (fun _ => day)⟩
  else none

private def emit (key : String) (options : PartitionPath.Options) (rows : List Row) :=
  WritePlan.FlatInt32.RowGroups.emit (dbOf key rows) "source" leaf (partition key) options encode policy limits

private def restore (key : String) (options : PartitionPath.Options) (files : List File) :=
  (WritePlan.FlatInt32.RowGroups.restore leaf (partition key) options convert policy limits files).map fun rows =>
    rows.map fun row => (TypedPartitions.physicalCells (schema := partition key) row (0 : Fin 1),
      TypedPartitions.partitionCells (physical := physical leaf) row (0 : Fin 1))

private def standardRows : List Row :=
  [(some 1, some 19782), (some 2, none), (none, some 19782), (some 3, some (-719528)),
    (some 4, some 2932896), (none, none), (some 5, some 19782)]

private def standardGrouped : List Row :=
  [(some 1, some 19782), (none, some 19782), (some 5, some 19782), (some 2, none),
    (none, none), (some 3, some (-719528)), (some 4, some 2932896)]

private def escapedRows : List Row := [(none, some (-1)), (some 8, none), (some 9, some 0)]

private def markerRows : List Row := [(some 10, none), (some 11, some 11017)]

#guard Id.run do
  let .ok files := emit "day" {} standardRows | return false
  return files.map (fun file => (file.path, file.groupRows)) ==
    [("day=2024-02-29/part-0.parquet", [2, 1]), ("day=__HIVE_DEFAULT_PARTITION__/part-0.parquet", [2]),
      ("day=0000-01-01/part-0.parquet", [1]), ("day=9999-12-31/part-0.parquet", [1])] &&
    (restore "day" {} files).toOption == some standardGrouped

#guard Id.run do
  let .ok files := emit specialKey specialMarker escapedRows | return false
  return (restore specialKey specialMarker files).toOption == some escapedRows &&
    files.map (·.path) == ["d%2F%C3%A9%3D%25=1969-12-31/part-0.parquet",
      "d%2F%C3%A9%3D%25=null%2F%3D%25/part-0.parquet", "d%2F%C3%A9%3D%25=1970-01-01/part-0.parquet"]

#guard Id.run do
  let .ok files := emit "day" dateMarker markerRows | return false
  return (restore "day" dateMarker files).toOption == some markerRows

#guard match emit "day" dateMarker (markerRows ++ [(none, some 11016), (some 12, some 2932897)]) with
  | .error (.source (.routing (.row 2 (.render (.nullMarkerCollision "day"))))) => true
  | _ => false

#print axioms decodeDirectory_singleton
#print axioms encodeText_ok_iff
#print axioms encode_convert_leftInverse
#print axioms encodeText_outside
#print axioms decodeDirectory_renderDirectory
#print axioms renderDirectory_markerCollision

private def writeFixture (root : System.FilePath) (name key : String) (options : PartitionPath.Options)
    (input grouped : List Row) : IO Unit := do
  let .ok files := emit key options input | throw (IO.userError "DATE manifest emission failed")
  unless (restore key options files).toOption == some grouped do
    throw (IO.userError "DATE manifest restoration did not match the grouped rows")
  let directory := root / name
  for file in files do
    let path := directory / file.path
    if let some parent := path.parent then IO.FS.createDirAll parent
    IO.FS.writeBinFile path file.bytes.data
  IO.FS.writeFile (directory / "inventory.txt") (String.intercalate "\n" (files.map (·.path)) ++ "\n")

public def runRenderChecks (args : List String) : IO Unit := do
  let [root] := args | throw (IO.userError "usage: Checks.lean <oracle-fixture-directory>")
  writeFixture root "default" "day" {} standardRows standardGrouped
  writeFixture root "escaped" specialKey specialMarker escapedRows escapedRows
  writeFixture root "date-marker" "day" dateMarker markerRows markerRows

end Silmaril.Formats.Hive.Date32

public def main : List String → IO Unit := Silmaril.Formats.Hive.Date32.runRenderChecks
