module

import Silmaril.Formats.Hive.Date32.Thms
meta import Silmaril.Formats.Hive.Date32.Defs

namespace Silmaril.Formats.Hive.Date32

open Silmaril.Relational Silmaril.Formats.Parquet
open Snapshot.FlatInt32 (Cell)
open WritePlan.FlatInt32 (physical)
open WritePlan.FlatInt32.RowGroups

private def leaf := "payload"
private def key := "day"
private def policy : Policy := ⟨2, 3, 5⟩
private def limits : FlatInt32Writer.Limits := ⟨16, 4096, {}, ⟨{}, 32, ⟨64, 64, ⟨16, 32⟩, 0⟩⟩⟩
private def customMarker : PartitionPath.Options := {nullMarker := "null/="}
private def dateMarker : PartitionPath.Options := {nullMarker := "2000-02-29"}

private abbrev Input := String × List (Option Int32)
private abbrev Values := Option Int32 × Option Int32

private def leap : Input := ("%64ay=2024%2D02%2d29", [some 1, none, some 2])

private def defaultInputs : List Input :=
  [leap, ("day=1969-12-31", [some 3]), ("day=9999-12-31", [some 4]),
    ("day=__HIVE_DEFAULT_PARTITION__", [none]), ("day=%5F%5FHIVE_DEFAULT_PARTITION__", [some 5]),
    ("day=1970-01-01", [some 6]), leap, ("day=0000-01-01", [some 7])]

private def customInputs : List Input :=
  [("day=null%2F%3D", [none, some 8]), ("day=2000%2D02%2d29", [some 9])]

private def dateMarkerInputs : List Input :=
  [("day=2000-02-29", [none]), ("day=2000%2D02%2d29", [some 10]), ("day=2000-03-01", [some 11])]

private def emit (input : Input) : Except (EmitError Error) File :=
  emitBucket policy limits leaf ⟨input.1, input.2.map fun slot _ => slot⟩

private def selectAll : Scan.Predicate (partition key).toScan Cell := fun _ => some true

private def keep : Scan.Predicate (partition key).toScan Cell := fun cells =>
  some ((cells (0 : Fin 1)).all (·.toInt ≤ 20000))

private def scan (options : PartitionPath.Options) := scanPruned leaf key options policy limits

private def observe (rows : Scan.Table ((partition key).extend (physical leaf)) Cell) : List Values :=
  rows.map fun row => (TypedPartitions.physicalCells (schema := partition key) row (0 : Fin 1),
    TypedPartitions.partitionCells (physical := physical leaf) row (0 : Fin 1))

#guard (["0000-01-01", "1969-12-31", "1970-01-01", "2000-02-29", "2024-02-29", "9999-12-31"].map
    fun text => (decodeText text).toOption.map Int32.toInt) ==
  [some (-719528), some (-1), some 0, some 11016, some 19782, some 2932896]

#guard (["1900-02-29", "2024-02-30", "2024-2-9", "10000-01-01", "", "2024-02-29/", " 2024-02-29"].map decodeText) ==
  (["1900-02-29", "2024-02-30", "2024-2-9", "10000-01-01", "", "2024-02-29/", " 2024-02-29"].map
    fun text => .error (.invalidDate text))

#guard Id.run do
  let .ok files := defaultInputs.mapM emit | return false
  let .ok all := scan {} selectAll files | return false
  let .ok selected := scan {} keep files | return false
  let .eos := selected.toArrow.termination | return false
  return observe all.rows == [(some 1, some 19782), (none, some 19782), (some 2, some 19782),
    (some 3, some (-1)), (some 4, some 2932896), (none, none), (some 5, none), (some 6, some 0),
    (some 1, some 19782), (none, some 19782), (some 2, some 19782), (some 7, some (-719528))] &&
    observe selected.rows == (observe all.rows).filter (fun row => row.2.all (·.toInt ≤ 20000)) &&
    selected.batches.map (fun batch => (batch.position.fileIndex, batch.position.groupIndex, batch.columns.rowCount)) ==
      [(0, 0, 2), (0, 1, 1), (1, 0, 1), (3, 0, 1), (4, 0, 1), (5, 0, 1), (6, 0, 2), (6, 1, 1), (7, 0, 1)] &&
    selected.batches.all (fun batch => (files[batch.position.fileIndex]?).map (·.path) == some batch.position.path)

#guard Id.run do
  let .ok files := customInputs.mapM emit | return false
  let .ok selected := scan customMarker selectAll files | return false
  return selected.result.isOk && observe selected.rows == [(none, none), (some 8, none), (some 9, some 11016)]

#guard Id.run do
  let .ok files := dateMarkerInputs.mapM emit | return false
  let .ok selected := scan dateMarker selectAll files | return false
  return selected.result.isOk && observe selected.rows == [(none, none), (some 10, none), (some 11, some 11017)]

private def malformed : File := ⟨"%64ay=2024%2D02%2d30/part-0.parquet", 1, [1], ⟨ByteArray.empty⟩⟩

-- The bad date wins over both a rejecting predicate and an unreadable payload.
#guard Id.run do
  let .ok file := emit leap | return false
  let .ok selected := scan {} (fun cells => some (cells (0 : Fin 1) == some 19782)) [file, malformed, file] |
    return false
  let .error (.file 1 path (.partition (.binding directory (.conversion "day" (.invalidDate "2024-02-30"))))) :=
    selected.result | return false
  return path == malformed.path && directory == "%64ay=2024%2D02%2d30" &&
    selected.batches.map (·.position) == [⟨0, file.path, 0⟩, ⟨0, file.path, 1⟩] &&
    observe selected.rows == [(some 1, some 19782), (none, some 19782), (some 2, some 19782)]

#guard Id.run do
  let bad := {malformed with path := "%6Gay=2024-02-29/part-0.parquet"}
  let .ok selected := scan {} (fun _ => some false) [bad] | return false
  let .error (.file 0 path (.partition (.path "%6Gay=2024-02-29" .invalidEscape))) := selected.result |
    return false
  return path == bad.path && selected.batches.isEmpty

#guard Id.run do
  let bad := {malformed with path := "%FF=2024-02-29/part-0.parquet"}
  let .ok selected := scan {} selectAll [bad] | return false
  let .error (.file 0 path (.partition (.path "%FF=2024-02-29" .invalidUtf8))) := selected.result |
    return false
  return path == bad.path && selected.batches.isEmpty

#guard Id.run do
  let bad := {malformed with path := "d%61x=2024-02-29/part-0.parquet"}
  let .ok selected := scan {} selectAll [bad] | return false
  let .error (.file 0 path (.partition (.binding _ (.unknownKey "dax")))) := selected.result |
    return false
  return path == bad.path && selected.batches.isEmpty

#guard Id.run do
  let bad := {malformed with path := "day=2024-02-29/%64ay=2024-03-01/part-0.parquet"}
  let .ok selected := scan {} selectAll [bad] | return false
  let .error (.file 0 path (.partition (.path _ (.duplicateKey "day")))) := selected.result |
    return false
  return path == bad.path && selected.batches.isEmpty

#guard Id.run do
  let bad := {malformed with path := "part-0.parquet"}
  let .ok selected := scan {} selectAll [bad] | return false
  let .error (.file 0 path (.partition (.binding "" (.missingKey "day")))) := selected.result |
    return false
  return path == bad.path && selected.batches.isEmpty

#guard Id.run do
  let bad := {malformed with path := "%64ay=2024%2D02%2d29/part-0.parquet"}
  let .ok rejected := scan {} (fun _ => some false) [bad] | return false
  let .ok selected := scan {} selectAll [bad] | return false
  let .error (.file 0 path (.payload _)) := selected.result | return false
  return path == bad.path && rejected.result.isOk && rejected.batches.isEmpty

#print axioms decodeText_ok_iff
#print axioms bindFileCells_singleton
#print axioms scanPruned_first_binding_error

private def showCell (cell : Option Int32) : String :=
  cell.map (fun value => toString value.toInt) |>.getD "null"

private def logTrace (directory : System.FilePath) (name : String)
    (options : PartitionPath.Options) (predicate : Scan.Predicate (partition key).toScan Cell)
    (files : List File) : IO Unit := do
  let .ok trace := scan options predicate files | throw (IO.userError "DATE schema admission failed")
  let .ok () := trace.result | throw (IO.userError "DATE scan did not reach EOS")
  let lines := trace.batches.map fun batch =>
    let pos := batch.position
    let rows := observe batch.columns.toRows
    let values := rows.map fun (payload, date) => showCell payload ++ "," ++ showCell date
    String.intercalate "\t" ([toString pos.fileIndex, pos.path, toString pos.groupIndex,
      toString batch.columns.rowCount] ++ values)
  IO.FS.writeFile (directory / (name ++ ".tsv")) (String.intercalate "\n" lines ++ "\n")

private def writeFixture (root : System.FilePath) (name : String) (options : PartitionPath.Options)
    (inputs : List Input) : IO Unit := do
  let .ok files := inputs.mapM emit | throw (IO.userError "native Parquet emit failed")
  let directory := root / name
  for file in files do
    let path := directory / file.path
    if let some parent := path.parent then IO.FS.createDirAll parent
    IO.FS.writeBinFile path file.bytes.data
  IO.FS.writeFile (directory / "inventory.txt") (String.intercalate "\n" (files.map (·.path)) ++ "\n")
  logTrace directory "all" options selectAll files
  logTrace directory "selected" options keep files

public def run (args : List String) : IO Unit := do
  let [root] := args | throw (IO.userError "usage: Checks.lean <oracle-fixture-directory>")
  writeFixture root "default" {} defaultInputs
  writeFixture root "custom" customMarker customInputs
  writeFixture root "date-marker" dateMarker dateMarkerInputs

end Silmaril.Formats.Hive.Date32

public def main : List String → IO Unit := Silmaril.Formats.Hive.Date32.run
