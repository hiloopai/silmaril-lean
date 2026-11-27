module

import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Thms
import Silmaril.Formats.Parquet.Snapshot.Footer.Thms
meta import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Defs

namespace Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups

open Silmaril.Relational Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema extendRow physicalCells partitionCells)
open Snapshot.FlatInt32 (Cell)

private def leaf := "payload"
private def partitions : PartitionSchema Unit := ⟨#[⟨"key", (), .reject⟩]⟩
private def expected := partitions.extend (physical leaf)
private def policy : Policy := ⟨2, 3, 5⟩
private def limits : FlatInt32Writer.Limits := ⟨16, 4096, {}, ⟨{}, 32, ⟨64, 64, ⟨16, 32⟩, 0⟩⟩⟩
private def customMarker : PartitionPath.Options := {nullMarker := "null/="}

private abbrev Values := Option Int32 × Option Int32

private def input : List Values :=
  [(some 10, some 3), (some 1, some 1), (some 4, none), (some 11, some 3), (none, some 1),
    (none, none), (some 12, some 3), (some 5, some 1), (some 8, some 2), (some 6, some 1),
    (some 7, none), (some 9, some 1)]

private def grouped : List Values :=
  [(some 10, some 3), (some 11, some 3), (some 12, some 3), (some 1, some 1), (none, some 1),
    (some 5, some 1), (some 6, some 1), (some 9, some 1), (some 4, none), (none, none),
    (some 7, none), (some 8, some 2)]

private def selected : List Values := grouped.take 3 ++ (grouped.drop 8).take 3

private def dbOf (values : List Values) : Database String := fun name =>
  if name == "source" then some ⟨expected, values.map fun (payload, key) => extendRow (fun _ => payload) (fun _ => key)⟩
  else none

private def encode : Encode Cell String := fun _ value => .ok (toString value.toInt)

private def decode : TypedPartitions.Convert Cell String := fun _ text =>
  match text.toInt? with
  | none => .error "expected decimal"
  | some n => if (Int32.ofInt n).toInt == n then .ok (Int32.ofInt n) else .error "outside Int32"

private def observe (rows : Scan.Table expected Cell) : List Values :=
  rows.map fun row => ((physicalCells (schema := partitions) row) (0 : Fin 1),
    (partitionCells (physical := physical leaf) row) (0 : Fin 1))

private def keep : Scan.Predicate partitions.toScan Cell := fun cells =>
  let key := cells (0 : Fin 1)
  some (key == some 3 || key.isNone)

private def make (options : PartitionPath.Options) := emit (dbOf input) "source" leaf partitions options encode policy limits
private def read (options : PartitionPath.Options) := restore leaf partitions options decode policy limits
private def prune (options : PartitionPath.Options) := restorePruned leaf partitions options decode policy limits keep

#guard (make {}).toOption.map (List.map fun file => (file.path, file.rowCount, file.groupRows)) == some
  [("key=3/part-0.parquet", 3, [2, 1]), ("key=1/part-0.parquet", 5, [2, 2, 1]),
    ("key=__HIVE_DEFAULT_PARTITION__/part-0.parquet", 3, [2, 1]), ("key=2/part-0.parquet", 1, [1])]

#guard ((make {}).toOption.bind fun files => (read {} files).toOption.map observe) == some grouped

#guard Id.run do
  let .ok files := make customMarker | return false
  let .ok full := read customMarker files | return false
  let .ok rows := prune customMarker files | return false
  return files.any (fun file => file.path == "key=null%2F%3D/part-0.parquet") && observe rows == selected &&
    observe (Scan.select (fun row => keep (partitionCells row)) full) == selected

#guard ((make {}).toOption.bind fun files => (prune {} files).toOption.map observe) == some selected

#guard Id.run do
  let .ok files := make {} | return false
  let .ok rows := restorePruned leaf partitions {} decode policy limits (fun _ => none) files | return false
  return rows.isEmpty

#guard Id.run do
  let .ok (first :: second :: _) := make {} | return false
  let .ok rows := prune {} [first, second, first] | return false
  return observe rows == grouped.take 3 ++ grouped.take 3

#guard match emit (dbOf []) "source" leaf partitions {} encode policy limits with
  | .ok [] => (read {} []).toOption.map observe == some []
  | _ => false

#guard match emit (dbOf input) "source" leaf partitions {} encode {policy with rowsPerGroup := 0} limits with
  | .error (.policy .zeroRowsPerGroup) => true
  | _ => false

#guard match emit (dbOf input) "source" leaf partitions {} encode {policy with maxGroupsPerFile := 2} limits with
  | .error (.cuts "key=1/part-0.parquet" .groupLimit) => true
  | _ => false

#guard match emit (dbOf input) "source" leaf partitions {} encode {policy with maxRowsPerFile := 4} limits with
  | .error (.cuts "key=1/part-0.parquet" (.rowLimit 5)) => true
  | _ => false

#guard Id.run do
  let .ok (first :: _) := make {} | return false
  match read {} [{first with groupRows := [1, 2]}] with
  | .error (.file 0 _ (.payload .dimensions)) => return true
  | _ => return false

#guard Id.run do
  let .ok (first :: _) := make {} | return false
  let invalid := {first with path := "../" ++ first.path}
  match restorePruned leaf partitions {} decode policy limits (fun _ => some false) [first, invalid] with
  | .error (.file 1 path (.path (.path _ .invalidSegment))) => return path == invalid.path
  | _ => return false

-- Reject a DATE file whose projected physical schema matches INT32.
#guard Id.run do
  let .ok files := make {} | return false
  let some file := files.getLast? | return false
  let .ok annotated := FlatInt32Writer.emitAnnotated .date limits ⟨1, [⟨leaf, .optional [some 8]⟩]⟩ |
    return false
  match read {} [{file with bytes := annotated.bytes}] with
  | .error (.file 0 path (.payload .wireSchema)) => return path == file.path
  | _ => return false

private def damage (file : File) (ordinal : Nat) : Option File := do
  let checked ← (openPayload policy limits leaf file).toOption
  let group ← checked.groupAt ordinal
  let column ← group.columns.head?
  return {file with bytes := ⟨file.bytes.data.set! column.metadata.dataPageOffset.toNat 0⟩}

-- Corrupt the second group of the third literal file. The first group still decodes.
#guard Id.run do
  let .ok (first :: skipped :: target :: rest) := make {} | return false
  let some damaged := damage target 1 | return false
  let .ok opened := openPayload policy limits leaf damaged | return false
  let .ok decoder := Snapshot.FlatInt32.bind (InputFailure := Unit) (readLimits limits policy.rowsPerGroup)
    (physical leaf) opened.metadata | return false
  let .ok prior := opened.readGroup decoder 0 | return false
  match prune {} (first :: skipped :: damaged :: rest) with
  | .error (.file 2 path (.payload (.parquet (.decode 1 (.profile (.page (.header (.missingField 1)))))))) =>
    return path == target.path && (prior.map fun row => row (0 : Fin 1)) == [some 4, none]
  | _ => return false

-- The same damaged selected-group header is untouched when the path is rejected.
#guard Id.run do
  let .ok (first :: skipped :: target :: rest) := make {} | return false
  let some damaged := damage skipped 1 | return false
  return (prune {} (first :: damaged :: target :: rest)).toOption.map observe == some selected

#print axioms planCuts_exact
#print axioms splitSlots_exact
#print axioms readPayload_footer
#print axioms FileMatches.counts
#print axioms restore_emit
#print axioms restorePruned_eq_filter
#print axioms Snapshot.check_footer

private def writeFixture (root : System.FilePath) (name : String) (options : PartitionPath.Options) : IO Unit := do
  let .ok files := make options | throw (IO.userError "multi-group native emit failed")
  let .ok rows := prune options files | throw (IO.userError "multi-group native pruning failed")
  let directory := root / name
  IO.FS.createDirAll directory
  for file in files do
    let path := directory / file.path
    if let some parent := path.parent then IO.FS.createDirAll parent
    IO.FS.writeBinFile path file.bytes.data
  let manifest := files.map fun file =>
    file.path ++ "\t" ++ toString file.rowCount ++ "\t" ++ String.intercalate "," (file.groupRows.map toString)
  let showCell := fun (cell : Option Int32) => cell.map (fun value => toString value.toInt) |>.getD "null"
  let selected := (observe rows).map fun (payload, key) => showCell payload ++ "\t" ++ showCell key
  IO.FS.writeFile (directory / "manifest.tsv") (String.intercalate "\n" manifest ++ "\n")
  IO.FS.writeFile (directory / "selected.tsv") (String.intercalate "\n" selected ++ "\n")

public def main (args : List String) : IO Unit := do
  let [root] := args | throw (IO.userError "expected a fixture output directory")
  writeFixture root "default" {}
  writeFixture root "custom" customMarker

end Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups

public def main := Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.main
