module

import Silmaril.Formats.Hive.WritePlan.FlatInt32.Thms
meta import Silmaril.Formats.Hive.WritePlan.FlatInt32.Defs

namespace Silmaril.Formats.Hive.WritePlan.FlatInt32

open Silmaril.Relational Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema extendRow physicalCells partitionCells)

private def leaf := "payload"
private def partitions : PartitionSchema Unit := ⟨#[⟨"key", (), .reject⟩]⟩
private def expected := partitions.extend (physical leaf)
private def limits : FlatInt32Writer.Limits := ⟨16, 4096, {}, ⟨{}, 32, ⟨64, 64, ⟨16, 32⟩, 0⟩⟩⟩

private abbrev RowValues := Option Int32 × Option Int32

private def row (values : RowValues) : Scan.Row expected Snapshot.FlatInt32.Cell :=
  extendRow (fun _ => values.1) (fun _ => values.2)

private def inputValues : List RowValues :=
  [(some 10, some 3), (none, some 1), (some 11, some 3), (some 4, none),
    (some 5, some 1), (none, none), (some 10, some 3), (some 8, some 2)]

private def grouped : List RowValues :=
  [(some 10, some 3), (some 11, some 3), (some 10, some 3),
    (none, some 1), (some 5, some 1), (some 4, none), (none, none), (some 8, some 2)]

private def dbOf (input : List RowValues) : Database String :=
  fun name => if name == "source" then some ⟨expected, input.map row⟩ else none

private def encode : Encode Snapshot.FlatInt32.Cell String :=
  fun _ value => .ok (toString value.toInt)

private def decode : TypedPartitions.Convert Snapshot.FlatInt32.Cell String :=
  fun _ text =>
    match text.toInt? with
    | none => .error "expected decimal"
    | some n => if (Int32.ofInt n).toInt == n then .ok (Int32.ofInt n) else .error "outside Int32"

private def observe (rows : Scan.Table expected Snapshot.FlatInt32.Cell) : List RowValues :=
  rows.map fun value =>
    ((physicalCells (schema := partitions) value) (0 : Fin 1),
      (partitionCells (physical := physical leaf) value) (0 : Fin 1))

private def manifest := emit (dbOf inputValues) "source" leaf partitions {} encode limits

#guard manifest.toOption.map (List.map fun file => (file.path, file.rowCount)) == some
  [("key=3/part-0.parquet", 3), ("key=1/part-0.parquet", 2),
    ("key=__HIVE_DEFAULT_PARTITION__/part-0.parquet", 2), ("key=2/part-0.parquet", 1)]

#guard (manifest.toOption.bind fun files => (restore leaf partitions {} decode limits files).toOption.map observe) ==
  some grouped

#guard match emit (dbOf []) "source" leaf partitions {} encode limits with
  | .ok [] => (restore leaf partitions {} decode limits []).toOption.map observe == some []
  | _ => false

#guard Id.run do
  let root : PartitionSchema Unit := ⟨#[]⟩
  let db : Database String := fun _ => some ⟨root.extend (physical leaf), [fun _ => some 5]⟩
  let .ok [file] := emit db "source" leaf root {} encode limits | return false
  let .ok rows := restore leaf root {} decode limits [file] | return false
  return file.path == "part-0.parquet" && (rows.map fun one => one (0 : Fin 1)) == [some 5]

#guard
  let duplicate : PartitionSchema Unit := ⟨#[⟨"key", (), .reject⟩, ⟨"key", (), .reject⟩]⟩
  let db : Database String := fun _ => some ⟨duplicate.extend (physical leaf), []⟩
  match emit db "source" leaf duplicate {} encode limits with
  | .error (.routing (.schema (.schemaKeys (.duplicateKey "key")))) => true
  | _ => false

#guard match emit (dbOf []) "unknown" leaf partitions {} encode limits with
  | .error .missingName => true
  | _ => false

#guard match emit (dbOf []) "source" "wrong" partitions {} encode limits with
  | .error .schemaMismatch => true
  | _ => false

#guard
  let bad : Encode Snapshot.FlatInt32.Cell String := fun _ key =>
    if key == 3 then .ok "3" else .error (toString key.toInt)
  match emit (dbOf inputValues) "source" leaf partitions {} bad {limits with maxFileBytes := 1} with
  | .error (.routing (.row 1 (.encode "key" "1"))) => true
  | _ => false

#guard
  let marker : Encode Snapshot.FlatInt32.Cell String := fun _ _ => .ok "__HIVE_DEFAULT_PARTITION__"
  match emit (dbOf inputValues) "source" leaf partitions {} marker limits with
  | .error (.routing (.row 0 (.render (.nullMarkerCollision "key")))) => true
  | _ => false

#guard Id.run do
  let options : PartitionPath.Options := {nullMarker := "null/="}
  let .ok [file] := emit (dbOf [(some 4, none)]) "source" leaf partitions options encode limits |
    return false
  return file.path == "key=null%2F%3D/part-0.parquet" &&
    (restore leaf partitions options decode limits [file]).toOption.map observe == some [(some 4, none)]

#guard match emit (dbOf [(some 4, some 1), (some 5, some 2), (none, some 2)])
    "source" leaf partitions {} encode {limits with page.scalar.levels.values := 1} with
  | .error (.parquet "key=2/part-0.parquet" .pageBudget) => true
  | _ => false

#guard Id.run do
  let some (file :: _) := manifest.toOption | return false
  let invalid := { file with path := "../" ++ file.path }
  match restore leaf partitions {} decode limits [invalid] with
  | .error (.path path .invalidSegment) => return path == invalid.path
  | _ => return false

#guard Id.run do
  let some (file :: _) := manifest.toOption | return false
  match restore leaf partitions {} decode limits [{ file with path := "key=bad/part-0.parquet" }] with
  | .error (.partition (.binding "key=bad" (.conversion "key" "expected decimal"))) => return true
  | _ => return false

#guard Id.run do
  let some (file :: _) := manifest.toOption | return false
  match restore leaf partitions {} decode limits [{ file with path := "key=3/other.parquet" }] with
  | .error (.filename "key=3/other.parquet") => return true
  | _ => return false

#print axioms emit_eq_reference
#print axioms emit_plan_error
#print axioms restore_emit

/-- Write the exact pure manifest to a fixture directory for the independent reader. -/
public def writeFixture (directory : System.FilePath) : IO Unit := do
  let .ok files := manifest | throw (IO.userError "native Hive emit failed")
  IO.FS.createDirAll directory
  for file in files do
    let path := directory / file.path
    if let some parent := path.parent then IO.FS.createDirAll parent
    IO.FS.writeBinFile path file.bytes.data
  IO.FS.writeFile (directory / "manifest.txt") (String.intercalate "\n" (files.map (·.path)) ++ "\n")

end Silmaril.Formats.Hive.WritePlan.FlatInt32

public def main (args : List String) : IO Unit :=
  match args with
  | [directory] => Silmaril.Formats.Hive.WritePlan.FlatInt32.writeFixture directory
  | _ => throw (IO.userError "expected a fixture output directory")
