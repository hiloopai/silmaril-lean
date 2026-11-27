module

import Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.Pruning.Thms
import Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.Thms
import Silmaril.Formats.Hive.Manifest.Thms
import Silmaril.Formats.Relational.NamedTable.FromHiveDateUtf8.Thms
meta import Silmaril.Formats.Relational.NamedTable.FromHiveDateUtf8.Defs
meta import Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.Pruning.Defs

namespace Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter

open Silmaril.Relational Silmaril.Formats.Parquet Silmaril.Formats.Arrow
open Int32ByteArrayGroup.File (Kind Value)
open Silmaril.Formats.Relational.NamedTable (Packed)
open Silmaril.Formats.Relational.NamedTable.FromHiveDateUtf8 (importSelected importResult)

private def schema (order : Order) : Schema := ⟨"n", "blob", ⟨"day", "label", order⟩⟩
private def dateFirst := schema .dateFirst
private def textFirst := schema .textFirst
private def limits : Limits :=
  ⟨⟨2, 3, 5⟩, ⟨⟨8192, {}, ⟨{}, 32, ⟨128, 128, ⟨16, 32⟩, 0⟩⟩,
    ⟨⟨{}, 32, ⟨128, 128, ⟨16, 32⟩, 0⟩⟩, ⟨128, 20⟩⟩, {}⟩, 3, 5⟩⟩
private def custom : PartitionPath.Options := {nullMarker := "null/=%"}

private def utf8 (text : String) : Bytes := ⟨text.toUTF8⟩

private structure Sample where
  int : Option Int32
  blob : Option Bytes
  day : Option Int32
  label : Option Bytes

private def leap := some (utf8 "café/blue")
private def input : List Sample :=
  [⟨some (-7), some (.ofList [255, 0]), some 19782, leap⟩,
    ⟨some 0, some (utf8 "x"), none, some (utf8 "")⟩,
    ⟨none, some .empty, some 19782, leap⟩,
    ⟨some 9, some (utf8 "y"), some (-719528), none⟩,
    ⟨none, none, none, some (utf8 "")⟩,
    ⟨some 11, none, some 19782, leap⟩]

private def dbOf (layout : Schema) (samples : List Sample) : Packed String String Value := fun name =>
  if name == "source" then
    some ⟨layout.toScan, samples.flatMap fun sample =>
      (Int32ByteArrayGroup.File.rows layout.intField layout.byteField [(sample.int, sample.blob)]).map
        fun row => TypedPartitions.extendRow row (layout.keys.cells sample.day sample.label)⟩
  else none

private def make (layout : Schema) (options : PartitionPath.Options) :=
  emit (dbOf layout input) "source" layout options limits

private def showCell : (kind : Kind) → Option (Value kind) → String
  | .int32 _, some value => toString value.toInt
  | .byteArray _, some bytes => "b:" ++ String.intercalate "," (bytes.toList.map (fun byte => toString byte.toNat))
  | _, none => "null"

private def observed (output : Scan.Schema String Kind) (row : Scan.Row output Value) : List String :=
  List.ofFn fun i => showCell (output.kind i).2 (row i)

private def defaultPaths :=
  ["day=2024-02-29/label=caf%C3%A9%2Fblue/part-0.parquet",
    "day=__HIVE_DEFAULT_PARTITION__/label=/part-0.parquet",
    "day=0000-01-01/label=__HIVE_DEFAULT_PARTITION__/part-0.parquet"]

private def customPaths :=
  ["label=caf%C3%A9%2Fblue/day=2024-02-29/part-0.parquet", "label=/day=null%2F%3D%25/part-0.parquet",
    "label=null%2F%3D%25/day=0000-01-01/part-0.parquet"]

#guard Id.run do
  let .ok files := make dateFirst {} | return false
  let .ok trace := readManifest dateFirst {} limits files | return false
  let .eos := trace.termination | return false
  return files.map (·.path) == defaultPaths && files.map (·.groupRows) == [[2, 1], [2], [1]] &&
    trace.batches.map (·.rowCount) == [2, 1, 2, 1] &&
    trace.rows.map (observed dateFirst.toScan) ==
      [["-7", "b:255,0", "19782", "b:99,97,102,195,169,47,98,108,117,101"],
       ["null", "b:", "19782", "b:99,97,102,195,169,47,98,108,117,101"],
       ["11", "null", "19782", "b:99,97,102,195,169,47,98,108,117,101"],
       ["0", "b:120", "null", "b:"], ["null", "null", "null", "b:"], ["9", "b:121", "-719528", "null"]]

#guard Id.run do
  let .ok files := make textFirst custom | return false
  let .ok trace := readManifest textFirst custom limits files | return false
  let .eos := trace.termination | return false
  return files.map (·.path) == customPaths && trace.batches.map (·.rowCount) == [2, 1, 2, 1] &&
    trace.rows.head?.map (observed textFirst.toScan) ==
      some ["-7", "b:255,0", "b:99,97,102,195,169,47,98,108,117,101", "19782"]

#guard Id.run do
  let .ok [] := emit (dbOf dateFirst []) "source" dateFirst {} limits | return false
  let .ok trace := readManifest dateFirst {} limits [] | return false
  let .eos := trace.termination | return false
  return trace.batches.isEmpty

#guard match emit (dbOf dateFirst input) "missing" dateFirst {} limits,
    emit (dbOf dateFirst input) "source" textFirst {} limits with
  | .error .missingName, .error .schemaMismatch => true
  | _, _ => false

#guard match emit (dbOf dateFirst input) "source" dateFirst {}
    {limits with cuts.rowsPerGroup := 0} with
  | .error (.policy .zeroRowsPerGroup) => true
  | _ => false

#guard match emit (dbOf dateFirst input) "source" dateFirst {}
    {limits with cuts.maxGroupsPerFile := 1} with
  | .error (.cuts path .groupLimit) => path == defaultPaths[0]!
  | _ => false

#guard match emit (dbOf dateFirst input) "source" dateFirst {}
    {limits with writer.maxGroups := 1} with
  | .error (.parquet path .groupLimit) => path == defaultPaths[0]!
  | _ => false

-- The first bucket fits and the later leap bucket exceeds the native group cap.
#guard match emit (dbOf dateFirst (input.drop 1 ++ input.take 1)) "source" dateFirst {}
    {limits with writer.maxGroups := 1} with
  | .error (.parquet path .groupLimit) => path == defaultPaths[0]!
  | _ => false

-- A late routing error precedes the writer cap, even with an admitted prefix.
#guard
  let collision : Sample := ⟨none, none, none, some (utf8 "__HIVE_DEFAULT_PARTITION__")⟩
  match emit (dbOf dateFirst (input ++ [collision])) "source" dateFirst {} {limits with writer.maxGroups := 0} with
  | .error (.routing (.row 6 (.render (.nullMarkerCollision "label")))) => true
  | _ => false

private def project (layout : Schema) : Scan.Projection layout.toScan := by
  rcases layout with ⟨intName, byteName, ⟨day, label, order⟩⟩
  cases order <;> exact Scan.Projection.ofArray (#[3, 0, 2, 3] : Array (Fin 4))

private def keepDay (layout : Schema) (predicate : Int32 → Bool) :
    Scan.Predicate layout.keys.schema.toScan Value := by
  rcases layout with ⟨_, _, ⟨_, _, order⟩⟩
  cases order
  · exact fun cells => (cells (0 : Fin 2)).map predicate
  · exact fun cells => (cells (1 : Fin 2)).map predicate

private def keepLeap (layout : Schema) := keepDay layout (· == 19782)

private def observesPruning (layout : Schema) (options : PartitionPath.Options) : Bool := Id.run do
  let .ok files := make layout options | return false
  let .ok strict := readManifest layout options limits files | return false
  let .ok selected := readSelected layout options limits (project layout) (keepLeap layout) files | return false
  let .eos := selected.termination | return false
  let output := (project layout).schema
  return selected.batches.map (·.rowCount) == [2, 1] &&
    selected.rows.map (observed output) ==
      ((project layout).scan (fun row => keepLeap layout (TypedPartitions.partitionCells row)) strict.rows).map
        (observed output)

#guard observesPruning dateFirst {} && observesPruning textFirst custom

#guard Id.run do
  let .ok files := make dateFirst {} | return false
  let empty : Scan.Projection dateFirst.toScan := Scan.Projection.ofArray #[]
  let .ok trace := readSelected dateFirst {} limits empty (keepDay dateFirst (fun _ => true)) files | return false
  let .eos := trace.termination | return false
  return trace.batches.map (·.rowCount) == [2, 1, 1] && trace.rows.length == 4

-- Both false and unknown payloads can be unreadable. A retained error stays visible.
#guard Id.run do
  let .ok [a, b, c] := make dateFirst {} | return false
  let badB := {b with bytes := .empty}
  let badC := {c with bytes := .empty}
  let .ok strict := readManifest dateFirst {} limits [a, badB, badC] | return false
  let .readError (.open rejected _) := strict.termination | return false
  let .ok pruned := readSelected dateFirst {} limits (project dateFirst) (keepLeap dateFirst)
    [a, badB, badC] | return false
  let .eos := pruned.termination | return false
  let .ok kept := readSelected dateFirst {} limits (project dateFirst) (keepDay dateFirst (fun _ => true))
    [a, badB, badC, a] | return false
  let .readError (.open failed _) := kept.termination | return false
  return rejected == b.path && failed == c.path && kept.batches.map (·.rowCount) == [2, 1] &&
    pruned.rows.map (observed (project dateFirst).schema) == kept.rows.map (observed (project dateFirst).schema)

private def corruptSecond (layout : Schema) (file : File) : Option File := do
  let opened ← (Int32ByteArrayGroup.File.openFile limits.reader file.bytes layout.intField layout.byteField).toOption
  let group ← opened.projection.snapshot.groupAt 1
  let column ← group.columns.head?
  return {file with bytes := ⟨file.bytes.data.set! column.metadata.dataPageOffset.toNat 0⟩}

#guard Id.run do
  let .ok (a :: rest) := make textFirst custom | return false
  let some bad := corruptSecond textFirst a | return false
  let .ok trace := readSelected textFirst custom limits (project textFirst) (keepLeap textFirst) (bad :: rest) |
    return false
  let .readError (.source path (.parquet (.groupFailure 1 _))) := trace.termination | return false
  return path == a.path && trace.batches.map (·.rowCount) == [2]

#guard Id.run do
  let .ok (a :: rest) := make dateFirst {} | return false
  let invalid := {a with path := "day=2024-02-30/label=bad/part-0.parquet"}
  match readSelected dateFirst {} limits (project dateFirst) (fun _ => none) (a :: invalid :: rest) with
  | .error (.binding path (.conversion "day" (.invalidDate "2024-02-30"))) => return path == invalid.path
  | _ => return false

private def tableObservation (db : Packed String String Value) (name : String) :
    Option (List String × List (List String)) :=
  (Scan.observePacked db name).map fun table =>
    (List.ofFn fun i => (table.schema.kind i).1, table.rows.map (observed table.schema))

private def observesNamed (layout : Schema) (options : PartitionPath.Options) : Bool := Id.run do
  let .ok files := make layout options | return false
  let projection := project layout
  let keep := keepLeap layout
  let before := dbOf layout input
  let .ok trace := readSelected layout options limits projection keep files | return false
  let .ok after := importSelected before "selected" layout options limits projection keep files | return false
  return tableObservation after "selected" == some
    (List.ofFn fun i => (projection.schema.kind i).1, trace.rows.map (observed projection.schema)) &&
    tableObservation after "source" == tableObservation before "source" && (after "absent").isNone

#guard observesNamed dateFirst {} && observesNamed textFirst custom

#guard Id.run do
  let .ok files := make dateFirst {} | return false
  let projection : Scan.Projection dateFirst.toScan := Scan.Projection.ofArray #[]
  let before := dbOf dateFirst input
  let .ok after := importSelected before "zero" dateFirst {} limits projection (keepLeap dateFirst) files | return false
  return tableObservation after "zero" == some ([], [[], [], []]) &&
    tableObservation after "source" == tableObservation before "source"

#guard Id.run do
  let .ok files := make textFirst custom | return false
  let projection := project textFirst
  let .ok after := importSelected (dbOf textFirst input) "empty" textFirst custom limits projection
    (fun _ => none) files | return false
  return tableObservation after "empty" == some (["day", "n", "label", "day"], [])

#guard Id.run do
  let .ok (a :: rest) := make dateFirst {} | return false
  let invalid := {a with path := "day=2024-02-30/label=bad/part-0.parquet"}
  let before := dbOf dateFirst input
  let files := a :: invalid :: rest
  match importSelected before "selected" dateFirst {} limits (project dateFirst) (fun _ => none) files,
      importSelected before "source" dateFirst {} limits (project dateFirst) (fun _ => none) files with
  | .error (.openError (.admission (.binding path (.conversion "day" (.invalidDate "2024-02-30"))))),
    .error .nameConflict => return path == invalid.path
  | _, _ => return false

-- The completed first group of a failing retained file cannot install a table.
#guard Id.run do
  let .ok (a :: rest) := make textFirst custom | return false
  let some damaged := corruptSecond textFirst a | return false
  let files := damaged :: rest
  let projection := project textFirst
  let keep := keepLeap textFirst
  let .ok trace := readSelected textFirst custom limits projection keep files | return false
  let .readError (expected@(.source path (.parquet (.groupFailure 1 _)))) := trace.termination | return false
  match importSelected (dbOf textFirst input) "selected" textFirst custom limits projection keep files with
  | .error (.readError (.runtime cause)) =>
    return path == a.path && trace.batches.map (·.rowCount) == [2] && decide (cause = expected)
  | _ => return false

#guard Id.run do
  let .ok (a :: rest) := make dateFirst {} | return false
  let projection := project dateFirst
  let .ok trace := readSelected dateFirst {} limits projection (keepLeap dateFirst) (a :: rest) | return false
  let closed := {trace with termination := .closed}
  match importResult (dbOf dateFirst input) "selected" (.ok closed) with
  | .error .closed => return trace.rows.length == 3
  | _ => return false

#print axioms namedRows_of_observe
#print axioms fileInput_rows
#print axioms FileMatches.cutBounds
#print axioms emit_routing_error
#print axioms emit_readback

#print axioms Manifest.scanFile_termination_eq_full
#print axioms Manifest.scan_equivalent_thenFilter
#print axioms scanSelectedPaths_admission_error
#print axioms scanSelectedPaths_eq_scan_filter
#print axioms readSelected_eq_postfilter
#print axioms emit_readSelected
#print axioms scanSelectedPaths_first_retained_error

#print axioms Silmaril.Formats.Relational.NamedTable.FromHiveDateUtf8.importResult_outcome
#print axioms Silmaril.Formats.Relational.NamedTable.FromHiveDateUtf8.importSelected_ok_iff
#print axioms Silmaril.Formats.Relational.NamedTable.FromHiveDateUtf8.importSelected_observe
#print axioms Silmaril.Formats.Relational.NamedTable.FromHiveDateUtf8.emit_importSelected

private def tracedResolve (run : String) (files : List File) (path : String) : Except Unit Bytes :=
  dbg_trace s!"open\t{run}\t{path}"
  resolve files path

private def writePruning (root : System.FilePath) (name : String) (layout : Schema)
    (options : PartitionPath.Options) (files : List File) : IO Unit := do
  let projection := project layout
  let keep := keepLeap layout
  let paths := files.map (·.path)
  let .ok strict := scanPaths (int32 := layout.intField) (byteArray := layout.byteField) (keys := layout.keys)
    options limits.reader (tracedResolve (name ++ "-strict") files) projection keep paths |
    throw (IO.userError "strict projected ingress failed")
  let .ok pruned := scanSelectedPaths layout options limits (tracedResolve (name ++ "-pruned") files)
    projection keep paths | throw (IO.userError "pruned ingress failed")
  let .eos := strict.termination | throw (IO.userError "strict comparison did not reach EOS")
  let .eos := pruned.termination | throw (IO.userError "pruned comparison did not reach EOS")
  unless strict.rows.map (observed projection.schema) == pruned.rows.map (observed projection.schema) &&
      strict.batches.map (·.rowCount) == pruned.batches.map (·.rowCount) do
    throw (IO.userError "strict and pruned native observations differ")
  let batches := pruned.batches.flatMap fun batch =>
    toString batch.rowCount :: batch.toRows.map (fun row => String.intercalate "\t" (observed projection.schema row))
  IO.FS.writeFile (root / "pruned.tsv") (String.intercalate "\n" batches ++ "\n")

private def writeNamed (root : System.FilePath) (layout : Schema)
    (options : PartitionPath.Options) (files : List File) : IO Unit := do
  let before := dbOf layout input
  let keep := keepLeap layout
  let .ok after := importSelected before "selected" layout options limits (project layout) keep files |
    throw (IO.userError "native named import failed")
  let some (labels, rows) := tableObservation after "selected" |
    throw (IO.userError "named import did not install the selected table")
  unless tableObservation after "source" == tableObservation before "source" do
    throw (IO.userError "named import changed a different table")
  let lines := String.intercalate "\t" labels :: rows.map (String.intercalate "\t")
  IO.FS.writeFile (root / "db.tsv") (String.intercalate "\n" lines ++ "\n")
  let zero : Scan.Projection layout.toScan := Scan.Projection.ofArray #[]
  let .ok afterZero := importSelected before "zero" layout options limits zero keep files |
    throw (IO.userError "zero-column named import failed")
  let some (zeroLabels, zeroRows) := tableObservation afterZero "zero" |
    throw (IO.userError "zero-column named import did not install a table")
  unless zeroLabels.isEmpty && zeroRows.all List.isEmpty do
    throw (IO.userError "zero-column table has cells")
  IO.FS.writeFile (root / "db-zero-count.txt") s!"{zeroRows.length}\n"

private def writeFixture (root : System.FilePath) (name : String) (layout : Schema)
    (options : PartitionPath.Options) (pruning named : Bool) : IO Unit := do
  let root := root / name
  let .ok files := make layout options | throw (IO.userError "paired Hive emission failed")
  let .ok trace := readManifest layout options limits files | throw (IO.userError "paired Hive ingress failed")
  let .eos := trace.termination | throw (IO.userError "paired Hive read did not reach EOS")
  for file in files do
    let path := root / file.path
    if let some parent := path.parent then IO.FS.createDirAll parent
    IO.FS.writeBinFile path file.bytes.data
  IO.FS.writeFile (root / "inventory.txt") (String.intercalate "\n" (files.map (·.path)) ++ "\n")
  let batches := trace.batches.flatMap fun batch =>
    toString batch.rowCount :: batch.toRows.map (fun row => String.intercalate "\t" (observed layout.toScan row))
  IO.FS.writeFile (root / "batches.tsv") (String.intercalate "\n" batches ++ "\n")
  if pruning then writePruning root name layout options files
  if named then writeNamed root layout options files

public def runWriterChecks (args : List String) : IO Unit := do
  let (root, pruning, named) ← match args with
    | [root] => pure (System.FilePath.mk root, false, false)
    | ["pruning", root] => pure (System.FilePath.mk root, true, false)
    | ["named", root] => pure (System.FilePath.mk root, true, true)
    | _ => throw (IO.userError "usage: Checks.lean [pruning|named] <fixture-root>")
  writeFixture root "date-first" dateFirst {} pruning named
  writeFixture root "text-first" textFirst custom pruning named

end Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter

public def main : List String → IO Unit := Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.runWriterChecks
