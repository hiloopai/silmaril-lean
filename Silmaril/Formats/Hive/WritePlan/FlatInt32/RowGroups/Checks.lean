module

import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Thms
import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.Thms
import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc.Thms
import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.Pruning.Thms
import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc.Projection.Thms
import Silmaril.Formats.Parquet.Snapshot.Footer.Thms
meta import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc.Defs
meta import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.Pruning.Defs
meta import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc.Projection.Defs

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

private def trace (options : PartitionPath.Options) :=
  Events.scanPruned leaf partitions options decode policy limits keep

private def batchShape {schema : Scan.Schema String Unit} (result : Events.Trace schema String) :=
  result.batches.map fun batch => (batch.position.fileIndex, batch.position.groupIndex, batch.columns.rowCount)

#guard Id.run do
  let .ok files := make {} | return false
  let .ok result := trace {} files | return false
  let .eos := result.toArrow.termination | return false
  return batchShape result == [(0, 0, 2), (0, 1, 1), (2, 0, 2), (2, 1, 1)] &&
    result.batches.map (fun batch => observe batch.columns.toRows) ==
      [[(some 10, some 3), (some 11, some 3)], [(some 12, some 3)], [(some 4, none), (none, none)], [(some 7, none)]] &&
    result.finish.toOption.map observe == (prune {} files).toOption.map observe

#guard Id.run do
  let .ok files := make customMarker | return false
  let .ok result := trace customMarker files | return false
  return result.batches.map (fun batch => batch.position.path) ==
    ["key=3/part-0.parquet", "key=3/part-0.parquet", "key=null%2F%3D/part-0.parquet", "key=null%2F%3D/part-0.parquet"] &&
    result.finish.toOption.map observe == some selected

#guard Id.run do
  let .ok (first :: skipped :: _) := make {} | return false
  let .ok result := trace {} [first, skipped, first] | return false
  return batchShape result == [(0, 0, 2), (0, 1, 1), (2, 0, 2), (2, 1, 1)] &&
    result.batches.all (fun batch => batch.position.path == first.path)

#guard Id.run do
  let .ok files := make {} | return false
  let .ok empty := trace {} [] | return false
  let .ok rejected := Events.scanPruned leaf partitions {} decode policy limits (fun _ => none) files | return false
  let .eos := empty.toArrow.termination | return false
  let .eos := rejected.toArrow.termination | return false
  return empty.batches.isEmpty && rejected.batches.isEmpty

#guard Id.run do
  let .ok (first :: skipped :: target :: later :: _) := make {} | return false
  let some damaged := damage target 1 | return false
  let invalid := {later with path := "../" ++ later.path}
  let .ok result := trace {} [first, skipped, damaged, invalid] | return false
  let .readError (.file 2 path (.payload (.parquet (.decode 1 (.profile (.page (.header (.missingField 1)))))))) :=
    result.toArrow.termination | return false
  return path == target.path && batchShape result == [(0, 0, 2), (0, 1, 1), (2, 0, 2)] &&
    observe result.rows == selected.take 5

#guard Id.run do
  let .ok (first :: skipped :: target :: rest) := make {} | return false
  let some damaged := damage skipped 1 | return false
  let .ok result := trace {} (first :: damaged :: target :: rest) | return false
  let .eos := result.toArrow.termination | return false
  return result.finish.toOption.map observe == some selected

#guard Id.run do
  let .ok (first :: skipped :: _) := make {} | return false
  let bad := {skipped with path := "../" ++ skipped.path}
  let .ok result := Events.scanPruned leaf partitions {} decode policy limits (fun _ => some false) [first, bad] |
    return false
  let .readError (.file 1 path (.path (.path _ .invalidSegment))) := result.toArrow.termination | return false
  return path == bad.path && result.batches.isEmpty

#guard match Events.scanPruned leaf partitions {} decode {policy with rowsPerGroup := 0} limits keep [] with
  | .error (.policy .zeroRowsPerGroup) => true
  | _ => false

#guard Id.run do
  let .ok files := make {} | return false
  let .ok result := trace {} files | return false
  let zero : Scan.Projection expected := ⟨0, fun i => nomatch i⟩
  let repeated : Scan.Projection expected := ⟨3, fun i => if i.val = 1 then (0 : Fin 2) else (1 : Fin 2)⟩
  let projected := result.project repeated
  return batchShape (result.project zero) == batchShape result && (result.project zero).rows.length == 6 &&
    batchShape projected == batchShape result && projected.rows.map (fun row => List.ofFn row) ==
      selected.map (fun (payload, key) => [key, payload, key])

open FlatProjection.Composition

private def ipcLimits : Arrow.MixedFlat.Limits := {}
private def keyPosition : Fin partitions.toScan.width := (0 : Fin 1)

private def convertIpc (options : PartitionPath.Options) (keys : List (Fin partitions.toScan.width))
    (ipc : Arrow.MixedFlat.Limits) := Events.ToIpc.convert leaf partitions options decode policy limits keep keys ipc

#guard Id.run do
  let .ok files := make {} | return false
  let .ok source := trace {} files | return false
  let .ok wire := convertIpc {} [] ipcLimits files | return false
  let .ok ⟨signature, pulled⟩ := Arrow.MixedFlat.Stream.Events.readAll ipcLimits wire | return false
  let .eos := pulled.termination | return false
  return List.ofFn (fun i => (signature.kind i).1) == [Events.ToIpc.field "payload"] &&
    pulled.batches.map (·.rowCount) == [2, 1, 2, 1] &&
    Ipc.readEvents ipcLimits wire == some (Events.ToIpc.observeTrace leaf partitions [] source)

#guard Id.run do
  let .ok files := make customMarker | return false
  let .ok source := trace customMarker files | return false
  let .ok wire := convertIpc customMarker [keyPosition] ipcLimits files | return false
  let some observed := Ipc.readEvents ipcLimits wire | return false
  return observed.fields == [Events.ToIpc.field "payload", Events.ToIpc.field "key"] &&
    observed == Events.ToIpc.observeTrace leaf partitions [keyPosition] source

#guard Id.run do
  let .ok files := make {} | return false
  let .ok wire := Events.ToIpc.convert leaf partitions {} decode policy limits (fun _ => none)
    [keyPosition] ipcLimits files | return false
  let some observed := Ipc.readEvents ipcLimits wire | return false
  return observed.fields == [Events.ToIpc.field "payload", Events.ToIpc.field "key"] && observed.batches.isEmpty

#guard Id.run do
  let .ok (first :: skipped :: target :: rest) := make {} | return false
  let .ok clean := convertIpc {} [keyPosition] ipcLimits (first :: skipped :: target :: rest) | return false
  let some damaged := damage skipped 1 | return false
  let .ok output := convertIpc {} [keyPosition] ipcLimits (first :: damaged :: target :: rest) | return false
  return output.toList == clean.toList

#guard Id.run do
  let .ok files := make {} | return false
  let denied := {ipcLimits with observation.ipc.batches := 0}
  match convertIpc {} [] denied files with
  | .error (.writer (.ipc (.limit .batches))) => return true
  | _ => return false

#guard Id.run do
  let .ok (first :: skipped :: target :: rest) := make {} | return false
  let some damaged := damage target 1 | return false
  let denied := {ipcLimits with observation.ipc.batches := 0}
  match convertIpc {} [keyPosition] denied (first :: skipped :: damaged :: rest) with
  | .error (.scan (.file 2 path (.payload (.parquet (.decode 1 (.profile (.page (.header (.missingField 1))))))))) =>
    return path == target.path
  | _ => return false

#guard match Events.ToIpc.convert leaf partitions {} decode {policy with rowsPerGroup := 0} limits keep []
    {ipcLimits with observation.ipc.fields := 0} [] with
  | .error (.scan (.policy .zeroRowsPerGroup)) => true
  | _ => false

private def unpruned (options : PartitionPath.Options) :=
  Events.scanUnpruned leaf partitions options decode policy limits

private def restrict (options : PartitionPath.Options) (files : List File) (whole : Events.Trace expected String) :=
  whole.restrict (Events.keepOccurrence partitions options decode keep files)

private def batchValues (result : Events.Trace expected String) :=
  result.batches.map fun batch => (batch.position, batch.columns.rowCount, observe batch.columns.toRows)

private def repeatFiles : List File → Option (List File)
  | [first, rejected, nulls, last] => some [nulls, rejected, first, nulls, last, first]
  | _ => none

#guard Id.run do
  let .ok original := make {} | return false
  let some files := repeatFiles original | return false
  let .ok whole := unpruned {} files | return false
  let .ok pruned := trace {} files | return false
  let reference := restrict {} files whole
  return whole.batches.length == 12 && pruned.result.toOption.isSome && reference.result.toOption.isSome &&
    batchShape pruned == [(0, 0, 2), (0, 1, 1), (2, 0, 2), (2, 1, 1),
      (3, 0, 2), (3, 1, 1), (5, 0, 2), (5, 1, 1)] &&
    batchValues pruned == batchValues reference

#guard Id.run do
  let .ok original := make customMarker | return false
  let some files := repeatFiles original | return false
  let .ok whole := unpruned customMarker files | return false
  let .ok pruned := trace customMarker files | return false
  let .ok wire := convertIpc customMarker [keyPosition] ipcLimits files | return false
  let reference := restrict customMarker files whole
  return whole.result.toOption.isSome && batchValues pruned == batchValues reference &&
    (pruned.batches.filter (fun batch => batch.position.path == "key=null%2F%3D/part-0.parquet")).length == 4 &&
    Ipc.readEvents ipcLimits wire == some (Events.ToIpc.observeTrace leaf partitions [keyPosition] reference)

-- A selected failure ends the shared prefix before the later rejected damage.
#guard Id.run do
  let .ok (first :: skipped :: target :: _) := make {} | return false
  let some selectedDamage := damage target 1 | return false
  let some unreachableDamage := damage skipped 1 | return false
  let files := [first, skipped, selectedDamage, unreachableDamage]
  let .ok whole := unpruned {} files | return false
  let .ok pruned := trace {} files | return false
  let .error (actual@(.file 2 _ (.payload (.parquet (.decode 1 _))))) := pruned.result | return false
  let reference := restrict {} files whole
  let .error expected := reference.result | return false
  return actual == expected && batchValues pruned == batchValues reference &&
    batchShape pruned == [(0, 0, 2), (0, 1, 1), (2, 0, 2)]

-- Reached rejected damage distinguishes a decode-all trace from skip-open pruning.
#guard Id.run do
  let .ok (first :: skipped :: target :: _) := make {} | return false
  let some rejectedDamage := damage skipped 1 | return false
  let files := [rejectedDamage, first, target]
  let .ok whole := unpruned {} files | return false
  let .ok pruned := trace {} files | return false
  let reference := restrict {} files whole
  let .error (.file 0 _ (.payload (.parquet (.decode 1 _)))) := reference.result | return false
  return reference.batches.isEmpty && pruned.result.toOption.isSome &&
    batchShape pruned == [(1, 0, 2), (1, 1, 1), (2, 0, 2), (2, 1, 1)]

#guard Id.run do
  let .ok (first :: skipped :: _) := make {} | return false
  let files := [first, {skipped with path := "../" ++ skipped.path}]
  let rejects : Scan.Predicate partitions.toScan Cell := fun _ => none
  let .ok whole := unpruned {} files | return false
  let .ok pruned := Events.scanPruned leaf partitions {} decode policy limits rejects files | return false
  let reference := whole.restrict (Events.keepOccurrence partitions {} decode rejects files)
  let .error (actual@(.file 1 _ (.path (.path _ .invalidSegment)))) := pruned.result | return false
  let .error expected := reference.result | return false
  return actual == expected && pruned.batches.isEmpty && reference.batches.isEmpty

private def wideKeys : List (Fin partitions.toScan.width) := [keyPosition, keyPosition]
private def repeatedSelection : List (Fin 3) := [2, 0, 1, 2]

private def projectIpc (options : PartitionPath.Options) (selection : List (Fin 3))
    (limitsIpc : Arrow.MixedFlat.Limits) :=
  Events.ToIpc.convertProjected leaf partitions options decode policy limits keep wideKeys selection limitsIpc

#guard Id.run do
  let .ok original := make customMarker | return false
  let some files := repeatFiles original | return false
  let .ok wideWire := convertIpc customMarker wideKeys ipcLimits files | return false
  let .ok projectedWire := projectIpc customMarker repeatedSelection ipcLimits files | return false
  let some wide := Ipc.readEvents ipcLimits wideWire | return false
  let some projected := Ipc.readEvents ipcLimits projectedWire | return false
  return wide.fields.map (·.name) == ["payload", "key", "key"] &&
    projected.fields.map (·.name) == ["key", "payload", "key", "key"] &&
    projected.batches.map Prod.fst == [2, 1, 2, 1, 2, 1, 2, 1] &&
    Ipc.projectEvents (repeatedSelection.map Fin.val) wide == some projected &&
    (Ipc.projectEvents [3] wide).isNone

#guard Id.run do
  let .ok original := make {} | return false
  let some files := repeatFiles original | return false
  let zeroFields := {ipcLimits with observation.ipc.fields := 0}
  let .ok wideWire := convertIpc {} wideKeys ipcLimits files | return false
  let .ok projectedWire := projectIpc {} [] zeroFields files | return false
  let some wide := Ipc.readEvents ipcLimits wideWire | return false
  let some projected := Ipc.readEvents zeroFields projectedWire | return false
  return projected.fields.isEmpty && projected.batches.all (fun batch => batch.2.isEmpty) &&
    projected.batches.map Prod.fst == [2, 1, 2, 1, 2, 1, 2, 1] && Ipc.projectEvents [] wide == some projected

-- Repeated output positions can exhaust a cap that admits the input layout.
#guard Id.run do
  let .ok files := make {} | return false
  let threeFields := {ipcLimits with observation.ipc.fields := 3}
  let .ok _ := convertIpc {} wideKeys threeFields files | return false
  match projectIpc {} repeatedSelection threeFields files with
  | .error (.writer (.ipc (.limit .fields))) => return true
  | _ => return false

#print axioms planCuts_exact
#print axioms splitSlots_exact
#print axioms readPayload_footer
#print axioms FileMatches.counts
#print axioms restore_emit
#print axioms restorePruned_eq_filter
#print axioms Snapshot.check_footer

#print axioms Events.Trace.toArrow_rows
#print axioms Events.finish_scanPruned
#print axioms Events.scanFile_batches
#print axioms Events.scanFile_first_error
#print axioms Events.scanPruned_first_error
#print axioms Events.Trace.project_positions
#print axioms Events.Trace.project_finish

#print axioms Events.ToIpc.fields_exact
#print axioms Events.ToIpc.convert_readback
#print axioms Events.ToIpc.convert_scan_error
#print axioms Events.scanPruned_eq_restrict
#print axioms Events.ToIpc.convert_readback_restrict
#print axioms Events.ToIpc.convertAt_readback
#print axioms Events.ToIpc.fields_width
#print axioms Events.ToIpc.projected_fields_width
#print axioms Events.ToIpc.project_observeTrace
#print axioms Events.ToIpc.convertProjected_readback_restrict

private def showCell (cell : Option Int32) : String := cell.map (fun value => toString value.toInt) |>.getD "null"

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
  let selected := (observe rows).map fun (payload, key) => showCell payload ++ "\t" ++ showCell key
  IO.FS.writeFile (directory / "manifest.tsv") (String.intercalate "\n" manifest ++ "\n")
  IO.FS.writeFile (directory / "selected.tsv") (String.intercalate "\n" selected ++ "\n")

private def writeTrace (path : System.FilePath) (result : Events.Trace expected String) : IO Unit := do
  let .eos := result.toArrow.termination | throw (IO.userError "manifest event read failed")
  let batches := result.batches.map fun batch =>
    let pos := batch.position
    let cells := (observe batch.columns.toRows).map fun (payload, key) => showCell payload ++ ":" ++ showCell key
    String.intercalate "\t" [toString pos.fileIndex, pos.path, toString pos.groupIndex,
      toString batch.columns.rowCount, String.intercalate "," cells]
  IO.FS.writeFile path (String.intercalate "\n" (batches ++ ["eos"]) ++ "\n")

private def writeEvents (root : System.FilePath) (name : String) (options : PartitionPath.Options) : IO Unit := do
  let .ok files := make options | throw (IO.userError "multi-group native emit failed")
  let .ok result := trace options files | throw (IO.userError "manifest event open failed")
  writeTrace (root / name / "events.tsv") result

private def writeIpc (root : System.FilePath) (name : String) (options : PartitionPath.Options) : IO Unit := do
  let .ok files := make options | throw (IO.userError "multi-group native emit failed")
  let .ok payload := convertIpc options [] ipcLimits files | throw (IO.userError "payload IPC emit failed")
  let .ok partitioned := convertIpc options [keyPosition] ipcLimits files | throw (IO.userError "partition IPC emit failed")
  let .ok empty := Events.ToIpc.convert leaf partitions options decode policy limits (fun _ => none)
    [keyPosition] ipcLimits files | throw (IO.userError "schema-only IPC emit failed")
  let directory := root / name
  IO.FS.writeBinFile (directory / "payload.arrows") payload.toByteArray
  IO.FS.writeBinFile (directory / "partitioned.arrows") partitioned.toByteArray
  IO.FS.writeBinFile (directory / "empty.arrows") empty.toByteArray

private def writeRepeat (root : System.FilePath) (name : String) (options : PartitionPath.Options) : IO Unit := do
  let .ok original := make options | throw (IO.userError "multi-group native emit failed")
  let some files := repeatFiles original | throw (IO.userError "unexpected repeat fixture file layout")
  let .ok whole := unpruned options files | throw (IO.userError "unpruned repeat open failed")
  let .ok pruned := trace options files | throw (IO.userError "pruned repeat open failed")
  let .ok wire := convertIpc options [keyPosition] ipcLimits files | throw (IO.userError "repeat IPC emit failed")
  let directory := root / name
  IO.FS.writeFile (directory / "repeat-paths.txt") (String.intercalate "\n" (files.map (·.path)) ++ "\n")
  writeTrace (directory / "repeat-unpruned.tsv") whole
  writeTrace (directory / "repeat-pruned.tsv") pruned
  IO.FS.writeBinFile (directory / "repeat.arrows") wire.toByteArray

private def writeProjection (root : System.FilePath) (name : String) (options : PartitionPath.Options) : IO Unit := do
  let .ok original := make options | throw (IO.userError "multi-group native emit failed")
  let some files := repeatFiles original | throw (IO.userError "unexpected projection fixture file layout")
  let .ok wide := convertIpc options wideKeys ipcLimits files | throw (IO.userError "wide IPC emit failed")
  let .ok projected := projectIpc options repeatedSelection ipcLimits files | throw (IO.userError "projected IPC emit failed")
  let .ok empty := projectIpc options [] {ipcLimits with observation.ipc.fields := 0} files |
    throw (IO.userError "zero-width IPC emit failed")
  let directory := root / name
  IO.FS.writeBinFile (directory / "project-wide.arrows") wide.toByteArray
  IO.FS.writeBinFile (directory / "project-repeat.arrows") projected.toByteArray
  IO.FS.writeBinFile (directory / "project-zero.arrows") empty.toByteArray

public def main (args : List String) : IO Unit := do
  let (root, mode) ← match args with
    | [root] => pure (root, "")
    | ["events", root] => pure (root, "events")
    | ["ipc", root] => pure (root, "ipc")
    | ["repeat", root] => pure (root, "repeat")
    | ["projection", root] => pure (root, "projection")
    | _ => throw (IO.userError "expected a fixture output directory, optionally preceded by events, ipc, repeat or projection")
  writeFixture root "default" {}
  writeFixture root "custom" customMarker
  if mode == "events" || mode == "ipc" || mode == "repeat" || mode == "projection" then
    writeEvents root "default" {}
    writeEvents root "custom" customMarker
  if mode == "ipc" || mode == "repeat" || mode == "projection" then
    writeIpc root "default" {}
    writeIpc root "custom" customMarker
  if mode == "repeat" || mode == "projection" then
    writeRepeat root "default" {}
    writeRepeat root "custom" customMarker
  if mode == "projection" then
    writeProjection root "default" {}
    writeProjection root "custom" customMarker

end Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups

public def main := Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.main
