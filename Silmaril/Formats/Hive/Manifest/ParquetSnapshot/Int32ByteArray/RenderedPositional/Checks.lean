module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.RenderedPositional.Thms
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Defs
import Silmaril.Formats.Hive.Manifest.Inventory.Thms
import Silmaril.Formats.Hive.PartitionPath.Positional.Render.Thms
import Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.Thms
import Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.ToCsv.Thms
import Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv.Thms
import Silmaril.Formats.Relational.NamedTable.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.Defs
meta import Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.ToCsv.Defs
meta import Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.FromCsv.Defs
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.RenderedPositional.Defs
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Defs

namespace Silmaril.Formats.Hive.Manifest.RenderedPositional

open Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Parquet Silmaril.Relational
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)
open TypedPartitions (PartitionSchema)
open PartitionPath (Partition)
open PartitionPath.Positional (RenderLimits)

private def ordinal : Field := ⟨"ordinal", .required⟩
private def payload : Field := ⟨"payload", .optional⟩
private def physical := Int32ByteArrayGroup.File.schema ordinal payload
private def partitions : PartitionSchema Kind :=
  ⟨#[⟨"year", .int32 .optional, .reject⟩, ⟨"region", .byteArray .optional, .reject⟩]⟩
private def admission : Inventory.Limits := ⟨8, 160⟩
private def renderLimits : RenderLimits := ⟨128, 64⟩
private def keys := ["region", "year"]
private def region := "café/blue=%5F:west\\x"
private def canonical := "caf%C3%A9%2Fblue%3D%255F%3Awest%5Cx/7/part.parquet"
private def lowerEscape := "caf%C3%A9%2fblue%3D%255F%3Awest%5Cx/7/B%2Eparquet"
private def zebra := "zebra/7/z.parquet"
private def pruned := "apart/8/skip.parquet"
private def late := "zz-later/7/late.parquet"
private def controls := "folder/_common_metadata"

private def entries (region year : String) : Partition :=
  [("region", some region), ("year", some year)]

private def path (region year leaf : String) :=
  (PartitionPath.Positional.render renderLimits keys .uri {} (entries region year)).map
    (fun directory => directory ++ "/" ++ leaf)

private def listing : Except PartitionPath.Positional.RenderError (List String) := do
  let first ← path region "7" "part.parquet"
  let last ← path "zebra" "7" "z.parquet"
  let skip ← path "apart" "8" "skip.parquet"
  return [last, first, controls, skip, lowerEscape, first]

private def fixture : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-int32-byte-array-file/empty-middle-v2.parquet"⟩

private def lookup (path : String) : Except String Bytes :=
  if path == canonical || path == lowerEscape || path == zebra then .ok fixture
  else if path == late then .ok ⟨fixture.data.set! 122 6⟩
  else .error "literal snapshot missing"

private def keep : Scan.Predicate partitions.toScan Value :=
  fun row => (row ⟨0, by decide⟩).map (· == (7 : Int32))
private def projection : Scan.Projection (partitions.extend physical) :=
  Scan.Projection.ofArray #[⟨3, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨1, by decide⟩]
private def zero : Scan.Projection (partitions.extend physical) := Scan.Projection.ofArray #[]

private abbrev RuntimeError := FileError (Int32ByteArray.Error String)
private abbrev ProjectedRow := Option Bytes × Option Int32 × Option Int32 × Option Bytes × Option Bytes

private def expectedRows (value : String) : List ProjectedRow :=
  let text : Option Bytes := some ⟨value.toUTF8⟩
  let ordinals : List Int32 := [-2147483648, 0, 17, 2147483647, -1]
  let payloads := [none, some Bytes.empty, some (Bytes.ofList [0xFF, 0]),
    some (Bytes.ofList [0x80]), some (Bytes.ofList [120, 121])]
  ordinals.zipWith (fun id bytes => (text, some id, some 7, text, bytes)) payloads

private def counts : List Nat := [3, 0, 2, 3, 0, 2, 3, 0, 2, 3, 0, 2]
private def rows := expectedRows region ++ expectedRows region ++ expectedRows region ++ expectedRows "zebra"

private def run (budget : Nat) (paths : List String)
    (maxDirectoryBytes : Nat := renderLimits.maxDirectoryBytes) :=
  scan (int32 := ordinal) (byteArray := payload) admission maxDirectoryBytes keys .uri {}
    Int32ByteArray.Ingress.convert paths {} lookup projection keep budget

private def projectedRows (table : Scan.Table projection.schema Value) : List ProjectedRow :=
  table.map fun row =>
    ((row ⟨0, by decide⟩ : Option Bytes), (row ⟨1, by decide⟩ : Option Int32),
      (row ⟨2, by decide⟩ : Option Int32), (row ⟨3, by decide⟩ : Option Bytes),
      (row ⟨4, by decide⟩ : Option Bytes))

private def observes (budget : Nat) (extra : List String) (expectedCounts : List Nat)
    (expected : List ProjectedRow) (termination : Events.Termination RuntimeError) : Bool := Id.run do
  let .ok paths := listing | return false
  let .ok trace := run budget (paths ++ extra) | return false
  return trace.batches.map (·.rowCount) == expectedCounts &&
    projectedRows trace.rows == expected && decide (trace.termination = termination)

private def lateCause : RuntimeError :=
  .source late (.parquet (.groupFailure 2 (.byteArray (.page 2 1 "payload" 0 108 (.encoding 3)))))

private def lateFailure : Events.Termination RuntimeError := .readError lateCause

#guard listing.toOption == some [zebra, canonical, controls, pruned, lowerEscape, canonical]
#guard (path "zz-later" "7" "late.parquet").toOption == some late
#guard observes 19 [] counts rows .closed
#guard observes 20 [] counts rows .eos
#guard fixture.data[122]! == 0
#guard observes 23 [late] (counts ++ [3, 0]) (rows ++ (expectedRows "zz-later").take 3) .closed
#guard observes 24 [late] (counts ++ [3, 0]) (rows ++ (expectedRows "zz-later").take 3) lateFailure

#guard match listing with
  | .error _ => false
  | .ok paths =>
    match scan (int32 := ordinal) (byteArray := payload) admission renderLimits.maxDirectoryBytes keys .uri {}
        Int32ByteArray.Ingress.convert paths {} lookup zero keep 20 with
    | .error _ => false
    | .ok trace => trace.batches.map (·.rowCount) == counts && trace.rows.length == 20 &&
        decide (trace.termination = .eos)

#guard match listing with
  | .error _ => false
  | .ok paths =>
    match prepareOrderedInventoryWith physical partitions admission
        (PartitionPath.Positional.parse renderLimits.maxDirectoryBytes keys .uri) {}
        Int32ByteArray.Ingress.convert paths with
    | .error _ => false
    | .ok files =>
      let trace := scanInt32ByteArraySnapshotsBounded {} lookup projection keep 20 files
      files.map (·.path.declared) == [pruned, canonical, canonical, lowerEscape, zebra] &&
        trace.batches.isEmpty &&
        decide (trace.termination = .readError (.open pruned (.lookup "literal snapshot missing")))

#guard match run 0 [controls, pruned] 6 with
  | .ok _ => false
  | .error reason => reason == .entry 1 (.partitionPath pruned (.directoryByteLimit 6 7))

#guard
  let bad := "apart/not-int/skip.parquet"
  match run 0 [controls, bad] with
  | .ok _ => false
  | .error reason => reason == .entry 1 (.binding bad (.conversion "year" (.invalidInt32 "not-int")))

#guard
  let marker := "__HIVE_DEFAULT_PARTITION__/7/part.parquet"
  match run 0 [marker] with
  | .ok _ => false
  | .error reason => reason == .entry 0 (.partitionPath marker (.nullMarkerCollision "region"))

#print axioms scan_eq_reference
#print axioms PartitionPath.Positional.parse_of_rendered_spelling
#print axioms prepareInventoryReferenceWithFileParser_congr


open Silmaril.Formats.Relational
open NamedTable.FromRenderedPositional (Database importScan)

private def storedSchema : Scan.Schema String Kind := ⟨0, Fin.elim0⟩

private def database : Database String := fun name =>
  if name == "other" then some ⟨storedSchema, [fun i => nomatch i]⟩ else none

private def load (name : String) (selected : Scan.Projection (partitions.extend physical))
    (budget : Nat) (paths : List String) :=
  importScan (int32 := ordinal) (byteArray := payload) database name admission
    renderLimits.maxDirectoryBytes keys .uri {} Int32ByteArray.Ingress.convert paths {} lookup selected keep budget

private def otherPreserved (loaded : Database String) : Bool :=
  match Scan.observePacked loaded "other", Scan.observePacked loaded "unrelated" with
  | some table, none => table.schema.width == 0 && table.rowCount == 1
  | _, _ => false

private def observesLoadedProjection (loaded : Database String) (name : String) : Bool := Id.run do
  let some table := Scan.observePacked loaded name | return false
  if same : NamedTable.schemaMatches projection.schema table.schema = true then
    let exactSchema := (NamedTable.schemaMatches_eq_true_iff _ _).mp same
    let actual : Scan.Table projection.schema Value :=
      cast (congrArg (fun schema => Scan.Table schema Value) exactSchema.symm) table.rows
    return projectedRows actual == rows && table.rowCount == 20 && otherPreserved loaded
  else return false

#guard Id.run do
  let .ok paths := listing | return false
  let .ok loaded := load "dest" projection 20 paths | return false
  return observesLoadedProjection loaded "dest"

#guard Id.run do
  let .ok paths := listing | return false
  let .ok loaded := load "dest" zero 20 paths | return false
  let some table := Scan.observePacked loaded "dest" | return false
  return table.schema.width == 0 && table.rowCount == 20 && otherPreserved loaded

#guard match load "dest" zero 0 [] with
  | .ok loaded =>
    match Scan.observePacked loaded "dest" with
    | some table => table.schema.width == 0 && table.rowCount == 0 && otherPreserved loaded
    | none => false
  | .error _ => false

#guard Id.run do
  let .ok paths := listing | return false
  let .error .closed := load "dest" projection 19 paths | return false
  return true

#guard Id.run do
  let .ok paths := listing | return false
  let .error (.readError (.runtime cause)) := load "dest" projection 24 (paths ++ [late]) | return false
  return decide (cause = lateCause)

#guard
  let bad := "apart/not-int/skip.parquet"
  match load "dest" projection 0 [controls, bad] with
  | .error (.openError (.admission reason)) =>
    reason == .entry 1 (.binding bad (.conversion "year" (.invalidInt32 "not-int")))
  | _ => false

#guard match load "other" projection 0 ["../invalid.parquet"] with
  | .error .nameConflict => true
  | _ => false

#print axioms NamedTable.FromRenderedPositional.importResult_outcome
#print axioms NamedTable.FromRenderedPositional.importScan_ok_iff
#print axioms NamedTable.FromRenderedPositional.importScan_observe
#print axioms NamedTable.FromRenderedPositional.importScan_eq_reference


open NamedTable.FromRenderedPositional

private def exportCsv (selected : Scan.Projection (partitions.extend physical))
    (budget maxBytes : Nat) (paths : List String) :=
  ToCsv.convert (int32 := ordinal) (byteArray := payload) database "dest" maxBytes admission
    renderLimits.maxDirectoryBytes keys .uri {} Int32ByteArray.Ingress.convert paths {} lookup selected keep budget

#guard Id.run do
  let .ok paths := listing | return false
  let .ok result := exportCsv projection 20 4096 paths | return false
  let schema := ToCsv.csvSchema projection.schema
  let .ok decoded := Csv.Typed.Utf8.decode schema ToCsv.codecs result.wire | return false
  return List.ofFn result.schema.kind == List.ofFn schema.kind &&
    projectedRows decoded == rows && otherPreserved result.db

#guard Id.run do
  let .ok paths := listing | return false
  let .ok result := exportCsv zero 20 4096 paths | return false
  let .ok decoded := Csv.Typed.Utf8.decode (ToCsv.csvSchema zero.schema) ToCsv.codecs result.wire | return false
  return result.schema.width == 0 && decoded.length == 20 &&
    result.wire == (List.replicate 21 ("\"\"\r\n".toUTF8.data.toList)).flatten

#guard Id.run do
  let .ok paths := listing | return false
  let .error (.input .closed) := exportCsv projection 19 4096 paths | return false
  return true

#guard Id.run do
  let .ok paths := listing | return false
  let .error (.input (.readError (.runtime cause))) :=
    exportCsv projection 24 4096 (paths ++ [late]) | return false
  return decide (cause = lateCause)

#guard
  let bad := "apart/not-int/skip.parquet"
  match exportCsv projection 0 4096 [controls, bad] with
  | .error (.input (.openError (.admission reason))) =>
    reason == .entry 1 (.binding bad (.conversion "year" (.invalidInt32 "not-int")))
  | _ => false

#guard Id.run do
  let .ok paths := listing | return false
  let .ok result := exportCsv zero 20 4096 paths | return false
  let .ok exactFit := exportCsv zero 20 result.wire.length paths | return false
  let .error (.byteLimit maximum actual) :=
    exportCsv zero 20 (result.wire.length - 1) paths | return false
  return exactFit.wire == result.wire && maximum == 83 && actual == 84

#guard
  let badSchema : Scan.Schema String Kind := ⟨1, fun _ => ("a\tb", .int32 .optional)⟩
  let imported : Except (NamedTable.ImportError Unit) (Database String) :=
    .ok (fun _ => some ⟨badSchema, []⟩)
  match ToCsv.exportImported "dest" 4096 imported with
  | .error (.output (.encodeError .unrepresentableWire)) => true
  | _ => false

#guard (ToCsv.bytesCodec.parse "%ff%00".toUTF8.data.toList).isNone

#print axioms ToCsv.csvSchema_label
#print axioms ToCsv.codecs_parsePrint
#print axioms ToCsv.exportImported_input_error
#print axioms ToCsv.convert_roundTrip
#print axioms ToCsv.convert_eq_reference


private def restoredName := "restored"

private def reimport (declared : Scan.Schema String Kind) (caps : FromCsv.Limits) (wire : Csv.Bytes) :=
  FromCsv.importCsv database restoredName declared declared caps wire

#guard Id.run do
  let .ok paths := listing | return false
  let .ok result := exportCsv projection 20 4096 paths | return false
  let .ok restored := reimport projection.schema ⟨result.wire.length, 20⟩ result.wire | return false
  return observesLoadedProjection restored restoredName

private def observesLoadedZero (loaded : Database String) : Bool :=
  match Scan.observePacked loaded restoredName with
  | some table => table.schema.width == 0 && table.rowCount == 20 && otherPreserved loaded
  | none => false

#guard Id.run do
  let .ok paths := listing | return false
  let .ok result := exportCsv zero 20 4096 paths | return false
  let .ok restored := reimport zero.schema ⟨84, 20⟩ result.wire | return false
  return observesLoadedZero restored

#guard Id.run do
  let .ok paths := listing | return false
  let .ok result := exportCsv zero 20 4096 paths | return false
  let .error (.openError (.byteLimit 83 84)) := reimport zero.schema ⟨83, 0⟩ result.wire | return false
  let .error (.openError (.rowLimit 19 20)) := reimport zero.schema ⟨84, 19⟩ result.wire | return false
  return true

private def changedKind : Scan.Schema String Kind :=
  ⟨projection.schema.width, fun i =>
    let column := projection.schema.kind i
    if i.val = 0 then (column.1, .byteArray .required) else column⟩

#guard Id.run do
  let .ok paths := listing | return false
  let .ok result := exportCsv projection 20 4096 paths | return false
  let .error .schemaMismatch :=
    FromCsv.importCsv database restoredName changedKind projection.schema ⟨4096, 20⟩ result.wire | return false
  return true

#guard match FromCsv.importCsv database "other" zero.schema zero.schema ⟨0, 0⟩ [0] with
  | .error .nameConflict => true
  | _ => false

#guard match reimport zero.schema ⟨0, 0⟩ [0] with
  | .error (.openError (.byteLimit 0 1)) => true
  | _ => false

/-- Replay independently written CSV on the actual named importer. -/
public def checkCsvInputs (directory : System.FilePath) : IO Unit := do
  let wire ← IO.FS.readBinFile (directory / "projected.csv")
  let .ok restored := reimport projection.schema ⟨wire.size, 20⟩ wire.data.toList |
    throw (IO.userError "independent projected CSV refused")
  unless observesLoadedProjection restored restoredName do
    throw (IO.userError "independent projected CSV changed the ordered named observation")
  let wire ← IO.FS.readBinFile (directory / "zero.csv")
  let .ok restored := reimport zero.schema ⟨wire.size, 20⟩ wire.data.toList |
    throw (IO.userError "independent zero-column CSV refused")
  unless observesLoadedZero restored do
    throw (IO.userError "independent zero-column CSV changed the row count")
  let rejected := [
    ("wrong-header.csv", projection.schema, Csv.Typed.Error.headerMismatch),
    ("bad-bytes.csv", projection.schema, .parseCell 4),
    ("bad-int.csv", projection.schema, .parseCell 2),
    ("bad-zero.csv", zero.schema, .zeroColumnMarker)]
  for (file, schema, expected) in rejected do
    let wire ← IO.FS.readBinFile (directory / file)
    let .error (.openError (.csv actual)) := reimport schema ⟨wire.size, 20⟩ wire.data.toList |
      throw (IO.userError s!"{file}: expected typed refusal")
    unless actual == expected do
      throw (IO.userError s!"{file}: expected {reprStr expected}, got {reprStr actual}")
  IO.println "Independent CSV imports matched the projected rows and zero-width count. Four typed refusals matched."

#print axioms FromCsv.readCsv_ok_iff
#print axioms FromCsv.importCsv_ok_iff
#print axioms FromCsv.importCsv_read_error
#print axioms FromCsv.import_convert

/-- Emit the actual converted bytes for the independent CSV reader. -/
public def emitCsv (projectedFile zeroFile : System.FilePath) : IO Unit := do
  let .ok paths := listing | throw (IO.userError "positional fixture rendering failed")
  let .ok projected := exportCsv projection 20 4096 paths |
    throw (IO.userError "projected CSV conversion failed")
  let .ok emptyColumns := exportCsv zero 20 4096 paths |
    throw (IO.userError "zero-column CSV conversion failed")
  IO.FS.writeBinFile projectedFile projected.wire.toByteArray
  IO.FS.writeBinFile zeroFile emptyColumns.wire.toByteArray

end Silmaril.Formats.Hive.Manifest.RenderedPositional

public def main (args : List String) : IO Unit :=
  match args with
  | ["--check-csv", directory] =>
    Silmaril.Formats.Hive.Manifest.RenderedPositional.checkCsvInputs directory
  | [projectedFile, zeroFile] =>
    Silmaril.Formats.Hive.Manifest.RenderedPositional.emitCsv projectedFile zeroFile
  | _ => throw (IO.userError "expected CSV output paths or --check-csv and its input directory")
