module

public import Silmaril.Formats.Hive.Date32.Manifest.Defs
import Silmaril.Proofs.Formats.Hive.Date32.Manifest
import Silmaril.Formats.Hive.Date32.Render.Thms
import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Thms

public section

namespace Silmaril.Formats.Hive.Date32

open Silmaril.Relational Silmaril.Formats.Parquet
open Snapshot.FlatInt32 (Cell)
open WritePlan.FlatInt32 (Database physical namedRows)
open WritePlan.FlatInt32.RowGroups
  (File FileError FileMatches PayloadError Policy bindFileCells checkRead readPayload)

/-- Restore the exact original typed rows in first-seen directory order and
source-relative order within each directory. The file relation certifies the
literal path, ordered cuts, and checked slots for every emitted file. -/
theorem restoreManifest_emitManifest {Name : Type*} (db : Database Name) (name : Name) (leaf key : String)
    (options : PartitionPath.Options) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (rows : Scan.Table ((partition key).extend (physical leaf)) Cell) (files : List File)
    (found : Scan.observePacked db name = some ⟨(partition key).extend (physical leaf), rows⟩)
    (written : emitManifest db name leaf key options policy limits = .ok files) :
    ∃ buckets, WritePlan.reference (physical leaf) (partition key) options encode rows = .ok buckets ∧
      List.Forall₂ (FileMatches policy limits leaf) buckets files ∧
      restoreManifest leaf key options policy limits files = .ok (WritePlan.groupOriginalRows options encode rows) :=
  WritePlan.FlatInt32.RowGroups.restore_emit db name leaf (partition key) options encode convert
    (encode_convert_leftInverse key) policy limits rows files found written

/-- A missing named source or schema mismatch retains its original cause. -/
theorem emitManifest_source_error {Name : Type*} (db : Database Name) (name : Name) (leaf key : String)
    (options : PartitionPath.Options) (policy : Policy) (limits : FlatInt32Writer.Limits)
    {cause : WritePlan.FlatInt32.EmitError RenderError}
    (failed : namedRows db name ((partition key).extend (physical leaf)) = .error cause) :
    emitManifest db name leaf key options policy limits = .error (.source cause) := by
  simp [emitManifest, WritePlan.FlatInt32.RowGroups.emit, failed, Except.mapError, Bind.bind, Except.bind]

/-- After source and schema admission and a classifiable prefix, a present
DATE equal to the decoded marker returns its indexed routing error before
cut or file admission, with no manifest value. -/
theorem emitManifest_first_markerCollision {Name : Type*} (db : Database Name) (name : Name) (leaf key : String)
    (options : PartitionPath.Options) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (before after : Scan.Table ((partition key).extend (physical leaf)) Cell)
    (row : Scan.Row ((partition key).extend (physical leaf)) Cell) (day : Int32)
    (bound : namedRows (Failure := RenderError) db name ((partition key).extend (physical leaf)) =
      .ok (before ++ row :: after))
    (schema : TypedPartitions.checkSchema (Failure := RenderError) (physical leaf) (partition key) = .ok ())
    (prefixOk : ∀ prior ∈ before, ∃ entry, WritePlan.classifyRow options encode prior = .ok entry)
    (present : TypedPartitions.partitionCells row (0 : Fin 1) = some day)
    (printed : encodeText day = .ok options.nullMarker) (marker : options.nullMarker.isEmpty = false)
    (valid : PartitionPath.validate options [(key, some options.nullMarker)] = .ok ()) :
    emitManifest db name leaf key options policy limits =
      .error (.source (.routing (.row before.length (.render (.nullMarkerCollision key))))) :=
  Proofs.Formats.Hive.Date32.Manifest.emitManifest_first_markerCollision db name leaf key options policy limits
    before after row day bound schema prefixOk present printed marker valid

/-- Following an exhausted prefix, the original literal path and its typed
path or partition binding failure precede the payload and the remaining files. -/
theorem restoreManifest_first_binding_error (leaf key : String) (options : PartitionPath.Options)
    (policy : Policy) (limits : FlatInt32Writer.Limits) (before : List File) (bad : File) (after : List File)
    (cause : FileError Error) (rows : Scan.Table ((partition key).extend (physical leaf)) Cell)
    (admitted : checkRead (Failure := Error) leaf (partition key) policy = .ok ())
    (done : restoreManifest leaf key options policy limits before = .ok rows)
    (failed : WritePlan.FlatInt32.RowGroups.bindFileCells (partition key) options convert bad = .error cause) :
    restoreManifest leaf key options policy limits (before ++ bad :: after) =
      .error (.file before.length bad.path cause) :=
  Proofs.Formats.Hive.Date32.Manifest.restoreManifest_first_binding_error leaf key options policy limits
    before bad after cause rows admitted done failed

/-- On a fully restored manifest, early partition selection agrees with
stable filtering of the exact typed rows, including duplicate occurrences. -/
theorem restoreSelected_eq_filter (leaf key : String) (options : PartitionPath.Options)
    (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate (partition key).toScan Cell) (files : List File)
    (rows : Scan.Table ((partition key).extend (physical leaf)) Cell)
    (restored : restoreManifest leaf key options policy limits files = .ok rows) :
    restoreSelected leaf key options policy limits predicate files =
      .ok (Scan.select (fun row => predicate (TypedPartitions.partitionCells row)) rows) :=
  WritePlan.FlatInt32.RowGroups.restorePruned_eq_filter leaf (partition key) options convert policy limits
    predicate files rows restored

/-- Path and DATE binding precede the predicate, even if it would reject
every occurrence. Preserve the original literal path and typed cause. -/
theorem restoreSelected_first_binding_error (leaf key : String) (options : PartitionPath.Options)
    (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate (partition key).toScan Cell) (before : List File) (bad : File) (after : List File)
    (cause : FileError Error) (rows : Scan.Table ((partition key).extend (physical leaf)) Cell)
    (admitted : checkRead (Failure := Error) leaf (partition key) policy = .ok ())
    (done : restoreSelected leaf key options policy limits predicate before = .ok rows)
    (failed : bindFileCells (partition key) options convert bad = .error cause) :
    restoreSelected leaf key options policy limits predicate (before ++ bad :: after) =
      .error (.file before.length bad.path cause) :=
  Proofs.Formats.Hive.Date32.Manifest.restoreSelected_first_binding_error leaf key options policy limits
    predicate before bad after cause rows admitted done failed

/-- A selected payload failure after an exhausted prefix retains its
original manifest index, literal path, and exact cause, including any
indexed row-group error. The remaining occurrences are immaterial. -/
theorem restoreSelected_first_payload_error (leaf key : String) (options : PartitionPath.Options)
    (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate (partition key).toScan Cell) (before : List File) (bad : File) (after : List File)
    (cause : PayloadError) (rows : Scan.Table ((partition key).extend (physical leaf)) Cell)
    (cells : Scan.Row (partition key).toScan Cell)
    (admitted : checkRead (Failure := Error) leaf (partition key) policy = .ok ())
    (done : restoreSelected leaf key options policy limits predicate before = .ok rows)
    (bound : bindFileCells (partition key) options convert bad = .ok cells)
    (keep : (predicate cells).getD false = true)
    (failed : readPayload policy limits leaf bad = .error cause) :
    restoreSelected leaf key options policy limits predicate (before ++ bad :: after) =
      .error (.file before.length bad.path (.payload cause)) :=
  Proofs.Formats.Hive.Date32.Manifest.restoreSelected_first_payload_error leaf key options policy limits
    predicate before bad after cause rows cells admitted done bound keep failed

end Silmaril.Formats.Hive.Date32
