module

public import Silmaril.Formats.Hive.Date32.Manifest.Defs
import Silmaril.Formats.Hive.Date32.Render.Thms
import Silmaril.Formats.Hive.WritePlan.Thms
import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Date32.Manifest

open Silmaril.Relational Silmaril.Formats.Parquet Silmaril.Formats.Hive Silmaril.Formats.Hive.Date32
open Snapshot.FlatInt32 (Cell)
open WritePlan.FlatInt32 (Database physical namedRows)
open WritePlan.FlatInt32.RowGroups (File FileError Policy checkRead)

private theorem classifyRow_markerCollision (leaf key : String) (options : PartitionPath.Options)
    (row : Scan.Row ((partition key).extend (physical leaf)) Cell) (day : Int32)
    (present : TypedPartitions.partitionCells row (0 : Fin 1) = some day)
    (printed : encodeText day = .ok options.nullMarker) (marker : options.nullMarker.isEmpty = false)
    (valid : PartitionPath.validate options [(key, some options.nullMarker)] = .ok ()) :
    WritePlan.classifyRow options encode row = .error (.render (.nullMarkerCollision key)) := by
  have entries : WritePlan.encodeEntries encode (TypedPartitions.partitionCells row) =
      .ok [(key, some options.nullMarker)] := by
    change (WritePlan.encodeEntry encode ⟨key, (), .reject⟩ (TypedPartitions.partitionCells row (0 : Fin 1))).bind
      (fun entry => .ok [entry]) = _
    simp [present, WritePlan.encodeEntry, encode, printed, Except.mapError, Except.map, Except.bind]
  have failed : PartitionPath.render options [(key, some options.nullMarker)] =
      .error (.nullMarkerCollision key) := by
    have collision := renderDirectory_markerCollision key options day printed marker valid
    cases path : PartitionPath.render options [(key, some options.nullMarker)] <;>
      simp_all [renderDirectory, Option.mapM, Except.mapError, Bind.bind, Except.bind]
  simp [WritePlan.classifyRow, entries, failed]

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
      .error (.source (.routing (.row before.length (.render (.nullMarkerCollision key))))) := by
  have failed := classifyRow_markerCollision leaf key options row day present printed marker valid
  have planned := (WritePlan.plan_first_row_error_iff options encode (before ++ row :: after)
    before.length (.render (.nullMarkerCollision key))).mpr
      ⟨schema, before, row, after, rfl, rfl, prefixOk, failed⟩
  simp [emitManifest, WritePlan.FlatInt32.RowGroups.emit, bound, planned, Except.mapError, Bind.bind, Except.bind]

theorem restoreManifest_first_binding_error (leaf key : String) (options : PartitionPath.Options)
    (policy : Policy) (limits : FlatInt32Writer.Limits) (before : List File) (bad : File) (after : List File)
    (cause : FileError Error) (rows : Scan.Table ((partition key).extend (physical leaf)) Cell)
    (admitted : checkRead (Failure := Error) leaf (partition key) policy = .ok ())
    (done : restoreManifest leaf key options policy limits before = .ok rows)
    (failed : WritePlan.FlatInt32.RowGroups.bindFileCells (partition key) options convert bad = .error cause) :
    restoreManifest leaf key options policy limits (before ++ bad :: after) =
      .error (.file before.length bad.path cause) := by
  open WritePlan.FlatInt32.RowGroups in
  unfold restoreManifest restore restorePruned at done ⊢
  simp only [admitted, Bind.bind, Except.bind] at done ⊢
  cases prior : before.zipIdx.mapM (WritePlan.FlatInt32.RowGroups.readPart
      leaf (partition key) options convert policy limits (fun _ => some true)) with
  | error reason => simp [prior, Except.map] at done
  | ok parts =>
    rw [List.zipIdx_append, List.mapM_append]
    simp [List.zipIdx_cons, prior, WritePlan.FlatInt32.RowGroups.readPart, failed, Except.mapError,
      Bind.bind, Except.bind, Except.map]

end Silmaril.Proofs.Formats.Hive.Date32.Manifest
