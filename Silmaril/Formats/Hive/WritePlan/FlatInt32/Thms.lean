module

public import Silmaril.Formats.Hive.WritePlan.FlatInt32.Defs
import Silmaril.Formats.Hive.WritePlan.Thms
import Silmaril.Proofs.Formats.Hive.WritePlan.FlatInt32

public section

namespace Silmaril.Formats.Hive.WritePlan.FlatInt32

open Silmaril.Relational Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema Convert)
open Snapshot.FlatInt32 (Cell)

variable {Name EncodeFailure DecodeFailure : Type*}

/-- The checked routing result, including its first indexed error, precedes
per-bucket write admission. -/
theorem emit_eq_reference (db : Database Name) (name : Name) (leaf : String)
    (schema : PartitionSchema Unit) (options : PartitionPath.Options)
    (encode : Encode Cell EncodeFailure) (limits : FlatInt32Writer.Limits)
    (rows : Scan.Table (schema.extend (physical leaf)) Cell)
    (found : Scan.observePacked db name = some ⟨schema.extend (physical leaf), rows⟩) :
    emit db name leaf schema options encode limits =
      ((WritePlan.reference (physical leaf) schema options encode rows).mapError EmitError.routing).bind
        (fun buckets => buckets.mapM (emitBucket limits leaf)) := by
  unfold emit
  rw [Proofs.Formats.Hive.WritePlan.FlatInt32.namedRows_of_observe db name _ rows found]
  change ((WritePlan.plan (physical leaf) schema options encode rows).mapError EmitError.routing).bind
    (fun buckets => buckets.mapM (emitBucket limits leaf)) = _
  rw [plan_eq_reference]

/-- A routing error retains its original cause and produces no manifest. -/
theorem emit_plan_error (db : Database Name) (name : Name) (leaf : String)
    (schema : PartitionSchema Unit) (options : PartitionPath.Options)
    (encode : Encode Cell EncodeFailure) (limits : FlatInt32Writer.Limits)
    (rows : Scan.Table (schema.extend (physical leaf)) Cell)
    (found : Scan.observePacked db name = some ⟨schema.extend (physical leaf), rows⟩)
    {reason : WritePlan.Error EncodeFailure}
    (failed : WritePlan.plan (physical leaf) schema options encode rows = .error reason) :
    emit db name leaf schema options encode limits = .error (.routing reason) := by
  rw [emit_eq_reference db name leaf schema options encode limits rows found, ← plan_eq_reference, failed]
  rfl

/-- Reading the actual emitted files and binding their paths recovers the
original rows in first-seen directory order, stable within each bucket. -/
theorem restore_emit (db : Database Name) (name : Name) (leaf : String)
    (schema : PartitionSchema Unit) (options : PartitionPath.Options)
    (encode : Encode Cell EncodeFailure) (decode : Convert Cell DecodeFailure)
    (inverse : CellLeftInverse schema encode decode) (limits : FlatInt32Writer.Limits)
    (rows : Scan.Table (schema.extend (physical leaf)) Cell) (files : List File)
    (found : Scan.observePacked db name = some ⟨schema.extend (physical leaf), rows⟩)
    (written : FlatInt32.emit db name leaf schema options encode limits = .ok files) :
    ∃ buckets, WritePlan.reference (physical leaf) schema options encode rows = .ok buckets ∧
      files.map (fun file => (file.path, file.rowCount)) =
        buckets.map (fun bucket => (filePath bucket.directory, bucket.rows.length)) ∧
      FlatInt32.restore leaf schema options decode limits files = .ok (groupOriginalRows options encode rows) :=
  Proofs.Formats.Hive.WritePlan.FlatInt32.restore_emit
    db name leaf schema options encode decode inverse limits rows files found written

end Silmaril.Formats.Hive.WritePlan.FlatInt32
