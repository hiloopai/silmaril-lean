module

public import Silmaril.Formats.Hive.WritePlan.FlatInt32.Defs
import Silmaril.Formats.Hive.WritePlan.Thms
import Silmaril.Formats.Hive.WritePlan.Restore.Thms
import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Arrow.Thms
import Silmaril.Semantics.Relational.Table.Thms
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn

public section

namespace Silmaril.Proofs.Formats.Hive.WritePlan.FlatInt32

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Hive Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.WritePlan
open Silmaril.Formats.Hive.WritePlan.FlatInt32
open TypedPartitions (PartitionSchema Convert)
open Snapshot.FlatInt32 (Cell)

variable {Name EncodeFailure DecodeFailure : Type*}

theorem namedRows_of_observe (db : Database Name) (name : Name) (expected : Scan.Schema String Unit)
    (rows : Scan.Table expected Cell) (found : Scan.observePacked db name = some ⟨expected, rows⟩) :
    namedRows (Failure := EncodeFailure) db name expected = .ok rows := by
  simp [namedRows, found]

private theorem writerInput_schema (leaf : String) (rows : Scan.Table (physical leaf) Cell) :
    (writerInput leaf rows).arrowSchema = physical leaf := by
  unfold FlatInt32Writer.Input.arrowSchema writerInput physical
  congr
  funext i
  rw [Fin.fin_one_eq_zero i]
  rfl

private theorem writerInput_rows (leaf : String) (rows : Scan.Table (physical leaf) Cell) :
    (writerInput leaf rows).rows = rows.map List.ofFn := by
  change (List.zipWith (fun row cell => cell :: row) (List.replicate rows.length [])
    (rows.map fun row => row (0 : Fin 1))).map List.reverse =
      rows.map (fun row => @List.ofFn (Option Int32) 1 row)
  rw [← List.map_const', List.zipWith_map, List.zipWith_self]
  simp [List.map_map, Function.comp_def, List.ofFn_succ]
  rfl

private theorem writerInput_limits (limits : FlatInt32Writer.Limits) (leaf : String)
    (rows : Scan.Table (physical leaf) Cell) :
    limits.snapshotLimits (writerInput leaf rows) = readLimits limits rows.length := by
  simp [FlatInt32Writer.Limits.snapshotLimits, FlatInt32Writer.Limits.scanLimits, writerInput, readLimits]

private theorem readAll_emit (limits : FlatInt32Writer.Limits) (leaf : String)
    (rows : Scan.Table (physical leaf) Cell) (output : FlatInt32Writer.Encoded)
    (written : FlatInt32Writer.emit limits (writerInput leaf rows) = .ok output) :
    Snapshot.FlatInt32.readAll (readLimits limits rows.length) (physical leaf) output.bytes =
      .ok ⟨physical leaf, ⟨[AlignedColumns.ofRows rows], .eos⟩⟩ := by
  obtain ⟨observed, lists, _, read⟩ := FlatInt32Writer.emit_snapshot_readAll written
  rw [writerInput_rows] at lists
  rw [writerInput_limits] at read
  have exactRows {opened : Scan.Schema String Unit} (same : opened = physical leaf)
      (observed : Scan.Table opened Cell) (lists : observed.map (@List.ofFn (Option Int32) opened.width) =
        rows.map (@List.ofFn (Option Int32) (physical leaf).width))
      (scanned : Snapshot.FlatInt32.readAll (readLimits limits rows.length) opened output.bytes =
        .ok ⟨opened, ⟨[AlignedColumns.ofRows observed], .eos⟩⟩) :
      Snapshot.FlatInt32.readAll (readLimits limits rows.length) (physical leaf) output.bytes =
        .ok ⟨physical leaf, ⟨[AlignedColumns.ofRows rows], .eos⟩⟩ := by
    subst opened
    have equal := List.ofFn_injective.list_map lists
    simpa only [equal] using scanned
  exact exactRows (writerInput_schema leaf rows) observed lists read

private theorem emitBucket_readback (limits : FlatInt32Writer.Limits) (leaf : String)
    (bucket : Bucket (physical leaf) Cell) (file : File)
    (written : emitBucket (Failure := EncodeFailure) limits leaf bucket = .ok file) :
    file.path = filePath bucket.directory ∧ file.rowCount = bucket.rows.length ∧
      readBucket (Failure := DecodeFailure) limits leaf file = .ok bucket := by
  cases split : Manifest.splitFile (filePath bucket.directory) with
  | error reason => simp [emitBucket, split, Except.mapError, bind, Except.bind] at written
  | ok parts =>
    by_cases exactPath : parts = (bucket.directory, filename)
    · subst parts
      cases encoded : FlatInt32Writer.emit limits (writerInput leaf bucket.rows) with
      | error reason =>
        simp [emitBucket, split, encoded, Except.mapError, bind, Except.bind] at written
      | ok output =>
        simp [emitBucket, split, encoded, Except.mapError, bind, Except.bind, pure, Except.pure] at written
        rcases written with rfl
        simp [readBucket, split, readAll_emit limits leaf bucket.rows output encoded, Events.Trace.rows,
          Except.mapError, bind, Except.bind, pure, Except.pure]
        simp [physical]
        cases bucket
        rfl
    · simp [emitBucket, split, exactPath, Except.mapError, bind, Except.bind] at written

private theorem emitBuckets_readback (limits : FlatInt32Writer.Limits) (leaf : String)
    (buckets : List (Bucket (physical leaf) Cell)) (files : List File)
    (written : buckets.mapM (emitBucket (Failure := EncodeFailure) limits leaf) = .ok files) :
    files.map (fun file => (file.path, file.rowCount)) =
      buckets.map (fun bucket => (filePath bucket.directory, bucket.rows.length)) ∧
      files.mapM (readBucket (Failure := DecodeFailure) limits leaf) = .ok buckets := by
  induction buckets generalizing files with
  | nil =>
    cases written
    exact ⟨rfl, rfl⟩
  | cons bucket buckets ih =>
    rw [List.mapM_cons] at written
    cases first : emitBucket (Failure := EncodeFailure) limits leaf bucket with
    | error reason => simp [first, bind, Except.bind] at written
    | ok file =>
      cases tail : buckets.mapM (emitBucket (Failure := EncodeFailure) limits leaf) with
      | error reason => simp [first, tail, bind, Except.bind] at written
      | ok filesTail =>
        simp [first, tail, bind, Except.bind, pure, Except.pure] at written
        subst files
        obtain ⟨path, count, read⟩ := emitBucket_readback (DecodeFailure := DecodeFailure) limits leaf bucket file first
        obtain ⟨ordered, restored⟩ := ih filesTail tail
        exact ⟨by simp [path, count, ordered],
          by simp [List.mapM_cons, read, restored, bind, Except.bind, pure, Except.pure]⟩

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
      FlatInt32.restore leaf schema options decode limits files = .ok (groupOriginalRows options encode rows) := by
  unfold FlatInt32.emit at written
  rw [namedRows_of_observe db name _ rows found] at written
  cases planned : WritePlan.plan (physical leaf) schema options encode rows with
  | error reason => simp [planned, Except.mapError, bind, Except.bind] at written
  | ok buckets =>
    simp only [planned, Except.mapError, bind, Except.bind] at written
    obtain ⟨paths, read⟩ := emitBuckets_readback (DecodeFailure := DecodeFailure) limits leaf buckets files written
    refine ⟨buckets, ?_, paths, ?_⟩
    · rwa [← plan_eq_reference]
    · simp [FlatInt32.restore, read, restore_plan_eq_groupedRows options encode decode inverse rows buckets planned,
        Except.mapError, bind, Except.bind]

end Silmaril.Proofs.Formats.Hive.WritePlan.FlatInt32
