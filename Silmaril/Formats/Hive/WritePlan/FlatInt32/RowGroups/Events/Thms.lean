module

public import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.Defs
import Silmaril.Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events

public section

namespace Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events

open Silmaril.Relational Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema Convert)
open Snapshot.FlatInt32 (Cell)

variable {Failure : Type*} {schema : Scan.Schema String Unit}

@[simp] theorem Trace.toArrow_rows (trace : Trace schema Failure) : trace.toArrow.rows = trace.rows := by
  simp [Trace.toArrow, Silmaril.Formats.Arrow.Events.Trace.rows, Trace.rows, List.flatMap_map, Function.comp_def]

/-- Exhausting the tagged scan and flattening its Arrow rows recovers the
pruned relational restore, with the same typed admission and read errors. -/
theorem finish_scanPruned (leaf : String) (partitions : PartitionSchema Unit) (options : PartitionPath.Options)
    (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate partitions.toScan Cell) (files : List File) :
    (scanPruned leaf partitions options decode policy limits predicate files).bind Trace.finish =
      restorePruned leaf partitions options decode policy limits predicate files :=
  Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.finish_scanPruned
    leaf partitions options decode policy limits predicate files

/-- A selected file contributes one batch at each original checked footer
ordinal, in order, with its typed partition constants and exact slots. -/
theorem scanFile_batches (leaf : String) (partitions : PartitionSchema Unit) (options : PartitionPath.Options)
    (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate partitions.toScan Cell) (file : File) (index : Nat)
    (cells : Scan.Row partitions.toScan Cell) (source : Reader.Source Nat (physical leaf) Cell SnapshotError)
    (groups : Slots) (bound : bindFileCells partitions options decode file = .ok cells)
    (keep : (predicate cells).getD false = true) (opened : openGroupSource policy limits leaf file = .ok source)
    (decoded : source.groups.mapM (readSlots source) = .ok groups) :
    scanFile leaf partitions options decode policy limits predicate (file, index) =
      ⟨(source.groups.zip groups).map (fun (ordinal, slots) => groupBatch cells ⟨index, file.path, ordinal⟩ slots), .ok ()⟩ := by
  simp only [scanFile, bound, keep, ite_true, opened]
  exact Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.scanSource_batches cells file index source groups decoded

/-- A later group fault in a selected file retains the exact decoded prefix
at its original ordinals and the original indexed payload cause. -/
theorem scanFile_first_error (leaf : String) (partitions : PartitionSchema Unit) (options : PartitionPath.Options)
    (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate partitions.toScan Cell) (file : File) (index : Nat)
    (cells : Scan.Row partitions.toScan Cell) (source : Reader.Source Nat (physical leaf) Cell SnapshotError)
    (before after : List Nat) (failed : Nat) (groups : Slots) (cause : PayloadError)
    (bound : bindFileCells partitions options decode file = .ok cells) (keep : (predicate cells).getD false = true)
    (opened : openGroupSource policy limits leaf file = .ok source) (split : source.groups = before ++ failed :: after)
    (decoded : before.mapM (readSlots source) = .ok groups) (error : readSlots source failed = .error cause) :
    scanFile leaf partitions options decode policy limits predicate (file, index) =
      ⟨(before.zip groups).map (fun (ordinal, slots) => groupBatch cells ⟨index, file.path, ordinal⟩ slots),
        .error (.file index file.path (.payload cause))⟩ := by
  simp only [scanFile, bound, keep, ite_true, opened]
  exact Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.scanSource_first_error
    cells file index source before after failed groups cause split decoded error

/-- Exhausted occurrences precede the failing file's own prefix. The
trace ends at the first reached file error. -/
theorem scanPruned_first_error (leaf : String) (partitions : PartitionSchema Unit) (options : PartitionPath.Options)
    (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate partitions.toScan Cell) (before : List File) (bad : File) (after : List File)
    (reason : ReadError Failure) (admitted : checkRead (Failure := Failure) leaf partitions policy = .ok ())
    (done : ∀ item ∈ before.zipIdx, (scanFile leaf partitions options decode policy limits predicate item).result = .ok ())
    (failed : (scanFile leaf partitions options decode policy limits predicate (bad, before.length)).result = .error reason) :
    scanPruned leaf partitions options decode policy limits predicate (before ++ bad :: after) =
      .ok ⟨before.zipIdx.flatMap (fun item => (scanFile leaf partitions options decode policy limits predicate item).batches) ++
        (scanFile leaf partitions options decode policy limits predicate (bad, before.length)).batches, .error reason⟩ := by
  simp only [scanPruned, admitted, Except.map, List.zipIdx_append, Nat.zero_add, List.zipIdx_cons]
  rw [Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.assemble_first_error _ _ _ _ _ done failed]

/-- Logical projection preserves each original batch's position and row count. -/
theorem Trace.project_positions (trace : Trace schema Failure) (projection : Scan.Projection schema) :
    (trace.project projection).batches.map (fun batch => (batch.position, batch.columns.rowCount)) =
      trace.batches.map (fun batch => (batch.position, batch.columns.rowCount)) :=
  by simp [Trace.project, List.map_map, Scan.Projection.projectColumns]

/-- Projecting the group columns observes the same rows as projecting the
exhausted relational result, with the original error on failure. -/
theorem Trace.project_finish (trace : Trace schema Failure) (projection : Scan.Projection schema) :
    (trace.project projection).finish = trace.finish.map projection.project :=
  Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.project_finish trace projection

end Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events
