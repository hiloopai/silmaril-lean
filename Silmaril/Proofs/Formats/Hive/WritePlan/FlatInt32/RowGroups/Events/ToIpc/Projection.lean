module

public import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc.Projection.Defs
public import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.Pruning.Defs
import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.Pruning.Thms
import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc.Thms
import Silmaril.Formats.Parquet.FlatProjection.Composition.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc.Projection

open Silmaril.Relational Silmaril.Formats.Hive Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.WritePlan.FlatInt32 (physical)
open Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups
open Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events
open Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc
open TypedPartitions (PartitionSchema Convert)
open Snapshot.FlatInt32 (Cell)
open FlatProjection.Composition

variable {Failure : Type*}

private theorem select_sourcePositions (leaf : String) (partitions : PartitionSchema Unit)
    (keys : List (Fin partitions.toScan.width)) (selected : List (Fin (keys.length + 1))) :
    select (selected.map Fin.val) (positions leaf partitions keys) = some (sourcePositions leaf partitions keys selected) := by
  induction selected with
  | nil => rfl
  | cons i rest ih =>
    have within : i.val < (positions leaf partitions keys).length := by
      change i.val < ((0 : Fin 1).castAdd partitions.toScan.width :: keys.map (·.natAdd 1)).length
      simp
    simp only [select, List.map_cons, List.mapM_cons, List.getElem?_eq_getElem within]
    rw [show List.mapM (fun p => (positions leaf partitions keys)[p]?) (rest.map Fin.val) =
      some (sourcePositions leaf partitions keys rest) from ih]
    rfl

private theorem project_observeBatch (leaf : String) (partitions : PartitionSchema Unit)
    (keys : List (Fin partitions.toScan.width)) (selected : List (Fin (keys.length + 1)))
    (batch : GroupBatch (partitions.extend (physical leaf))) :
    Ipc.projectEventBatch (selected.map Fin.val) (observeBatchAt (positions leaf partitions keys) batch) =
      some (observeBatchAt (sourcePositions leaf partitions keys selected) batch) := by
  simp [Ipc.projectEventBatch, observeBatchAt, select_map, select_sourcePositions]

theorem project_observeTrace (leaf : String) (partitions : PartitionSchema Unit)
    (keys : List (Fin partitions.toScan.width)) (selected : List (Fin (keys.length + 1)))
    (trace : Trace (partitions.extend (physical leaf)) Failure) :
    Ipc.projectEvents (selected.map Fin.val) (observeTrace leaf partitions keys trace) =
      some (observeTraceAt (sourcePositions leaf partitions keys selected) trace) := by
  have batches : (trace.batches.map (observeBatchAt (positions leaf partitions keys))).mapM
      (Ipc.projectEventBatch (selected.map Fin.val)) =
      some (trace.batches.map (observeBatchAt (sourcePositions leaf partitions keys selected))) := by
    rw [List.mapM_map]
    simp only [Function.comp_def, project_observeBatch]
    exact List.mapM_pure (m := Option)
  simp [Ipc.projectEvents, observeTrace, observeTraceAt, fieldsAt, select_map, select_sourcePositions, batches]

theorem convertProjected_readback_restrict (leaf : String) (partitions : PartitionSchema Unit)
    (options : PartitionPath.Options) (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate partitions.toScan Cell) (keys : List (Fin partitions.toScan.width))
    (selected : List (Fin (keys.length + 1))) (wideIpc projectedIpc : Silmaril.Formats.Arrow.MixedFlat.Limits)
    (files : List File) {whole : Trace (partitions.extend (physical leaf)) Failure} {wideWire projectedWire : KBytes}
    (safe : ReachedRejectedFilesDecode leaf partitions options decode policy limits predicate files)
    (unpruned : scanUnpruned leaf partitions options decode policy limits files = .ok whole)
    (wideWritten : convert leaf partitions options decode policy limits predicate keys wideIpc files = .ok wideWire)
    (projectedWritten : convertProjected leaf partitions options decode policy limits predicate keys selected projectedIpc files =
      .ok projectedWire) :
    let restricted := whole.restrict (keepOccurrence partitions options decode predicate files)
    let wide := observeTrace leaf partitions keys restricted
    let projected := observeTraceAt (sourcePositions leaf partitions keys selected) restricted
    whole.result = .ok () ∧ Ipc.readEvents wideIpc wideWire = some wide ∧
      Ipc.projectEvents (selected.map Fin.val) wide = some projected ∧
      Ipc.readEvents projectedIpc projectedWire = some projected := by
  obtain ⟨done, wider⟩ := convert_readback_restrict leaf partitions options decode policy limits predicate keys wideIpc files
    safe unpruned wideWritten
  obtain ⟨source, _, pruned, _, _, _, narrowed⟩ :=
    convertAt_readback leaf partitions options decode policy limits predicate
      (sourcePositions leaf partitions keys selected) projectedIpc files projectedWritten
  have same := scanPruned_eq_restrict leaf partitions options decode policy limits predicate files safe
  rw [pruned, unpruned] at same
  have sourceEq := Except.ok.inj same
  subst source
  exact ⟨done, wider, project_observeTrace leaf partitions keys selected _, narrowed⟩

end Silmaril.Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc.Projection
