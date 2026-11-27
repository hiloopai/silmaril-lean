module

public import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc.Defs
import Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc

open Silmaril.Relational Silmaril.Formats.Hive Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.WritePlan.FlatInt32 (physical)
open Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups
open Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events
open Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc
open TypedPartitions (PartitionSchema Convert)
open Snapshot.FlatInt32 (Cell)
open FlatProjection.Composition
open Silmaril.Formats.Arrow.MixedFlat

variable {Failure : Type*}

private theorem observeInput {schema : Scan.Schema String Unit} (indices : List (Fin schema.width))
    (batch : GroupBatch schema) :
    Ipc.observeSourceBatch (batchInputAt indices batch).observe = some (observeBatchAt indices batch) := by
  simp [Ipc.observeSourceBatch, batchInputAt, OrderedWriter.BatchInput.observe, OrderedWriter.Column.observe,
    observeBatchAt, Ipc.observeSlots, List.map_map, Function.comp_def, Option.map_map]

private theorem observeInputs {schema : Scan.Schema String Unit} (indices : List (Fin schema.width))
    (trace : Trace schema Failure) :
    Ipc.observeSource ⟨fieldsAt schema indices, (trace.batches.map (batchInputAt indices)).map OrderedWriter.BatchInput.observe⟩ =
      some (observeTraceAt indices trace) := by
  simp [Ipc.observeSource, List.mapM_map, Function.comp_def, observeInput, observeTraceAt]
  exact List.mapM_pure (m := Option)

theorem convertAt_readback (leaf : String) (partitions : PartitionSchema Unit) (options : PartitionPath.Options)
    (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate partitions.toScan Cell)
    (indices : List (Fin (partitions.extend (physical leaf)).width))
    (ipc : Silmaril.Formats.Arrow.MixedFlat.Limits) (files : List File) {wire : KBytes}
    (converted : convertAt leaf partitions options decode policy limits predicate indices ipc files = .ok wire) :
    let declared := fieldsAt (partitions.extend (physical leaf)) indices
    ∃ (sourceTrace : Trace (partitions.extend (physical leaf)) Failure)
      (trace : Stream.Events.Trace (Silmaril.Formats.Arrow.MixedFlat.Events.schema declared)),
      scanPruned leaf partitions options decode policy limits predicate files = .ok sourceTrace ∧
      sourceTrace.result = .ok () ∧
      Stream.Events.readAll ipc wire = .ok ⟨Silmaril.Formats.Arrow.MixedFlat.Events.schema declared, trace⟩ ∧
      trace.termination = .eos ∧ Ipc.readEvents ipc wire = some (observeTraceAt indices sourceTrace) := by
  cases scanned : scanPruned leaf partitions options decode policy limits predicate files with
  | error cause => simp [convertAt, scanned] at converted
  | ok sourceTrace =>
    cases stopped : sourceTrace.result with
    | error cause => simp [convertAt, scanned, stopped] at converted
    | ok done =>
      cases done
      cases written : OrderedWriter.emit ipc (fieldsAt (partitions.extend (physical leaf)) indices)
          (sourceTrace.batches.map (batchInputAt indices)) with
      | error cause => simp [convertAt, scanned, stopped, written, Except.mapError] at converted
      | ok actual =>
        simp [convertAt, scanned, stopped, written, Except.mapError] at converted
        subst wire
        obtain ⟨observed, _, trace, _, pulled, eos⟩ := Ipc.read_emitted written
        exact ⟨sourceTrace, trace, rfl, stopped, pulled, eos, observed.trans (observeInputs indices sourceTrace)⟩

end Silmaril.Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc
