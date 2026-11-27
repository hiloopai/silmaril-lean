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

private theorem observeInput (leaf : String) (partitions : PartitionSchema Unit)
    (keys : List (Fin partitions.toScan.width)) (batch : GroupBatch (partitions.extend (physical leaf))) :
    Ipc.observeSourceBatch (batchInput leaf partitions keys batch).observe = some (observeBatch leaf partitions keys batch) := by
  simp [Ipc.observeSourceBatch, batchInput, OrderedWriter.BatchInput.observe, OrderedWriter.Column.observe,
    observeBatch, Ipc.observeSlots, List.map_map, Function.comp_def, Option.map_map]

private theorem observeInputs (leaf : String) (partitions : PartitionSchema Unit)
    (keys : List (Fin partitions.toScan.width)) (trace : Trace (partitions.extend (physical leaf)) Failure) :
    Ipc.observeSource ⟨fields leaf partitions keys,
      (trace.batches.map (batchInput leaf partitions keys)).map OrderedWriter.BatchInput.observe⟩ =
      some (observeTrace leaf partitions keys trace) := by
  simp [Ipc.observeSource, List.mapM_map, Function.comp_def, observeInput, observeTrace]
  exact List.mapM_pure (m := Option)

theorem convert_readback (leaf : String) (partitions : PartitionSchema Unit) (options : PartitionPath.Options)
    (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate partitions.toScan Cell) (keys : List (Fin partitions.toScan.width))
    (ipc : Silmaril.Formats.Arrow.MixedFlat.Limits) (files : List File) {wire : KBytes}
    (converted : convert leaf partitions options decode policy limits predicate keys ipc files = .ok wire) :
    ∃ (sourceTrace : Trace (partitions.extend (physical leaf)) Failure)
      (trace : Stream.Events.Trace (Silmaril.Formats.Arrow.MixedFlat.Events.schema (fields leaf partitions keys))),
      scanPruned leaf partitions options decode policy limits predicate files = .ok sourceTrace ∧
      sourceTrace.result = .ok () ∧
      Stream.Events.readAll ipc wire = .ok ⟨Silmaril.Formats.Arrow.MixedFlat.Events.schema (fields leaf partitions keys), trace⟩ ∧
      trace.termination = .eos ∧ Ipc.readEvents ipc wire = some (observeTrace leaf partitions keys sourceTrace) := by
  cases scanned : scanPruned leaf partitions options decode policy limits predicate files with
  | error cause => simp [convert, scanned] at converted
  | ok sourceTrace =>
    cases stopped : sourceTrace.result with
    | error cause => simp [convert, scanned, stopped] at converted
    | ok done =>
      cases done
      cases written : OrderedWriter.emit ipc (fields leaf partitions keys) (sourceTrace.batches.map (batchInput leaf partitions keys)) with
      | error cause => simp [convert, scanned, stopped, written, Except.mapError] at converted
      | ok actual =>
        simp [convert, scanned, stopped, written, Except.mapError] at converted
        subst wire
        obtain ⟨observed, _, trace, _, pulled, eos⟩ := Ipc.read_emitted written
        exact ⟨sourceTrace, trace, rfl, stopped, pulled, eos, observed.trans (observeInputs leaf partitions keys sourceTrace)⟩

end Silmaril.Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc
