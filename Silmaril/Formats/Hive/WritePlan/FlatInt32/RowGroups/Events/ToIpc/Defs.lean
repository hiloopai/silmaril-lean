module

public import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.Defs
public import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Defs
public import Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc.Defs

/-! Emit native Arrow IPC only after a selected Hive manifest reaches EOS. -/

@[expose] public section

namespace Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc

open Silmaril.Relational Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema Convert)
open Snapshot.FlatInt32 (Cell)
open FlatProjection.Composition
open Arrow.MixedFlat

/-- The physical INT32 payload is first. Optional partition positions are
checked against the typed declaration and appear in the supplied order. -/
def positions (leaf : String) (partitions : PartitionSchema Unit)
    (keys : List (Fin partitions.toScan.width)) : List (Fin (partitions.extend (physical leaf)).width) :=
  (0 : Fin 1).castAdd partitions.toScan.width :: keys.map (·.natAdd (physical leaf).width)

def field (label : String) : Field := ⟨label, true, .primitive .int32⟩

def fields (leaf : String) (partitions : PartitionSchema Unit) (keys : List (Fin partitions.toScan.width)) :
    List Field :=
  (positions leaf partitions keys).map fun i => field ((partitions.extend (physical leaf)).kind i).1

/-- One input record per original selected group. Only cells and counts
enter the record, while occurrence and group positions stay on the scan. -/
def batchInput (leaf : String) (partitions : PartitionSchema Unit) (keys : List (Fin partitions.toScan.width))
    (batch : GroupBatch (partitions.extend (physical leaf))) : OrderedWriter.BatchInput :=
  ⟨batch.columns.rowCount, (positions leaf partitions keys).map fun i =>
    .int32 ((partitions.extend (physical leaf)).kind i).1 true (batch.columns.values i)⟩

/-- Observe the selected group cells independently of writer input encoding. -/
def observeBatch (leaf : String) (partitions : PartitionSchema Unit) (keys : List (Fin partitions.toScan.width))
    (batch : GroupBatch (partitions.extend (physical leaf))) : Ipc.BatchObservation :=
  (batch.columns.rowCount, (positions leaf partitions keys).map fun i =>
    (batch.columns.values i).map (Option.map (Ipc.Cell.primitive ∘ Arrow.Value.int32)))

def observeTrace {Failure : Type*} (leaf : String) (partitions : PartitionSchema Unit)
    (keys : List (Fin partitions.toScan.width)) (trace : Trace (partitions.extend (physical leaf)) Failure) :
    Ipc.EventObservation :=
  ⟨fields leaf partitions keys, trace.batches.map (observeBatch leaf partitions keys)⟩

inductive Error (Failure : Type*) where
  | scan (cause : ReadError Failure)
  | writer (cause : OrderedWriter.Error)
  deriving BEq

/-- Complete the partition-pruned scan before writer admission. A late file
failure preserves its typed cause and returns no IPC carrier. -/
def convert {Failure : Type*} (leaf : String) (partitions : PartitionSchema Unit) (options : PartitionPath.Options)
    (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate partitions.toScan Cell) (keys : List (Fin partitions.toScan.width))
    (ipc : Arrow.MixedFlat.Limits) (files : List File) : Except (Error Failure) KBytes :=
  match scanPruned leaf partitions options decode policy limits predicate files with
  | .error cause => .error (.scan cause)
  | .ok trace =>
    match trace.result with
    | .error cause => .error (.scan cause)
    | .ok () =>
      (OrderedWriter.emit ipc (fields leaf partitions keys) (trace.batches.map (batchInput leaf partitions keys))).mapError
        .writer

end Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc
