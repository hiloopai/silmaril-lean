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

def fieldsAt (schema : Scan.Schema String Unit) (indices : List (Fin schema.width)) : List Field :=
  indices.map fun i => field (schema.kind i).1

/-- One input record per original selected group. Only cells and counts
enter the record, while occurrence and group positions stay on the scan. -/
def batchInputAt {schema : Scan.Schema String Unit} (indices : List (Fin schema.width))
    (batch : GroupBatch schema) : OrderedWriter.BatchInput :=
  ⟨batch.columns.rowCount, indices.map fun i => .int32 (schema.kind i).1 true (batch.columns.values i)⟩

/-- Observe the selected group cells independently of writer input encoding. -/
def observeBatchAt {schema : Scan.Schema String Unit} (indices : List (Fin schema.width))
    (batch : GroupBatch schema) : Ipc.BatchObservation :=
  (batch.columns.rowCount, indices.map fun i =>
    (batch.columns.values i).map (Option.map (Ipc.Cell.primitive ∘ Arrow.Value.int32)))

def observeTraceAt {schema : Scan.Schema String Unit} {Failure : Type*} (indices : List (Fin schema.width))
    (trace : Trace schema Failure) : Ipc.EventObservation :=
  ⟨fieldsAt schema indices, trace.batches.map (observeBatchAt indices)⟩

def fields (leaf : String) (partitions : PartitionSchema Unit) (keys : List (Fin partitions.toScan.width)) :
    List Field :=
  fieldsAt (partitions.extend (physical leaf)) (positions leaf partitions keys)

def batchInput (leaf : String) (partitions : PartitionSchema Unit) (keys : List (Fin partitions.toScan.width))
    (batch : GroupBatch (partitions.extend (physical leaf))) : OrderedWriter.BatchInput :=
  batchInputAt (positions leaf partitions keys) batch

def observeBatch (leaf : String) (partitions : PartitionSchema Unit) (keys : List (Fin partitions.toScan.width))
    (batch : GroupBatch (partitions.extend (physical leaf))) : Ipc.BatchObservation :=
  observeBatchAt (positions leaf partitions keys) batch

def observeTrace {Failure : Type*} (leaf : String) (partitions : PartitionSchema Unit)
    (keys : List (Fin partitions.toScan.width)) (trace : Trace (partitions.extend (physical leaf)) Failure) :
    Ipc.EventObservation :=
  observeTraceAt (positions leaf partitions keys) trace

inductive Error (Failure : Type*) where
  | scan (cause : ReadError Failure)
  | writer (cause : OrderedWriter.Error)
  deriving BEq

/-- Complete the scan, then encode the given typed source positions. -/
def convertAt {Failure : Type*} (leaf : String) (partitions : PartitionSchema Unit) (options : PartitionPath.Options)
    (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate partitions.toScan Cell)
    (indices : List (Fin (partitions.extend (physical leaf)).width))
    (ipc : Arrow.MixedFlat.Limits) (files : List File) : Except (Error Failure) KBytes :=
  match scanPruned leaf partitions options decode policy limits predicate files with
  | .error cause => .error (.scan cause)
  | .ok trace =>
    match trace.result with
    | .error cause => .error (.scan cause)
    | .ok () =>
      (OrderedWriter.emit ipc (fieldsAt (partitions.extend (physical leaf)) indices)
        (trace.batches.map (batchInputAt indices))).mapError .writer

/-- Complete the partition-pruned scan before writer admission. A late file
failure preserves its typed cause and returns no IPC carrier. -/
def convert {Failure : Type*} (leaf : String) (partitions : PartitionSchema Unit) (options : PartitionPath.Options)
    (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate partitions.toScan Cell) (keys : List (Fin partitions.toScan.width))
    (ipc : Arrow.MixedFlat.Limits) (files : List File) : Except (Error Failure) KBytes :=
  convertAt leaf partitions options decode policy limits predicate (positions leaf partitions keys) ipc files

end Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc
