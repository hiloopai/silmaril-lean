module

public import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc.Defs
import Silmaril.Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc

public section

namespace Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc

open Silmaril.Relational Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema Convert)
open Snapshot.FlatInt32 (Cell)
open FlatProjection.Composition

variable {Failure : Type*}

/-- Declare the physical payload first, followed by the selected typed
partition columns in the caller's order. Every field is nullable INT32. -/
theorem fields_exact (leaf : String) (partitions : PartitionSchema Unit) (keys : List (Fin partitions.toScan.width)) :
    fields leaf partitions keys = field leaf :: keys.map (fun i => field (partitions.toScan.kind i).1) := by
  simp [fields, positions, TypedPartitions.PartitionSchema.extend, physical, List.map_map, Function.comp_def]

/-- The actual native pull reader reaches EOS with the exact schema and
one batch per completed selected group, preserving counts and nullable cells. -/
theorem convert_readback (leaf : String) (partitions : PartitionSchema Unit) (options : PartitionPath.Options)
    (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate partitions.toScan Cell) (keys : List (Fin partitions.toScan.width))
    (ipc : Arrow.MixedFlat.Limits) (files : List File) {wire : KBytes}
    (converted : convert leaf partitions options decode policy limits predicate keys ipc files = .ok wire) :
    ∃ (sourceTrace : Trace (partitions.extend (physical leaf)) Failure)
      (trace : Arrow.MixedFlat.Stream.Events.Trace (Arrow.MixedFlat.Events.schema (fields leaf partitions keys))),
      scanPruned leaf partitions options decode policy limits predicate files = .ok sourceTrace ∧
      sourceTrace.result = .ok () ∧
      Arrow.MixedFlat.Stream.Events.readAll ipc wire = .ok ⟨Arrow.MixedFlat.Events.schema (fields leaf partitions keys), trace⟩ ∧
      trace.termination = .eos ∧ Ipc.readEvents ipc wire = some (observeTrace leaf partitions keys sourceTrace) :=
  Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc.convert_readback
    leaf partitions options decode policy limits predicate keys ipc files converted

/-- An admission or reached scan failure precedes the IPC writer for every
writer budget. The original typed cause survives. -/
theorem convert_scan_error (leaf : String) (partitions : PartitionSchema Unit) (options : PartitionPath.Options)
    (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate partitions.toScan Cell) (keys : List (Fin partitions.toScan.width))
    (ipc : Arrow.MixedFlat.Limits) (files : List File) {cause : ReadError Failure}
    (failed : (scanPruned leaf partitions options decode policy limits predicate files).bind Trace.result = .error cause) :
    convert leaf partitions options decode policy limits predicate keys ipc files = .error (.scan cause) := by
  cases scanned : scanPruned leaf partitions options decode policy limits predicate files <;>
    simp_all [convert, Except.bind]

end Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc
