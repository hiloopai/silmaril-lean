module

public import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc.Projection.Defs
public import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.Pruning.Defs
import Silmaril.Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc.Projection
import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc.Thms

public section

namespace Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc

open Silmaril.Relational Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema Convert)
open Snapshot.FlatInt32 (Cell)
open FlatProjection.Composition

variable {Failure : Type*}

/-- One wide position for the payload and every supplied key, including repeats. -/
theorem fields_width (leaf : String) (partitions : PartitionSchema Unit) (keys : List (Fin partitions.toScan.width)) :
    (fields leaf partitions keys).length = keys.length + 1 := by
  simp [fields_exact]

/-- Each selected position supplies one projected field. -/
theorem projected_fields_width (leaf : String) (partitions : PartitionSchema Unit)
    (keys : List (Fin partitions.toScan.width)) (selected : List (Fin (keys.length + 1))) :
    (fieldsAt (partitions.extend (physical leaf)) (sourcePositions leaf partitions keys selected)).length =
      selected.length := by
  simp only [fieldsAt, sourcePositions, List.length_map]

/-- Post-read selection of the wide observation gives the same fields,
counts and cells as selecting the corresponding typed source positions. -/
theorem project_observeTrace (leaf : String) (partitions : PartitionSchema Unit)
    (keys : List (Fin partitions.toScan.width)) (selected : List (Fin (keys.length + 1)))
    (trace : Trace (partitions.extend (physical leaf)) Failure) :
    Ipc.projectEvents (selected.map Fin.val) (observeTrace leaf partitions keys trace) =
      some (observeTraceAt (sourcePositions leaf partitions keys selected) trace) :=
  Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc.Projection.project_observeTrace
    leaf partitions keys selected trace

/-- Each write has its own successful admission and its pull read uses the
same limits as that write. Both observations refer to the same stable
partition restriction. Selection can repeat positions or have width zero. -/
theorem convertProjected_readback_restrict (leaf : String) (partitions : PartitionSchema Unit)
    (options : PartitionPath.Options) (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate partitions.toScan Cell) (keys : List (Fin partitions.toScan.width))
    (selected : List (Fin (keys.length + 1))) (wideIpc projectedIpc : Arrow.MixedFlat.Limits)
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
      Ipc.readEvents projectedIpc projectedWire = some projected :=
  Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc.Projection.convertProjected_readback_restrict
    leaf partitions options decode policy limits predicate keys selected wideIpc projectedIpc files
    safe unpruned wideWritten projectedWritten

end Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc
