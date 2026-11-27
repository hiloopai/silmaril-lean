module

public import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.Pruning.Defs
public import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc.Defs
import Silmaril.Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.Pruning

public section

namespace Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events

open Silmaril.Relational Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema Convert)
open Snapshot.FlatInt32 (Cell)
open FlatProjection.Composition

variable {Failure : Type*}

/-- When every reached rejected payload decodes, the optimized scan is the
stable restriction of the unpruned trace. Original group batches, literal
paths, occurrence indices, footer ordinals and termination are preserved.
A reached path failure has the same cause on both sides. -/
theorem scanPruned_eq_restrict (leaf : String) (partitions : PartitionSchema Unit)
    (options : PartitionPath.Options) (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate partitions.toScan Cell) (files : List File)
    (safe : ReachedRejectedFilesDecode leaf partitions options decode policy limits predicate files) :
    scanPruned leaf partitions options decode policy limits predicate files =
      (scanUnpruned leaf partitions options decode policy limits files).map (fun trace =>
        trace.restrict (keepOccurrence partitions options decode predicate files)) :=
  Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.Pruning.scanPruned_eq_restrict
    leaf partitions options decode policy limits predicate files safe

/-- A successful native write observes the same restricted ordered groups
through the actual pull reader's EOS. The unpruned reference also exhausts
under the reached rejected payload hypothesis. -/
theorem ToIpc.convert_readback_restrict (leaf : String) (partitions : PartitionSchema Unit)
    (options : PartitionPath.Options) (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate partitions.toScan Cell) (keys : List (Fin partitions.toScan.width))
    (ipc : Arrow.MixedFlat.Limits) (files : List File)
    {whole : Trace (partitions.extend (physical leaf)) Failure} {wire : KBytes}
    (safe : ReachedRejectedFilesDecode leaf partitions options decode policy limits predicate files)
    (unpruned : scanUnpruned leaf partitions options decode policy limits files = .ok whole)
    (written : ToIpc.convert leaf partitions options decode policy limits predicate keys ipc files = .ok wire) :
    whole.result = .ok () ∧ Ipc.readEvents ipc wire = some
      (ToIpc.observeTrace leaf partitions keys (whole.restrict (keepOccurrence partitions options decode predicate files))) :=
  Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.Pruning.convert_readback_restrict
    leaf partitions options decode policy limits predicate keys ipc files safe unpruned written

end Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events
