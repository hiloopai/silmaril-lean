module

public import Silmaril.Formats.Hive.WritePlan.FlatInt32.Prune.Defs
import Silmaril.Formats.Hive.WritePlan.FlatInt32.Thms
import Silmaril.Proofs.Formats.Hive.WritePlan.FlatInt32.Prune

public section

namespace Silmaril.Formats.Hive.WritePlan.FlatInt32

open Silmaril.Relational Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema Convert partitionCells)
open Snapshot.FlatInt32 (Cell)

variable {Name EncodeFailure DecodeFailure : Type*}

/-- On a successful full restore, file pruning gives exactly the stable row
filter over the same typed partition cells and marker options. -/
theorem restorePruned_eq_filter (leaf : String) (schema : PartitionSchema Unit)
    (options : PartitionPath.Options) (decode : Convert Cell DecodeFailure) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate schema.toScan Cell) (files : List File)
    (rows : Scan.Table (schema.extend (physical leaf)) Cell)
    (restored : restore leaf schema options decode limits files = .ok rows) :
    restorePruned leaf schema options decode limits predicate files =
      .ok (Scan.select (fun row => predicate (partitionCells row)) rows) :=
  Proofs.Formats.Hive.WritePlan.FlatInt32.Prune.restorePruned_eq_filter options decode limits predicate restored

/-- On successful emission, filter the routed reference in first-seen directory
order and stable row order within each group, with the same codec and options. -/
theorem restorePruned_emit (db : Database Name) (name : Name) (leaf : String)
    (schema : PartitionSchema Unit) (options : PartitionPath.Options)
    (encode : Encode Cell EncodeFailure) (decode : Convert Cell DecodeFailure)
    (inverse : CellLeftInverse schema encode decode) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate schema.toScan Cell)
    (rows : Scan.Table (schema.extend (physical leaf)) Cell) (files : List File)
    (found : Scan.observePacked db name = some ⟨schema.extend (physical leaf), rows⟩)
    (written : emit db name leaf schema options encode limits = .ok files) :
    restorePruned leaf schema options decode limits predicate files =
      .ok (Scan.select (fun row => predicate (partitionCells row)) (groupOriginalRows options encode rows)) := by
  obtain ⟨_, _, _, restored⟩ := restore_emit db name leaf schema options encode decode inverse limits rows files found written
  exact restorePruned_eq_filter leaf schema options decode limits predicate files _ restored

end Silmaril.Formats.Hive.WritePlan.FlatInt32
