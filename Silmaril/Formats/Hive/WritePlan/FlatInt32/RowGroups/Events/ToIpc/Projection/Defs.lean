module

public import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc.Defs

/-! Select positions of the native Hive payload/key layout before IPC encoding. -/

@[expose] public section

namespace Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc

open Silmaril.Relational Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema Convert)
open Snapshot.FlatInt32 (Cell)

/-- Wide position zero is the physical payload, followed by one position
per declared key. Selection keeps caller order and any repeated positions. -/
def sourcePositions (leaf : String) (partitions : PartitionSchema Unit)
    (keys : List (Fin partitions.toScan.width)) (selected : List (Fin (keys.length + 1))) :
    List (Fin (partitions.extend (physical leaf)).width) :=
  have width : (positions leaf partitions keys).length = keys.length + 1 := by
    change ((0 : Fin 1).castAdd partitions.toScan.width :: keys.map (·.natAdd 1)).length = _
    simp
  selected.map fun i => (positions leaf partitions keys)[i.val]'(width.symm ▸ i.isLt)

/-- Encode the corresponding source slots after the pruned scan completes.
An empty selection still encodes each original group's row count. -/
def convertProjected {Failure : Type*} (leaf : String) (partitions : PartitionSchema Unit)
    (options : PartitionPath.Options) (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate partitions.toScan Cell) (keys : List (Fin partitions.toScan.width))
    (selected : List (Fin (keys.length + 1))) (ipc : Arrow.MixedFlat.Limits) (files : List File) :
    Except (Error Failure) KBytes :=
  convertAt leaf partitions options decode policy limits predicate (sourcePositions leaf partitions keys selected) ipc files

end Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc
