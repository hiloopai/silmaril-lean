module

public import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.Defs

/-! Restrict a checked native Hive trace by original manifest occurrence. -/

@[expose] public section

namespace Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events

open Silmaril.Relational Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema Convert)
open Snapshot.FlatInt32 (Cell)

variable {schema : Scan.Schema String Unit} {Failure : Type*}

/-- Keep whole batches in order with their original tags and terminal outcome. -/
def Trace.restrict (trace : Trace schema Failure) (keep : Nat → Bool) : Trace schema Failure :=
  ⟨trace.batches.filter (fun batch => keep batch.position.fileIndex), trace.result⟩

/-- Resolve a tag against the original literal occurrence and use the same
path binder and typed predicate as the scan. An unresolved occurrence stays
in the reference restriction, whose terminal outcome is unchanged. -/
def keepOccurrence (partitions : PartitionSchema Unit) (options : PartitionPath.Options)
    (decode : Convert Cell Failure) (predicate : Scan.Predicate partitions.toScan Cell)
    (files : List File) (index : Nat) : Bool :=
  match files[index]? with
  | none => true
  | some file =>
    match bindFileCells partitions options decode file with
    | .error _ => true
    | .ok cells => (predicate cells).getD false

/-- Decode each reached occurrence without partition pruning. -/
def scanUnpruned (leaf : String) (partitions : PartitionSchema Unit) (options : PartitionPath.Options)
    (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits) (files : List File) :
    Except (ReadError Failure) (Trace (partitions.extend (physical leaf)) Failure) :=
  scanPruned leaf partitions options decode policy limits (fun _ => some true) files

/-- A rejected occurrence which the unpruned scan reaches after a completed
strict prefix must decode all its groups. Reachability uses original
occurrence indices and the unpruned prefix, independently of restriction.
A path error is a common failure before either predicate runs. -/
def ReachedRejectedFilesDecode (leaf : String) (partitions : PartitionSchema Unit) (options : PartitionPath.Options)
    (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate partitions.toScan Cell) (files : List File) : Prop :=
  ∀ before entry after, files.zipIdx = before ++ entry :: after →
    (Trace.assemble (scanFile leaf partitions options decode policy limits (fun _ => some true)) before).result = .ok () →
    ∀ cells, bindFileCells partitions options decode entry.1 = .ok cells →
      (predicate cells).getD false = false → ∃ groups, readPayload policy limits leaf entry.1 = .ok groups

end Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events
