module

public import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Defs
import Silmaril.Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups

public section

namespace Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups

open Silmaril.Relational Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema Convert partitionCells)
open Snapshot.FlatInt32 (Cell)

variable {Name EncodeFailure DecodeFailure : Type*}

/-- Successful cuts cover exactly the requested rows within both per-file bounds. -/
theorem planCuts_exact {policy : Policy} {rows : Nat} {sizes : List Nat}
    (planned : planCuts policy rows = .ok sizes) :
    sizes = cuts policy.rowsPerGroup policy.maxGroupsPerFile rows ∧ sizes.sum = rows ∧
    rows ≤ policy.maxRowsPerFile ∧ sizes.length ≤ policy.maxGroupsPerFile ∧
    ∀ count ∈ sizes, 0 < count ∧ count ≤ policy.rowsPerGroup :=
  Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.planCuts_exact planned

/-- The exact cut sizes and original slot order are both observable. -/
theorem splitSlots_exact {α : Type*} (sizes : List Nat) (rows : List α) (total : sizes.sum = rows.length) :
    (splitSlots sizes rows).map List.length = sizes ∧ (splitSlots sizes rows).flatten = rows :=
  Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.splitSlots_exact sizes rows total

/-- The original file footer contains the exact total and ordered group sizes. -/
theorem readPayload_footer (policy : Policy) (limits : FlatInt32Writer.Limits) (leaf : String)
    (file : File) (groups : Slots) (read : readPayload policy limits leaf file = .ok groups) :
    ∃ span metadata, Footer.readFooter limits.footer file.bytes = .ok (span, metadata) ∧
      metadata.numRows = Int.ofNat file.rowCount ∧
      metadata.rowGroups.map Footer.RowGroup.numRows = file.groupRows.map Int.ofNat :=
  Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.readPayload_footer policy limits leaf file groups read

/-- Each emitted file carries exactly the total and ordered group counts of
its actual decoded slots. -/
theorem FileMatches.counts {policy : Policy} {limits : FlatInt32Writer.Limits} {leaf : String}
    {bucket : Bucket (physical leaf) Cell} {file : File} (matched : FileMatches policy limits leaf bucket file) :
    file.groupRows.sum = file.rowCount ∧
      (splitSlots file.groupRows (physicalSlots bucket.rows)).map List.length = file.groupRows := by
  have total := (planCuts_exact matched.planned).2.1
  exact ⟨total.trans matched.count.symm,
    (splitSlots_exact file.groupRows (physicalSlots bucket.rows) (by simpa [physicalSlots] using total)).1⟩

/-- Successful emission returns the original routed occurrences with checked cuts
and exact slots. Full restoration reconstructs the independent grouped rows. -/
theorem restore_emit (db : Database Name) (name : Name) (leaf : String)
    (schema : PartitionSchema Unit) (options : PartitionPath.Options)
    (encode : Encode Cell EncodeFailure) (decode : Convert Cell DecodeFailure)
    (inverse : CellLeftInverse schema encode decode) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (rows : Scan.Table (schema.extend (physical leaf)) Cell) (files : List File)
    (found : Scan.observePacked db name = some ⟨schema.extend (physical leaf), rows⟩)
    (written : emit db name leaf schema options encode policy limits = .ok files) :
    ∃ buckets, WritePlan.reference (physical leaf) schema options encode rows = .ok buckets ∧
      List.Forall₂ (FileMatches policy limits leaf) buckets files ∧
      restore leaf schema options decode policy limits files = .ok (groupOriginalRows options encode rows) :=
  Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.restore_emit
    db name leaf schema options encode decode inverse policy limits rows files found written

/-- On a successfully restored manifest, skipping rejected occurrences agrees
with a stable row filter over the same typed partition values. -/
theorem restorePruned_eq_filter (leaf : String) (schema : PartitionSchema Unit)
    (options : PartitionPath.Options) (decode : Convert Cell DecodeFailure) (policy : Policy)
    (limits : FlatInt32Writer.Limits) (predicate : Scan.Predicate schema.toScan Cell) (files : List File)
    (rows : Scan.Table (schema.extend (physical leaf)) Cell)
    (restored : restore leaf schema options decode policy limits files = .ok rows) :
    restorePruned leaf schema options decode policy limits predicate files =
      .ok (Scan.select (fun row => predicate (partitionCells row)) rows) :=
  Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.restorePruned_eq_filter
    leaf schema options decode policy limits predicate files rows restored

end Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups
