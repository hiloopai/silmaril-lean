module

public import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.Pruning.Defs
public import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc.Defs
import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.Thms
import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.ToIpc.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.Pruning

open Silmaril.Relational Silmaril.Formats.Hive Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.WritePlan.FlatInt32 (physical SnapshotError)
open Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups
open Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events
open TypedPartitions (PartitionSchema Convert)
open Snapshot.FlatInt32 (Cell)
open FlatProjection.Composition

variable {schema : Scan.Schema String Unit} {Failure : Type*}

private theorem batches_assemble {α : Type*} (traceOf : α → Trace schema Failure)
    (files : List α) (p : GroupBatch schema → Prop) (each : ∀ item ∈ files, ∀ b ∈ (traceOf item).batches, p b) :
    ∀ b ∈ (Trace.assemble traceOf files).batches, p b := by
  induction files with
  | nil => simp [Trace.assemble]
  | cons item rest ih =>
    have current := each item (by simp)
    have tail := ih (fun entry mem => each entry (List.mem_cons_of_mem _ mem))
    cases outcome : (traceOf item).result with
    | error cause => simpa [Trace.assemble, outcome] using current
    | ok done =>
      cases done
      intro batch mem
      simp only [Trace.assemble, outcome, List.mem_append] at mem
      exact mem.elim (current batch) (tail batch)

private theorem fileIndex_scanFile (leaf : String) (partitions : PartitionSchema Unit)
    (options : PartitionPath.Options) (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (file : File) (index : Nat) :
    ∀ b ∈ (scanFile leaf partitions options decode policy limits (fun _ => some true) (file, index)).batches,
      b.position.fileIndex = index := by
  cases bound : bindFileCells partitions options decode file with
  | error cause => simp [scanFile, bound]
  | ok cells =>
    cases opened : openGroupSource policy limits leaf file with
    | error cause => simp [scanFile, bound, opened]
    | ok source =>
      simp only [scanFile, bound, Option.getD_some, ite_true, opened, scanSource]
      apply batches_assemble
      intro ordinal _ batch mem
      cases read : readSlots source ordinal with
      | error cause => simp [scanGroup, read] at mem
      | ok slots =>
        have exactBatch : batch = groupBatch cells ⟨index, file.path, ordinal⟩ slots := by
          simpa [scanGroup, read] using mem
        rw [exactBatch]
        rfl

private theorem lookup_occurrence (files : List File) (file : File) (index : Nat)
    (mem : (file, index) ∈ files.zipIdx) : files[index]? = some file := by
  obtain ⟨pos, found⟩ := List.mem_iff_getElem?.mp mem
  rw [List.getElem?_zipIdx, Nat.zero_add] at found
  cases item : files[pos]? with
  | none => simp [item] at found
  | some actual =>
    simp [item] at found
    obtain ⟨rfl, rfl⟩ := found
    exact item

private theorem scanFile_restrict (leaf : String) (partitions : PartitionSchema Unit)
    (options : PartitionPath.Options) (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate partitions.toScan Cell) (files : List File) (file : File) (index : Nat)
    (lookup : files[index]? = some file)
    (decoded : ∀ cells, bindFileCells partitions options decode file = .ok cells →
      (predicate cells).getD false = false → ∃ groups, readPayload policy limits leaf file = .ok groups) :
    scanFile leaf partitions options decode policy limits predicate (file, index) =
      (scanFile leaf partitions options decode policy limits (fun _ => some true) (file, index)).restrict
        (keepOccurrence partitions options decode predicate files) := by
  let whole := scanFile leaf partitions options decode policy limits (fun _ => some true) (file, index)
  change _ = whole.restrict _
  cases bound : bindFileCells partitions options decode file with
  | error cause => simp [whole, scanFile, bound, Trace.restrict]
  | ok cells =>
    have decision (batch) (mem : batch ∈ whole.batches) :
        keepOccurrence partitions options decode predicate files batch.position.fileIndex =
          (predicate cells).getD false := by
      rw [fileIndex_scanFile leaf partitions options decode policy limits file index batch mem]
      simp [keepOccurrence, lookup, bound]
    cases kept : (predicate cells).getD false with
    | true =>
      have same : scanFile leaf partitions options decode policy limits predicate (file, index) = whole := by
        simp [whole, scanFile, bound, kept]
      have all := List.filter_eq_self.mpr (fun batch mem => (decision batch mem).trans kept)
      simp only [same, Trace.restrict, all]
    | false =>
      have none : whole.batches.filter (fun batch =>
          keepOccurrence partitions options decode predicate files batch.position.fileIndex) = [] :=
        List.filter_eq_nil_iff.mpr (fun batch mem => by simp [decision batch mem, kept])
      obtain ⟨groups, read⟩ := decoded cells bound kept
      cases opened : openGroupSource policy limits leaf file with
      | error cause => simp [readPayload, opened, bind, Except.bind] at read
      | ok source =>
        have slots : source.groups.mapM (readSlots source) = .ok groups := by
          simpa [readPayload, opened, bind, Except.bind] using read
        have complete := congrArg Trace.result
          (scanFile_batches leaf partitions options decode policy limits (fun _ => some true)
            file index cells source groups bound rfl opened slots)
        change whole.result = .ok () at complete
        simp only [scanFile, bound, kept, Bool.false_eq_true, ite_false]
        change _ = Trace.mk (whole.batches.filter (fun batch =>
          keepOccurrence partitions options decode predicate files batch.position.fileIndex)) whole.result
        rw [none, complete]

private theorem assemble_restrict {α : Type*} (unpruned pruned : α → Trace schema Failure)
    (keep : Nat → Bool) (files : List α)
    (same : ∀ before entry after, files = before ++ entry :: after →
      (Trace.assemble unpruned before).result = .ok () → pruned entry = (unpruned entry).restrict keep) :
    Trace.assemble pruned files = (Trace.assemble unpruned files).restrict keep := by
  induction files with
  | nil => rfl
  | cons entry rest ih =>
    have first := same [] entry rest rfl rfl
    cases done : (unpruned entry).result with
    | error cause => simp [Trace.assemble, first, Trace.restrict, done]
    | ok exhausted =>
      cases exhausted
      have later : ∀ before next after, rest = before ++ next :: after →
          (Trace.assemble unpruned before).result = .ok () → pruned next = (unpruned next).restrict keep := by
        intro before next after split reached
        exact same (entry :: before) next after (congrArg (List.cons entry) split)
          (by simp [Trace.assemble, done, reached])
      simp [Trace.assemble, first, done, ih later, Trace.restrict, List.filter_append]

theorem scanPruned_eq_restrict (leaf : String) (partitions : PartitionSchema Unit)
    (options : PartitionPath.Options) (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate partitions.toScan Cell) (files : List File)
    (safe : ReachedRejectedFilesDecode leaf partitions options decode policy limits predicate files) :
    scanPruned leaf partitions options decode policy limits predicate files =
      (scanUnpruned leaf partitions options decode policy limits files).map (fun trace =>
        trace.restrict (keepOccurrence partitions options decode predicate files)) := by
  unfold scanUnpruned scanPruned
  cases admitted : checkRead (Failure := Failure) leaf partitions policy with
  | error cause => rfl
  | ok done =>
    simp only [Except.map, Except.ok.injEq]
    apply assemble_restrict
    intro before entry after split reached
    obtain ⟨file, index⟩ := entry
    have mem : (file, index) ∈ files.zipIdx := by simp [split]
    exact scanFile_restrict leaf partitions options decode policy limits predicate files file index
      (lookup_occurrence files file index mem) (safe before (file, index) after split reached)

theorem convert_readback_restrict (leaf : String) (partitions : PartitionSchema Unit)
    (options : PartitionPath.Options) (decode : Convert Cell Failure) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (predicate : Scan.Predicate partitions.toScan Cell) (keys : List (Fin partitions.toScan.width))
    (ipc : Silmaril.Formats.Arrow.MixedFlat.Limits) (files : List File)
    {whole : Trace (partitions.extend (physical leaf)) Failure} {wire : KBytes}
    (safe : ReachedRejectedFilesDecode leaf partitions options decode policy limits predicate files)
    (unpruned : scanUnpruned leaf partitions options decode policy limits files = .ok whole)
    (written : ToIpc.convert leaf partitions options decode policy limits predicate keys ipc files = .ok wire) :
    whole.result = .ok () ∧ Ipc.readEvents ipc wire = some
      (ToIpc.observeTrace leaf partitions keys (whole.restrict (keepOccurrence partitions options decode predicate files))) := by
  obtain ⟨source, _, scanned, complete, _, _, observed⟩ :=
    ToIpc.convert_readback leaf partitions options decode policy limits predicate keys ipc files written
  have same := scanPruned_eq_restrict leaf partitions options decode policy limits predicate files safe
  rw [scanned, unpruned] at same
  have sourceEq := Except.ok.inj same
  subst source
  exact ⟨complete, observed⟩

end Silmaril.Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups.Events.Pruning
