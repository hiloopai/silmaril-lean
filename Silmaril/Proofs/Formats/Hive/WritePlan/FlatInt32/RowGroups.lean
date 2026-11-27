module

public import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Defs
import Silmaril.Formats.Hive.WritePlan.Thms
import Silmaril.Formats.Hive.WritePlan.Restore.Thms
import Silmaril.Formats.Hive.TypedPartitions.Thms
import Silmaril.Formats.Parquet.Snapshot.Footer.Thms
import Mathlib.Data.List.Basic

public section

namespace Silmaril.Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups

open Silmaril.Relational Silmaril.Formats.Hive Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.WritePlan
open Silmaril.Formats.Hive.WritePlan.FlatInt32 (physical filePath filename checkFilePath)
open Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups
open TypedPartitions (PartitionSchema Convert TypedPartition materialize partitionCells)
open Snapshot.FlatInt32 (Cell)

variable {Name EncodeFailure DecodeFailure : Type*}

private theorem cuts_bounds (width fuel rows : Nat) (positive : 0 < width) :
    (cuts width fuel rows).length ≤ fuel ∧ ∀ count ∈ cuts width fuel rows, 0 < count ∧ count ≤ width := by
  induction fuel generalizing rows with
  | zero => simp [cuts]
  | succ fuel ih =>
    cases rows with
    | zero => simp [cuts]
    | succ rows =>
      obtain ⟨length, bound⟩ := ih (rows + 1 - width)
      simp only [cuts, List.length_cons, Nat.add_le_add_iff_right, length, true_and, List.mem_cons]
      rintro count (rfl | member)
      · omega
      · exact bound count member

theorem planCuts_exact {policy : Policy} {rows : Nat} {sizes : List Nat}
    (planned : planCuts policy rows = .ok sizes) :
    sizes = cuts policy.rowsPerGroup policy.maxGroupsPerFile rows ∧ sizes.sum = rows ∧
    rows ≤ policy.maxRowsPerFile ∧ sizes.length ≤ policy.maxGroupsPerFile ∧
    ∀ count ∈ sizes, 0 < count ∧ count ≤ policy.rowsPerGroup := by
  unfold planCuts at planned
  split at planned <;> try contradiction
  rename_i nonzero
  split at planned <;> try contradiction
  rename_i within
  dsimp only at planned
  split at planned <;> try contradiction
  rename_i total
  cases planned
  obtain ⟨length, bound⟩ := cuts_bounds policy.rowsPerGroup policy.maxGroupsPerFile rows (by omega)
  exact ⟨rfl, total, by omega, length, bound⟩

theorem splitSlots_exact {α : Type*} (sizes : List Nat) (rows : List α) (total : sizes.sum = rows.length) :
    (splitSlots sizes rows).map List.length = sizes ∧ (splitSlots sizes rows).flatten = rows := by
  induction sizes generalizing rows with
  | nil =>
    cases rows <;> simp_all [splitSlots]
  | cons size sizes ih =>
    have within : size ≤ rows.length := by simp at total; omega
    have remaining : sizes.sum = (rows.drop size).length := by simp at total ⊢; omega
    obtain ⟨counts, slots⟩ := ih (rows.drop size) remaining
    simp [splitSlots, counts, slots, Nat.min_eq_left within]

theorem readPayload_footer (policy : Policy) (limits : FlatInt32Writer.Limits) (leaf : String)
    (file : File) (groups : Slots) (read : readPayload policy limits leaf file = .ok groups) :
    ∃ span metadata, Footer.readFooter limits.footer file.bytes = .ok (span, metadata) ∧
      metadata.numRows = Int.ofNat file.rowCount ∧
      metadata.rowGroups.map Footer.RowGroup.numRows = file.groupRows.map Int.ofNat := by
  cases opened : openPayload policy limits leaf file with
  | error reason => simp [readPayload, opened, bind, Except.bind] at read
  | ok snapshot =>
    cases planned : planCuts policy file.rowCount with
    | error reason => simp [openPayload, planned, Except.mapError, bind, Except.bind] at opened
    | ok sizes =>
      simp only [openPayload, planned, Except.mapError, bind, Except.bind] at opened
      split at opened <;> try contradiction
      rename_i shape
      have same : file.groupRows = sizes := by
        by_contra different
        simp [different] at shape
      split at opened <;> try contradiction
      generalize checked : Snapshot.check (Failure := Snapshot.FlatInt32.Error Unit)
        ⟨limits.footer, 2⟩ file.bytes = result at opened
      cases result with
      | error reason => contradiction
      | ok actual =>
        dsimp only at opened
        split at opened <;> try contradiction
        cases raw : Footer.ColumnOrder.readSelection limits.footer actual 0 with
        | error reason => simp [raw] at opened
        | ok original =>
          simp only [raw] at opened
          split at opened <;> try contradiction
          split at opened <;> try contradiction
          rename_i dimensions
          have exactDimensions : actual.metadata.numRows = Int.ofNat file.rowCount ∧
              actual.metadata.rowGroups.map Footer.RowGroup.numRows = sizes.map Int.ofNat := by
            simpa using dimensions
          rw [← same] at exactDimensions
          have footerRead := Snapshot.check_footer (Failure := Snapshot.FlatInt32.Error Unit)
            (limits := ⟨limits.footer, 2⟩) (bytes := file.bytes) (snapshot := actual) checked
          exact ⟨actual.footer, actual.metadata, footerRead, exactDimensions⟩

private theorem emitBucket_exact (policy : Policy) (limits : FlatInt32Writer.Limits) (leaf : String)
    (bucket : Bucket (physical leaf) Cell) (file : File)
    (written : emitBucket (Failure := EncodeFailure) policy limits leaf bucket = .ok file) :
    FileMatches policy limits leaf bucket file := by
  unfold emitBucket at written
  cases split : Manifest.splitFile (filePath bucket.directory) with
  | error reason => simp [split, Except.mapError, bind, Except.bind] at written
  | ok parts =>
    simp only [split, Except.mapError, bind, Except.bind] at written
    split at written <;> try contradiction
    rename_i same
    have splitExact := split.trans (congrArg Except.ok (not_not.mp same))
    cases planned : planCuts policy bucket.rows.length with
    | error reason => simp [planned] at written
    | ok sizes =>
      simp only [planned] at written
      cases assembled : FlatInt32Writer.RowGroups.assemble limits leaf (splitSlots sizes (physicalSlots bucket.rows)) with
      | error reason => simp [assembled] at written
      | ok bytes =>
        simp only [assembled] at written
        cases read : readPayload policy limits leaf ⟨filePath bucket.directory, bucket.rows.length, sizes, bytes⟩ with
        | error reason => simp [read] at written
        | ok observed =>
          simp only [read] at written
          split at written <;> try contradiction
          rename_i values
          simp only [pure, Except.pure, Except.ok.injEq] at written
          subst file
          subst observed
          exact ⟨rfl, splitExact, rfl, planned, read⟩

private theorem mapM_cons_ok {α β ε : Type*} {f : α → Except ε β}
    {head : α} {tail : List α} {items : List β} (success : (head :: tail).mapM f = .ok items) :
    ∃ first rest, items = first :: rest ∧ f head = .ok first ∧ tail.mapM f = .ok rest := by
  cases first : f head <;> cases rest : tail.mapM f <;>
    simp_all [List.mapM_cons, bind, Except.bind, pure, Except.pure]

private theorem emitBuckets_exact (policy : Policy) (limits : FlatInt32Writer.Limits) (leaf : String)
    {buckets : List (Bucket (physical leaf) Cell)} {files : List File}
    (written : buckets.mapM (emitBucket (Failure := EncodeFailure) policy limits leaf) = .ok files) :
    List.Forall₂ (FileMatches policy limits leaf) buckets files := by
  induction buckets generalizing files with
  | nil => cases written; exact .nil
  | cons bucket buckets ih =>
    obtain ⟨file, remaining, rfl, first, tail⟩ := mapM_cons_ok written
    exact .cons (emitBucket_exact policy limits leaf bucket file first) (ih tail)

private theorem physicalSlots_rows (leaf : String) (rows : Scan.Table (physical leaf) Cell) :
    (physicalSlots rows).map (fun cell (_ : Fin (physical leaf).width) => cell) = rows := by
  simp only [physicalSlots, List.map_map]
  conv_rhs => rw [← List.map_id rows]
  apply List.map_congr_left
  intro row _
  funext index
  have zero : index = (0 : Fin 1) := Fin.fin_one_eq_zero index
  rw [zero]
  rfl

private def bindBucket {leaf : String} {schema : PartitionSchema Unit} (options : PartitionPath.Options)
    (decode : Convert Cell DecodeFailure) (bucket : Bucket (physical leaf) Cell) :
    Except (RestoreError DecodeFailure) (TypedPartition (physical leaf) schema Cell) :=
  (decodeDirectory schema options decode bucket.directory).map fun cells => ⟨cells, bucket.rows⟩

private theorem readParts_emitted (leaf : String) (schema : PartitionSchema Unit)
    (options : PartitionPath.Options) (decode : Convert Cell DecodeFailure) (policy : Policy)
    (limits : FlatInt32Writer.Limits) {buckets : List (Bucket (physical leaf) Cell)} {files : List File}
    (filesMatch : List.Forall₂ (FileMatches policy limits leaf) buckets files)
    {parts : List (TypedPartition (physical leaf) schema Cell)}
    (bound : buckets.mapM (bindBucket options decode) = .ok parts) (index : Nat) :
    (files.zipIdx index).mapM (readPart leaf schema options decode policy limits (fun _ => some true)) = .ok parts := by
  induction filesMatch generalizing parts index with
  | nil => cases bound; rfl
  | cons head tail ih =>
    obtain ⟨entry, entries, rfl, first, rest⟩ := mapM_cons_ok bound
    simp only [bindBucket] at first
    rename_i bucket file buckets files
    have checkedPath : checkFilePath (Failure := DecodeFailure) file.path = .ok bucket.directory := by
      simp [checkFilePath, head.split, Except.mapError, bind, Except.bind, pure, Except.pure]
    cases binding : decodeDirectory schema options decode bucket.directory with
    | error reason => simp [binding, Except.map] at first
    | ok cells =>
      simp [binding, Except.map] at first
      subst entry
      have total : file.groupRows.sum = (physicalSlots bucket.rows).length := by
        simpa [physicalSlots] using (planCuts_exact head.planned).2.1
      have flattened := (splitSlots_exact file.groupRows (physicalSlots bucket.rows) total).2
      simp [List.mapM_cons, ih rest (index + 1), readPart, checkedPath, binding, head.read, flattened,
        physicalSlots_rows, Except.mapError, bind, Except.bind, pure, Except.pure]

private theorem restore_emitted (leaf : String) (schema : PartitionSchema Unit)
    (options : PartitionPath.Options) (decode : Convert Cell DecodeFailure) (policy : Policy)
    (limits : FlatInt32Writer.Limits) {buckets : List (Bucket (physical leaf) Cell)} {files : List File}
    (nonzero : policy.rowsPerGroup ≠ 0) (filesMatch : List.Forall₂ (FileMatches policy limits leaf) buckets files)
    {rows : Scan.Table (schema.extend (physical leaf)) Cell}
    (restored : WritePlan.restore (physical leaf) schema options decode buckets = .ok rows) :
    FlatInt32.RowGroups.restore leaf schema options decode policy limits files = .ok rows := by
  cases schemaOk : TypedPartitions.checkSchema (Failure := DecodeFailure) (physical leaf) schema with
  | error reason => simp [WritePlan.restore, schemaOk] at restored
  | ok success =>
    cases success
    simp only [WritePlan.restore, schemaOk] at restored
    change ((buckets.mapM (bindBucket options decode)).map materialize) = .ok rows at restored
    cases bound : buckets.mapM (bindBucket (schema := schema) options decode) with
    | error reason => simp [bound, Except.map] at restored
    | ok parts =>
      simp [bound, Except.map] at restored
      subst rows
      simp [FlatInt32.RowGroups.restore, restorePruned, schemaOk, nonzero,
        readParts_emitted leaf schema options decode policy limits filesMatch bound 0,
        Except.mapError, Except.map, bind, Except.bind]

theorem restore_emit (db : FlatInt32.Database Name) (name : Name) (leaf : String)
    (schema : PartitionSchema Unit) (options : PartitionPath.Options)
    (encode : Encode Cell EncodeFailure) (decode : Convert Cell DecodeFailure)
    (inverse : CellLeftInverse schema encode decode) (policy : Policy) (limits : FlatInt32Writer.Limits)
    (rows : Scan.Table (schema.extend (physical leaf)) Cell) (files : List File)
    (found : Scan.observePacked db name = some ⟨schema.extend (physical leaf), rows⟩)
    (written : emit db name leaf schema options encode policy limits = .ok files) :
    ∃ buckets, WritePlan.reference (physical leaf) schema options encode rows = .ok buckets ∧
      List.Forall₂ (FileMatches policy limits leaf) buckets files ∧
      FlatInt32.RowGroups.restore leaf schema options decode policy limits files = .ok (groupOriginalRows options encode rows) := by
  have named : FlatInt32.namedRows (Failure := EncodeFailure) db name (schema.extend (physical leaf)) = .ok rows := by
    simp [FlatInt32.namedRows, found]
  cases planned : WritePlan.plan (physical leaf) schema options encode rows with
  | error reason => simp [emit, named, planned, Except.mapError, bind, Except.bind] at written
  | ok buckets =>
    simp only [emit, named, planned, Except.mapError, bind, Except.bind] at written
    split at written <;> try contradiction
    rename_i nonzero
    have filesMatch := emitBuckets_exact policy limits leaf written
    refine ⟨buckets, ?_, filesMatch, ?_⟩
    · rwa [← plan_eq_reference]
    · exact restore_emitted leaf schema options decode policy limits nonzero filesMatch
        (restore_plan_eq_groupedRows options encode decode inverse rows buckets planned)

private def keepPart {leaf : String} {schema : PartitionSchema Unit}
    (predicate : Scan.Predicate schema.toScan Cell) (part : TypedPartition (physical leaf) schema Cell) :
    TypedPartition (physical leaf) schema Cell :=
  if (predicate part.cells).getD false then part else ⟨part.cells, []⟩

private theorem readPart_pruned (leaf : String) (schema : PartitionSchema Unit)
    (options : PartitionPath.Options) (decode : Convert Cell DecodeFailure) (policy : Policy)
    (limits : FlatInt32Writer.Limits) (predicate : Scan.Predicate schema.toScan Cell)
    (file : File) (index : Nat) (part : TypedPartition (physical leaf) schema Cell)
    (read : readPart leaf schema options decode policy limits (fun _ => some true) (file, index) = .ok part) :
    readPart leaf schema options decode policy limits predicate (file, index) = .ok (keepPart predicate part) := by
  cases path : checkFilePath (Failure := DecodeFailure) file.path with
  | error reason => simp [readPart, path, Except.mapError, bind, Except.bind] at read
  | ok directory =>
    cases binding : decodeDirectory schema options decode directory with
    | error reason => simp [readPart, path, binding, Except.mapError, bind, Except.bind] at read
    | ok cells =>
      cases payload : readPayload policy limits leaf file with
      | error reason => simp [readPart, path, binding, payload, Except.mapError, bind, Except.bind] at read
      | ok groups =>
        simp [readPart, path, binding, payload, Except.mapError, bind, Except.bind, pure, Except.pure] at read
        subst part
        cases keep : (predicate cells).getD false <;>
          simp [readPart, path, binding, payload, keepPart, keep, Except.mapError, bind, Except.bind, pure, Except.pure]

private theorem readParts_pruned (leaf : String) (schema : PartitionSchema Unit)
    (options : PartitionPath.Options) (decode : Convert Cell DecodeFailure) (policy : Policy)
    (limits : FlatInt32Writer.Limits) (predicate : Scan.Predicate schema.toScan Cell)
    (files : List File) (index : Nat) (parts : List (TypedPartition (physical leaf) schema Cell))
    (read : (files.zipIdx index).mapM (readPart leaf schema options decode policy limits (fun _ => some true)) = .ok parts) :
    (files.zipIdx index).mapM (readPart leaf schema options decode policy limits predicate) = .ok (parts.map (keepPart predicate)) := by
  induction files generalizing index parts with
  | nil => cases read; rfl
  | cons file rest ih =>
    rw [List.zipIdx_cons] at read
    obtain ⟨first, tail, rfl, head, readTail⟩ := mapM_cons_ok read
    simp [List.mapM_cons, readPart_pruned leaf schema options decode policy limits predicate file index first head,
      ih (index + 1) tail readTail, bind, Except.bind, pure, Except.pure]

private theorem materialize_pruned {leaf : String} {schema : PartitionSchema Unit}
    (predicate : Scan.Predicate schema.toScan Cell) (parts : List (TypedPartition (physical leaf) schema Cell)) :
    materialize (parts.map (keepPart predicate)) = Scan.select (fun row => predicate (partitionCells row)) (materialize parts) := by
  induction parts with
  | nil => rfl
  | cons part rest ih =>
    simp only [materialize, List.map_cons, List.flatMap_cons, Scan.select, List.filter_append] at *
    rw [ih]
    cases keep : (predicate part.cells).getD false <;>
      simp [keepPart, keep, TypedPartition.materialize, List.filter_map, Function.comp_def]

theorem restorePruned_eq_filter (leaf : String) (schema : PartitionSchema Unit)
    (options : PartitionPath.Options) (decode : Convert Cell DecodeFailure) (policy : Policy)
    (limits : FlatInt32Writer.Limits) (predicate : Scan.Predicate schema.toScan Cell) (files : List File)
    (rows : Scan.Table (schema.extend (physical leaf)) Cell)
    (restored : FlatInt32.RowGroups.restore leaf schema options decode policy limits files = .ok rows) :
    restorePruned leaf schema options decode policy limits predicate files =
      .ok (Scan.select (fun row => predicate (partitionCells row)) rows) := by
  cases schemaOk : TypedPartitions.checkSchema (Failure := DecodeFailure) (physical leaf) schema with
  | error reason => simp [FlatInt32.RowGroups.restore, restorePruned, schemaOk, Except.mapError, bind, Except.bind] at restored
  | ok success =>
    cases success
    by_cases zero : policy.rowsPerGroup = 0
    · simp [FlatInt32.RowGroups.restore, restorePruned, schemaOk, zero, Except.mapError, bind, Except.bind] at restored
    · cases read : files.zipIdx.mapM (readPart leaf schema options decode policy limits (fun _ => some true)) with
      | error reason =>
        simp [FlatInt32.RowGroups.restore, restorePruned, schemaOk, zero, read, Except.mapError, Except.map, bind, Except.bind] at restored
      | ok parts =>
        simp [FlatInt32.RowGroups.restore, restorePruned, schemaOk, zero, read, Except.mapError, Except.map, bind, Except.bind] at restored
        subst rows
        simp [restorePruned, schemaOk, zero, readParts_pruned leaf schema options decode policy limits predicate files 0 parts read,
          materialize_pruned, Except.mapError, Except.map, bind, Except.bind]

end Silmaril.Proofs.Formats.Hive.WritePlan.FlatInt32.RowGroups
