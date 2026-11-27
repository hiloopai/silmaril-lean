module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Projection.Defs
import Silmaril.Formats.Parquet.Timestamp.Leaf.Thms
import Silmaril.Semantics.Relational.Scan.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas
import Init.Data.List.FinRange

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Projection

open Silmaril.Formats Parquet Timestamp Silmaril.Relational
open Silmaril.Formats.Parquet.Timestamp.Leaf.Projection
open Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary.WithV1
open Silmaril.Numeric.Timestamp (Ticks)

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

private theorem ofFnM_finRange {α ε : Type} {n : Nat} (f : Fin n → Except ε α) :
    Vector.toList <$> Vector.ofFnM f = (List.finRange n).mapM f := by
  rw [Vector.toList_ofFnM]
  induction n with
  | zero => simp
  | succ n ih => simp [List.ofFnM_succ, List.finRange_succ, List.mapM_map, ih, Function.comp_def]

private theorem vector_ok_iff {α ε : Type} {n : Nat} {f : Fin n → Except ε α} {v : Vector α n} :
    Vector.ofFnM f = .ok v ↔ ∀ i : Fin n, f i = .ok v[i.val] := by
  have lists : (List.finRange n).mapM f = .ok v.toList ↔ ∀ i : Fin n, f i = .ok v[i.val] := by
    rw [List.mapM_eq_ok_iff_forall₂, List.forall₂_iff_get]
    constructor
    · intro h i
      simpa using h.2 i.val (by simp) (by simp)
    · intro h
      refine ⟨by simp, ?_⟩
      intro i lt _
      simpa using h ⟨i, by simpa using lt⟩
  rw [← lists, ← ofFnM_finRange]
  cases Vector.ofFnM f <;> simp [Functor.map, Except.map, Vector.toList_inj]

private theorem vector_first_error {α ε : Type} {n : Nat} {f : Fin n → Except ε α}
    {before after : List (Fin n)} {i : Fin n} {values : List α} {cause : ε}
    (split : List.finRange n = before ++ i :: after)
    (earlier : before.mapM f = .ok values) (failed : f i = .error cause) :
    Vector.ofFnM f = .error cause := by
  have whole : Vector.toList <$> Vector.ofFnM f = .error cause := by
    rw [ofFnM_finRange, split]
    simp [earlier, failed, Bind.bind, Except.bind]
  cases eq : Vector.ofFnM f <;> simp_all [Functor.map, Except.map]

theorem bindAt_ok {snapshot : Snapshot.Checked} {limits : Footer.Limits} {position ordinal : Nat}
    {bound : BoundTo snapshot} (read : bindAt snapshot limits position ordinal = .ok bound) :
    Leaf.bind limits snapshot ordinal = .ok bound.val := by
  unfold bindAt at read
  split at read
  · rename_i original accepted
    cases Except.ok.inj read
    exact accepted
  · contradiction

theorem bindOrdinals_first_error {snapshot : Snapshot.Checked} {limits : Footer.Limits}
    {ordinals : Array Nat} {before after : List (Fin ordinals.size)} {position : Fin ordinals.size}
    {bounds : List (BoundTo snapshot)} {cause : Leaf.Error}
    (split : List.finRange ordinals.size = before ++ position :: after)
    (earlier : before.mapM (fun i => bindAt snapshot limits i.val ordinals[i.val]) = .ok bounds)
    (failed : Leaf.bind limits snapshot ordinals[position.val] = .error cause) :
    bindOrdinals snapshot limits ordinals = .error (.bind position.val ordinals[position.val] cause) := by
  unfold bindOrdinals
  apply vector_first_error split earlier
  unfold bindAt
  split <;> rename_i result observed
  · rw [failed] at observed
    contradiction
  · have same : result = cause := Except.error.inj (observed.symm.trans failed)
    rw [same]

theorem openFile_bound {limits : Limits} {input : Bytes} {ordinals : Array Nat} {checked : Checked}
    (opened : openFile limits input ordinals = .ok checked) :
    Snapshot.check (Failure := Unit) limits.input.snapshot input = .ok checked.snapshot ∧
      ∃ width : checked.width = ordinals.size, ∀ i : Fin checked.width,
        Leaf.bind limits.input.snapshot.footer checked.snapshot ordinals[(i.cast width).val] = .ok (checked.column i) := by
  unfold openFile at opened
  split at opened
  · contradiction
  split at opened
  · contradiction
  obtain ⟨snapshot, snapshotOk, opened⟩ := bind_ok opened
  split at opened
  · contradiction
  dsimp only at opened
  split at opened
  · contradiction
  obtain ⟨columns, columnsOk, opened⟩ := bind_ok opened
  cases Except.ok.inj opened
  refine ⟨mapError_ok snapshotOk, rfl, fun i => ?_⟩
  exact bindAt_ok (vector_ok_iff.mp columnsOk i)

theorem openFile_selected {limits : Limits} {input : Bytes} {ordinals : Array Nat} {checked : Checked}
    (opened : openFile limits input ordinals = .ok checked) :
    ∃ width : checked.width = ordinals.size, ∀ i : Fin checked.width,
      (checked.column i).snapshot = checked.snapshot ∧
      (checked.column i).ordinal = ordinals[(i.cast width).val] ∧
      (checked.column i).ordinal ≠ 0 ∧
      checked.snapshot.metadata.schema[(checked.column i).ordinal]? = some (checked.column i).binding.leaf := by
  obtain ⟨_, width, bound⟩ := openFile_bound opened
  refine ⟨width, fun i => ?_⟩
  obtain ⟨same, position, nonzero, _, leaf, _, _⟩ := Leaf.bind_sound (bound i)
  exact ⟨same, position, by rwa [position], by rwa [position]⟩

theorem readCounts_ok_iff {checked : Checked} {limits : Limits} {group rows : Nat}
    {position : Fin checked.width} {counts : Counts rows} :
    checked.readCounts limits group rows position = .ok counts ↔
      ∃ slots, AllCodecs.readGroup limits.codec limits.input.leaf (checked.column position) group = .ok slots ∧
        slots.map (Option.map Ticks.ticks) = counts.val := by
  unfold Checked.readCounts
  cases original : AllCodecs.readGroup limits.codec limits.input.leaf (checked.column position) group with
  | error cause => simp [original, Except.mapError, Bind.bind, Except.bind]
  | ok slots =>
    simp only [Except.mapError, Bind.bind, Except.bind, original, Except.ok.injEq]
    constructor
    · intro h
      split at h
      · exact ⟨slots, rfl, congrArg Subtype.val (Except.ok.inj h)⟩
      · contradiction
    · rintro ⟨read, rfl, same⟩
      have aligned : (slots.map (Option.map Ticks.ticks)).length = rows := same ▸ counts.property
      simp only [aligned, ↓reduceDIte, pure, Except.pure, Except.ok.injEq]
      exact Subtype.ext same

theorem readCounts_failure {checked : Checked} {limits : Limits} {group rows : Nat}
    {position : Fin checked.width} {cause : AllCodecs.GroupError}
    (failed : AllCodecs.readGroup limits.codec limits.input.leaf (checked.column position) group = .error cause) :
    checked.readCounts limits group rows position =
      .error (.read group position.val (checked.column position).ordinal cause) := by
  simp [Checked.readCounts, failed, Except.mapError, Bind.bind, Except.bind]

theorem readGroup_ok_iff {checked : Checked} {limits : Limits} {group : Nat}
    {batch : Scan.Columns checked.schema Leaf.Events.Cell} :
    checked.readGroup limits group = .ok batch ↔
      checked.groupRows limits group = .ok batch.rowCount ∧
      ∀ position : Fin checked.width, ∃ counts,
        checked.readCounts limits group batch.rowCount position = .ok counts ∧
        batch.values position = cells (checked.schema.kind position).2 counts.val := by
  constructor
  · intro read
    obtain ⟨rows, rowOk, read⟩ := bind_ok read
    obtain ⟨columns, columnsOk, read⟩ := bind_ok read
    cases Except.ok.inj read
    exact ⟨rowOk, fun i => ⟨columns[i.val], vector_ok_iff.mp columnsOk i, rfl⟩⟩
  · rintro ⟨rowOk, each⟩
    classical
    let columns := Vector.ofFn fun i => Classical.choose (each i)
    have read : Vector.ofFnM (checked.readCounts limits group batch.rowCount) = .ok columns := by
      apply vector_ok_iff.mpr
      intro i
      simpa [columns] using (Classical.choose_spec (each i)).1
    simp only [Checked.readGroup, rowOk, read, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq]
    refine AlignedColumns.ext ?_ ?_
    · rfl
    funext i
    simpa [columns] using (Classical.choose_spec (each i)).2.symm

theorem readGroup_first_column_error {checked : Checked} {limits : Limits} {group rows : Nat}
    {before after : List (Fin checked.width)} {position : Fin checked.width} {values : List (Counts rows)}
    {cause : Leaf.Projection.Error}
    (rowOk : checked.groupRows limits group = .ok rows)
    (split : List.finRange checked.width = before ++ position :: after)
    (earlier : before.mapM (checked.readCounts limits group rows) = .ok values)
    (failed : checked.readCounts limits group rows position = .error cause) :
    checked.readGroup limits group = .error cause := by
  simp [Checked.readGroup, rowOk, vector_first_error split earlier failed, Bind.bind, Except.bind]

theorem readGroup_footer {checked : Checked} {limits : Limits} {group : Nat}
    {batch : Scan.Columns checked.schema Leaf.Events.Cell} (read : checked.readGroup limits group = .ok batch) :
    ∃ original, checked.snapshot.groupAt group = some original ∧
      batch.rowCount = original.numRows.toNat ∧ batch.rowCount ≤ limits.input.leaf.maxRows := by
  have rows := (readGroup_ok_iff.mp read).1
  cases selected : checked.snapshot.groupAt group with
  | none => simp [Checked.groupRows, selected] at rows
  | some original =>
    by_cases excess : limits.input.leaf.maxRows < original.numRows.toNat
    · simp [Checked.groupRows, selected, excess, Bind.bind, Except.bind] at rows
    · simp [Checked.groupRows, selected, excess, pure, Except.pure] at rows
      exact ⟨original, rfl, rows.symm, rows ▸ Nat.le_of_not_gt excess⟩

theorem readGroup_column {checked : Checked} {limits : Limits} {group : Nat}
    {batch : Scan.Columns checked.schema Leaf.Events.Cell} (read : checked.readGroup limits group = .ok batch)
    (position : Fin checked.width) :
    ∃ slots, AllCodecs.readGroup limits.codec limits.input.leaf (checked.column position) group = .ok slots ∧
      batch.values position = cells (checked.schema.kind position).2 (slots.map (Option.map Ticks.ticks)) ∧
      (batch.values position).map (Option.map Ticks.ticks) = slots.map (Option.map Ticks.ticks) := by
  obtain ⟨counts, success, values⟩ := (readGroup_ok_iff.mp read).2 position
  obtain ⟨slots, original, same⟩ := readCounts_ok_iff.mp success
  refine ⟨slots, original, same ▸ values, ?_⟩
  rw [values, same]
  rw [cells, List.map_map]
  conv => rhs; rw [← List.map_id counts.val]
  apply List.map_congr_left
  intro tick _
  cases tick <;> rfl

theorem project_readCounts_ok_iff (checked : Checked) (limits : Limits)
    (p : Scan.Projection checked.schema) (group rows : Nat) (position : Fin p.width) (counts : Counts rows) :
    (checked.project p).readCounts limits group rows position = .ok counts ↔
      checked.readCounts limits group rows (p.index position) = .ok counts := by
  rw [readCounts_ok_iff, readCounts_ok_iff]
  rfl

theorem readGroup_project (checked : Checked) (limits : Limits)
    (p : Scan.Projection checked.schema) {group : Nat}
    {batch : Scan.Columns checked.schema Leaf.Events.Cell} (read : checked.readGroup limits group = .ok batch) :
    (checked.project p).readGroup limits group = .ok (checked.projectBatch p batch) := by
  obtain ⟨rows, columns⟩ := readGroup_ok_iff.mp read
  apply readGroup_ok_iff.mpr
  refine ⟨rows, fun i => ?_⟩
  obtain ⟨counts, success, values⟩ := columns (p.index i)
  exact ⟨counts, (project_readCounts_ok_iff checked limits p group batch.rowCount i counts).2 success, values⟩

theorem readGroup_succeeds_iff (checked : Checked) (limits : Limits) (group : Nat) :
    (∃ batch, checked.readGroup limits group = .ok batch) ↔
      ∃ rows, checked.groupRows limits group = .ok rows ∧
        ∀ position : Fin checked.width, ∃ counts, checked.readCounts limits group rows position = .ok counts := by
  constructor
  · rintro ⟨batch, ok⟩
    obtain ⟨rows, columns⟩ := readGroup_ok_iff.mp ok
    exact ⟨batch.rowCount, rows, fun i => ⟨_, (columns i).choose_spec.1⟩⟩
  · rintro ⟨rows, rowOk, columns⟩
    classical
    let batch : Scan.Columns checked.schema Leaf.Events.Cell :=
      ⟨rows, fun i => cells (checked.schema.kind i).2 (Classical.choose (columns i)).val,
        fun i => by simpa only [cells, List.length_map] using (Classical.choose (columns i)).property⟩
    exact ⟨batch, readGroup_ok_iff.mpr ⟨rowOk, fun i =>
      ⟨_, Classical.choose_spec (columns i), rfl⟩⟩⟩

theorem projected_group_succeeds_iff (checked : Checked) (limits : Limits)
    (p : Scan.Projection checked.schema) (group : Nat) :
    (∃ batch, (checked.project p).readGroup limits group = .ok batch) ↔
      ∃ rows, checked.groupRows limits group = .ok rows ∧
        ∀ position : Fin p.width, ∃ counts, checked.readCounts limits group rows (p.index position) = .ok counts := by
  rw [readGroup_succeeds_iff]
  simp only [project_readCounts_ok_iff]
  rfl

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Projection
