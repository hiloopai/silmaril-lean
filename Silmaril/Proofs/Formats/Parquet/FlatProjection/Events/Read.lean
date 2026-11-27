module

public import Silmaril.Formats.Parquet.FlatProjection.Events.Defs
import Silmaril.Formats.Parquet.FlatProjection.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Thms
import Silmaril.Semantics.Relational.Scan.Thms
import Init.Data.List.FinRange

public section

namespace Silmaril.Proofs.Formats.Parquet.FlatProjection.Events

open Silmaril.Formats Parquet
open Silmaril.Formats.Parquet.FlatProjection.Events
open Silmaril.Relational

private theorem sequence_ok_iff {ε : Type} {n : Nat} {α : Fin n → Type}
    {read : (i : Fin n) → Except ε (α i)} {values : (i : Fin n) → α i} :
    sequence read = .ok values ↔ ∀ i, read i = .ok (values i) := by
  induction n with
  | zero =>
    have same : (fun i : Fin 0 => i.elim0 : (i : Fin 0) → α i) = values := funext fun i => i.elim0
    rw [sequence, same]
    simp
  | succ n ih =>
    constructor
    · intro ok i
      cases first : read 0 with
      | error cause => simp [sequence, first, Bind.bind, Except.bind] at ok
      | ok head =>
        cases rest : sequence (fun i : Fin n => read i.succ) with
        | error cause => simp [sequence, first, rest, Bind.bind, Except.bind] at ok
        | ok tail =>
          have h : Fin.cases (motive := α) head tail = values := by
            simpa [sequence, first, rest, Bind.bind, Except.bind, pure, Except.pure] using ok
          cases h
          refine Fin.cases ?_ (fun j => ?_) i
          · simpa using first
          · simpa using (ih.mp rest) j
    · intro each
      have rest := ih.mpr (fun i : Fin n => each i.succ)
      have h : Fin.cases (motive := α) (values 0) (fun i => values i.succ) = values := by
        funext i
        exact Fin.cases (by simp) (fun j => by simp) i
      simp [sequence, each 0, rest, h, Bind.bind, Except.bind, pure, Except.pure]

private theorem sequence_erase {ε : Type} {n : Nat} {α : Fin n → Type}
    (read : (i : Fin n) → Except ε (α i)) :
    (sequence read).map (fun _ => ()) =
      ((List.finRange n).mapM fun i => (read i).map (fun _ => ())).map (fun _ => ()) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sequence, List.finRange_succ, List.mapM_cons, List.mapM_map]
    cases first : read 0 with
    | error cause => simp [Bind.bind, Except.bind, Except.map]
    | ok head =>
      have tail := ih (fun i : Fin n => read i.succ)
      simp only [Function.comp_def]
      cases r : sequence (fun i : Fin n => read i.succ) <;>
        cases l : (List.finRange n).mapM (fun i => (read i.succ).map (fun _ => ())) <;>
        simp only [r, l] at tail <;>
        simp [Bind.bind, Except.bind, Except.map, pure, Except.pure]
      all_goals simp only [Except.map, Except.error.injEq, reduceCtorEq] at tail
      exact tail

theorem sequence_first_error {ε : Type} {n : Nat} {α : Fin n → Type}
    {read : (i : Fin n) → Except ε (α i)} {before after : List (Fin n)}
    {position : Fin n} {cause : ε} {done : List Unit}
    (split : List.finRange n = before ++ position :: after)
    (earlier : before.mapM (fun i => (read i).map (fun _ => ())) = .ok done)
    (failed : read position = .error cause) : sequence read = .error cause := by
  have h := sequence_erase read
  rw [split, List.mapM_append, List.mapM_cons] at h
  simp [failed, Bind.bind, Except.bind, Except.map] at h
  cases eq : sequence read <;> simp_all [Except.map]

theorem bindOrdinal_exact {limits : Footer.Limits} {snapshot : Snapshot.Checked} {ordinal : Nat}
    {bound : Bound snapshot} (read : bindOrdinal limits snapshot ordinal = .ok bound) :
    bound.ordinal = ordinal := by
  unfold bindOrdinal at read
  split at read
  · split at read
    · contradiction
    · rename_i value accepted
      cases Except.ok.inj read
      have selected := (Timestamp.Leaf.bind_sound accepted).2.1
      simp [Bound.ordinal, selected]
  · cases primitive : FlatProjection.bindOrdinal snapshot ordinal with
    | error cause => simp [primitive, Bind.bind, Except.bind, Except.mapError] at read
    | ok original =>
      have agrees := FlatProjection.bind_ordinal primitive
      cases original with
      | int32 name layout binding =>
        simp [primitive, Bind.bind, Except.bind, Except.mapError, pure, Except.pure] at read
        cases read
        exact agrees
      | byteArray name layout binding =>
        simp only [primitive, Bind.bind, Except.bind, Except.mapError] at read
        cases leaf : Footer.ColumnOrder.readFlat limits snapshot binding.columnOrdinal with
        | error cause => simp [leaf] at read
        | ok selected =>
          cases annotation : Plain.ByteArray.Utf8.readAnnotation selected with
          | error cause => simp [leaf, annotation] at read
          | ok value =>
            simp [leaf, annotation, pure, Except.pure] at read
            cases read
            exact agrees

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

private theorem unmap_error_ok {ε δ α : Type} {result : Except ε α} {wrap : ε → δ} {value : α}
    (accepted : result.mapError wrap = .ok value) : result = .ok value := by
  cases result <;> cases accepted
  rfl

theorem openFile_exact {limits : Limits} {input : Bytes} {ordinals : Array Nat} {checked : Checked}
    (opened : openFile limits input ordinals = .ok checked) :
    Snapshot.check (Failure := Unit) limits.primitive.column.snapshot input = .ok checked.snapshot ∧
      ∃ width : checked.width = ordinals.size, ∀ i : Fin checked.width,
        bindOrdinal limits.primitive.column.snapshot.footer checked.snapshot ordinals[i.cast width] =
          .ok (checked.bindings i) ∧ (checked.bindings i).ordinal = ordinals[i.cast width] := by
  unfold openFile at opened
  dsimp only at opened
  split at opened
  · contradiction
  split at opened
  · contradiction
  obtain ⟨snapshot, accepted, opened⟩ := bind_ok opened
  split at opened
  · contradiction
  split at opened
  · contradiction
  obtain ⟨columns, bound, opened⟩ := bind_ok opened
  cases Except.ok.inj opened
  refine ⟨unmap_error_ok accepted, rfl, fun i => ?_⟩
  have selected := unmap_error_ok (sequence_ok_iff.mp bound i)
  exact ⟨selected, bindOrdinal_exact selected⟩

private theorem readColumn_ok_iff {checked : Checked} {limits : Limits} {group rows : Nat}
    {i : Fin checked.width} {column : Column (checked.schema.kind i).2 rows} :
    checked.readColumn limits group rows i = .ok column ↔
      (checked.bindings i).read limits group = .ok column.val := by
  unfold Checked.readColumn
  dsimp only
  cases read : (checked.bindings i).read limits group with
  | error cause => simp [Except.mapError, Bind.bind, Except.bind]
  | ok values =>
    simp only [Except.mapError, Bind.bind, Except.bind, Except.ok.injEq]
    constructor
    · intro accepted
      split at accepted
      · exact congrArg Subtype.val (Except.ok.inj accepted)
      · contradiction
    · rintro rfl
      simp [column.property, pure, Except.pure]

theorem readGroup_ok_iff {checked : Checked} {limits : Limits} {group : Nat}
    {batch : Scan.Columns checked.schema Cell} :
    checked.readGroup limits group = .ok batch ↔
      checked.groupRows limits group = .ok batch.rowCount ∧
      ∀ i, (checked.bindings i).read limits group = .ok (batch.values i) := by
  constructor
  · intro read
    obtain ⟨rows, rowOk, read⟩ := bind_ok read
    obtain ⟨columns, columnsOk, read⟩ := bind_ok read
    cases Except.ok.inj read
    exact ⟨rowOk, fun i => readColumn_ok_iff.mp (sequence_ok_iff.mp columnsOk i)⟩
  · rintro ⟨rowOk, each⟩
    let columns : (i : Fin checked.width) → Column (checked.schema.kind i).2 batch.rowCount :=
      fun i => ⟨batch.values i, batch.length_eq i⟩
    have read : sequence (checked.readColumn limits group batch.rowCount) = .ok columns :=
      sequence_ok_iff.mpr fun i => readColumn_ok_iff.mpr (each i)
    simp only [Checked.readGroup, rowOk, read, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq]
    cases batch
    rfl

theorem readGroup_footer {checked : Checked} {limits : Limits} {group : Nat}
    {batch : Scan.Columns checked.schema Cell} (read : checked.readGroup limits group = .ok batch) :
    ∃ original, checked.snapshot.groupAt group = some original ∧
      batch.rowCount = original.numRows.toNat ∧ batch.rowCount ≤ limits.primitive.column.column.maxRows := by
  have rows := (readGroup_ok_iff.mp read).1
  cases selected : checked.snapshot.groupAt group with
  | none => simp [Checked.groupRows, selected] at rows
  | some original =>
    by_cases excess : limits.primitive.column.column.maxRows < original.numRows.toNat
    · simp [Checked.groupRows, selected, excess, Bind.bind, Except.bind] at rows
    · simp [Checked.groupRows, selected, excess, pure, Except.pure] at rows
      exact ⟨original, rfl, rows.symm, rows ▸ Nat.le_of_not_gt excess⟩

theorem readGroup_first_column_error {checked : Checked} {limits : Limits} {group rows : Nat}
    {before after : List (Fin checked.width)} {position : Fin checked.width}
    {done : List Unit} {cause : Error}
    (rowOk : checked.groupRows limits group = .ok rows)
    (split : List.finRange checked.width = before ++ position :: after)
    (earlier : before.mapM (fun i => (checked.readColumn limits group rows i).map (fun _ => ())) = .ok done)
    (failed : checked.readColumn limits group rows position = .error cause) :
    checked.readGroup limits group = .error cause := by
  simp [Checked.readGroup, rowOk, sequence_first_error split earlier failed, Bind.bind, Except.bind]

theorem readGroup_project (checked : Checked) (limits : Limits)
    (p : Scan.Projection checked.schema) {group : Nat}
    {batch : Scan.Columns checked.schema Cell} (read : checked.readGroup limits group = .ok batch) :
    (checked.project p).readGroup limits group = .ok (checked.projectBatch p batch) := by
  obtain ⟨rows, columns⟩ := readGroup_ok_iff.mp read
  exact readGroup_ok_iff.mpr ⟨rows, fun i => columns (p.index i)⟩

end Silmaril.Proofs.Formats.Parquet.FlatProjection.Events
