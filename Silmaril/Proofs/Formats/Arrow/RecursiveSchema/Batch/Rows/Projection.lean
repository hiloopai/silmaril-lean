module

public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows.Defs
import Batteries.Data.List.Lemmas

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Rows

open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Semantics (Column)

private theorem cells_of_forall {positions : List (Column × Nat)} {values : Row}
    (related : List.Forall₂ (fun (column, slot) value => CellWire column slot value)
      positions values) : CellsWire positions values := by
  induction related with
  | nil => exact .nil
  | @cons head _ _ _ first _ ih =>
    obtain ⟨column, slot⟩ := head
    exact .cons first ih

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

theorem readCell_wire {depth slot : Nat} {column : Column} {cell : Cell}
    (read : readCell depth (IndexedColumn.ofColumn column) slot = .ok cell) :
    CellWire column slot cell := by
  induction depth generalizing column slot cell with
  | zero => simp [readCell] at read
  | succ depth ih =>
    obtain ⟨presence, payload, children⟩ := column
    simp only [IndexedColumn.ofColumn, readCell] at read
    by_cases visible : presence.visible[slot]? = some true
    · have reached : Reached presence slot := visible
      cases valid : presence.valid[slot]? with
      | none => simp [visible, valid, throw] at read
      | some bit =>
        cases bit with
        | false =>
          simp [visible, valid, pure, Except.pure] at read
          subst cell
          exact .null reached valid
        | true =>
          have present : Present presence slot := ⟨reached, valid⟩
          cases payload with
          | int32 words =>
            cases word : words[slot]? with
            | none => simp [visible, valid, IndexedPayload.ofPayload, word, throw] at read
            | some value =>
              simp [visible, valid, IndexedPayload.ofPayload, word, pure, Except.pure] at read
              subst cell
              exact .int32 present word
          | int64 words =>
            cases word : words[slot]? with
            | none => simp [visible, valid, IndexedPayload.ofPayload, word, throw] at read
            | some value =>
              simp [visible, valid, IndexedPayload.ofPayload, word, pure, Except.pure] at read
              subst cell
              exact .int64 present word
          | struct =>
            simp only [visible, valid, IndexedPayload.ofPayload, bne_self_eq_false, Bool.false_eq_true,
              ite_false, List.mapM_map] at read
            obtain ⟨fields, decoded, read⟩ := bind_ok read
            cases Except.ok.inj read
            apply CellWire.struct present
            apply cells_of_forall
            rw [List.forall₂_map_left_iff]
            exact (List.mapM_eq_ok_iff_forall₂.mp decoded).imp fun _ _ field => ih field
          | list offsets =>
            cases children with
            | nil => simp [visible, valid, IndexedPayload.ofPayload, throw] at read
            | cons child rest =>
              cases rest with
              | cons other rest => simp [visible, valid, IndexedPayload.ofPayload, throw] at read
              | nil =>
                cases lo : offsets[slot]? with
                | none => simp [visible, valid, IndexedPayload.ofPayload, lo, throw] at read
                | some start =>
                  cases hi : offsets[slot + 1]? with
                  | none => simp [visible, valid, IndexedPayload.ofPayload, lo, hi, throw] at read
                  | some stop =>
                    simp only [visible, valid, IndexedPayload.ofPayload, bne_self_eq_false,
                      Bool.false_eq_true, ite_false, List.map_cons, List.map_nil, lo, hi] at read
                    split at read
                    · contradiction
                    · rename_i extent
                      obtain ⟨values, decoded, read⟩ := bind_ok read
                      cases Except.ok.inj read
                      have ordered : start ≤ stop := by
                        by_contra! reversed
                        apply extent
                        simp [reversed]
                      apply CellWire.list present lo hi ordered
                      apply cells_of_forall
                      rw [List.forall₂_map_left_iff]
                      exact (List.mapM_eq_ok_iff_forall₂.mp decoded).imp fun _ _ item => ih item
    · have invisible : (presence.visible[slot]? != some true) = true := by
        simpa using visible
      simp [invisible, throw, bind, Except.bind] at read

theorem project_wire {depth : Nat} {physical : Formats.Arrow.RecursiveSchema.Batch.Semantics.Observation}
    {logical : Observation} (read : project depth physical = .ok logical) :
    ProjectionWire physical logical := by
  unfold project at read
  obtain ⟨rows, decoded, read⟩ := bind_ok read
  cases Except.ok.inj read
  refine ⟨rfl, (List.mapM_eq_ok_iff_forall₂.mp decoded).imp ?_⟩
  intro index row checked
  apply cells_of_forall
  rw [List.forall₂_map_left_iff]
  have raw := mapError_ok checked
  rw [List.mapM_map] at raw
  exact (List.mapM_eq_ok_iff_forall₂.mp raw).imp fun _ _ cell => readCell_wire cell

end Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Rows
