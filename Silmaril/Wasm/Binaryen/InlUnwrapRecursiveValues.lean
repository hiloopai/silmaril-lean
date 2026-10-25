module

public import Silmaril.Wasm.Binaryen.InlUnwrapTypedPhase

@[expose] public section

/-! # Recursive typed value normalization for unwrap

A value-only bare side can correspond to multiple original blocks and running
labels. Normalization follows the finite relation derivation while preserving
its ambient typing. It executes only administrative entry/completion steps and
therefore retains the exact original store and frame.
-/

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded

variable {R : List Instr} {H : Type} {P : Profile}

/-- Structural unwrap pairs preserve whether an administrative head is a value. -/
theorem UA.val?_eq {a b : Admin} (related : UA R a b) : a.val? = b.val? := by
  cases related with
  | plain related => cases related <;> rfl
  | _ => rfl

/-- A value on the bare side has exactly the same original value head. -/
theorem UA.eq_of_val_right {a : Admin} {v : Val} (related : UA R a v.toAdmin) :
    a = v.toAdmin := by
  apply Admin.eq_of_val?
  rw [UA.val?_eq related, Admin.val?_toAdmin]

private theorem split_values {x y : List Admin} {us : List Val}
    (shape : x ++ y = vals us) :
    ∃ u v : List Val, x = vals u ∧ y = vals v ∧ us = u ++ v := by
  have all : (x ++ y).all Admin.isVal = true := by rw [shape]; simp
  rw [List.all_append, Bool.and_eq_true] at all
  obtain ⟨u, rfl⟩ := exists_vals_of_all all.1
  obtain ⟨v, rfl⟩ := exists_vals_of_all all.2
  exact ⟨u, v, rfl, rfl, Execution.Core.Sim.vals_injective (by simpa using shape.symm)⟩

/-- Normalize every target-only block/running-label phase when the transformed
side is already values. This recursion decreases relation depth rather than
claiming that stripping a target wrapper decreases the source code rank. -/
theorem UL.typed_values_reverse :
    ∀ {x y : List Admin}, UL R x y →
    ∀ {s : Store H} {f : Frame} {vs us : List Val},
      ContextTyped ⟨s, f, vals vs ++ x⟩ → y = vals us →
      Steps P Det.noHost ⟨s, f, vals vs ++ x⟩ ⟨s, f, vals vs ++ vals us⟩
  | _, _, .nil, _, _, _, _, _, values => by rw [← values]
  | _, _, (@UL.cons _ a b os ns head tail), s, f, vs, us, typed, values => by
    cases us with
    | nil => cases values
    | cons v us =>
      simp only [vals_cons'] at values
      obtain ⟨rfl, rfl⟩ := List.cons.inj values
      obtain rfl := UA.eq_of_val_right head
      have typed' : ContextTyped ⟨s, f, vals (vs ++ [v]) ++ os⟩ := by
        simpa only [vals_append, vals_cons', Execution.Core.vals_nil', List.append_assoc,
          List.singleton_append] using typed
      simpa only [vals_append, vals_cons', Execution.Core.vals_nil', List.append_assoc,
        List.singleton_append] using UL.typed_values_reverse tail typed' rfl
  | _, _, (@UL.site _ bt os ns tail), s, f, vs, us, typed, values => by
    obtain ⟨u, v, bodyValues, tailValues, rfl⟩ := split_values values
    have typedBlock : ContextTyped ⟨s, f, vals vs ++ [.plain (.block bt R)]⟩ := by
      apply ContextTyped.suffix
      simpa only [List.append_assoc, List.singleton_append] using typed
    have first := Steps.append_right (block_values_run (P := P) typedBlock bodyValues) os
    have typedTail : ContextTyped ⟨s, f, vals (vs ++ u) ++ os⟩ := by
      have after := typed.steps (Closure.steps_congr first (by simp) rfl)
      simpa only [vals_append, List.append_assoc] using after
    have last := UL.typed_values_reverse tail typedTail tailValues
    refine Relation.ReflTransGen.trans (b := ⟨s, f, vals (vs ++ u) ++ os⟩) ?_ ?_
    · simpa only [vals_append, List.append_assoc, List.singleton_append] using first
    · simpa only [vals_append, List.append_assoc] using last
  | _, _, (@UL.run _ n X X' os ns body safe tail), s, f, vs, us, typed, values => by
    obtain ⟨u, v, bodyValues, tailValues, rfl⟩ := split_values values
    have typedBody : ContextTyped ⟨s, f, X⟩ := by
      apply ContextTyped.label (n := n) (cont := []) (vs := vs) (rest := os)
      simpa only [List.append_assoc, List.singleton_append] using typed
    have inside := UL.typed_values_reverse body (vs := []) typedBody bodyValues
    have inside' : Steps P Det.noHost ⟨s, f, X⟩ ⟨s, f, vals u⟩ := by
      simpa only [Execution.Core.vals_nil', List.nil_append] using inside
    have complete := (Closure.steps_label inside' n []).tail Step.labelVals
    have first := Steps.append_right (Steps.vals_left complete vs) os
    have typedTail : ContextTyped ⟨s, f, vals (vs ++ u) ++ os⟩ := by
      have after := typed.steps (Closure.steps_congr first (by simp) rfl)
      simpa only [vals_append, List.append_assoc] using after
    have last := UL.typed_values_reverse tail typedTail tailValues
    refine Relation.ReflTransGen.trans (b := ⟨s, f, vals (vs ++ u) ++ os⟩) ?_ ?_
    · simpa only [vals_append, List.append_assoc, List.singleton_append] using first
    · simpa only [vals_append, List.append_assoc] using last
  | _, _, .foldIf _ _ _ _ _ _, _, _, _, _, _, values => by
    have all := congrArg (List.all · Admin.isVal) values
    simp [Admin.isVal, Admin.val?] at all
  | _, _, .foldBlock _ _ _ _, _, _, _, _, _, values => by
    have all := congrArg (List.all · Admin.isVal) values
    simp [Admin.isVal, Admin.val?] at all
  | _, _, .foldLabel _ _ _ _, _, _, _, _, _, values => by
    have all := congrArg (List.all · Admin.isVal) values
    simp [Admin.isVal, Admin.val?] at all
  | _, _, .foldExit kernel _, _, _, _, _, _, values => by
    have all := congrArg (List.all · Admin.isVal) values
    rcases kernel with rfl | ⟨a, rfl⟩
    · simp [Admin.isVal, Admin.val?] at all
    · simp [Admin.isVal, Admin.val?] at all

end Silmaril.Wasm.Binaryen.Unwrap
