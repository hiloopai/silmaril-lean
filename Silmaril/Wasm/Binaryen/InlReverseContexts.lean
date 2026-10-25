module

public import Silmaril.Wasm.Binaryen.InlReverseFlat

@[expose] public section

/-! # Reconstructing original contexts from selected inlined steps

The generic relation preserves values and flat heads in both directions.
These right-oriented inversions recover the original suffix from the actual
target execution. Lifting the matched head then gives an actual original step
with the target's selected result, without a numerical determinism assumption.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Validation Numerics SingleThreaded InlS

variable {H : Type} {p : Prm} {P : Profile}

theorem AN.val?_eq {a b : Admin} (related : AN p a b) : a.val? = b.val? := by
  cases related <;> rfl

theorem AN.val_inv_right {a : Admin} {v : Val} (related : AN p a v.toAdmin) :
    a = v.toAdmin :=
  Admin.eq_of_val? (by rw [related.val?_eq, Admin.val?_toAdmin])

theorem LN.vals_inv_right : ∀ {vs : List Val} {original : List Admin},
    LN p original (vals vs) → original = vals vs
  | [], _, .nil => rfl
  | _ :: _, _, .cons head rest => by
    rw [head.val_inv_right, LN.vals_inv_right rest]
    rfl

theorem LN.append_inv_right : ∀ {A B original : List Admin}, LN p original (A ++ B) →
    ∃ oldA oldB, original = oldA ++ oldB ∧ LN p oldA A ∧ LN p oldB B
  | [], _, original, related => ⟨[], original, rfl, .nil, related⟩
  | _ :: _, _, _, .cons head rest => by
    obtain ⟨oldA, oldB, rfl, left, right⟩ := LN.append_inv_right rest
    exact ⟨_ :: oldA, oldB, rfl, .cons head left, right⟩

theorem LN.cons_inv_right {a : Admin} {rest original : List Admin}
    (related : LN p original (a :: rest)) :
    ∃ oldHead oldRest, original = oldHead :: oldRest ∧ AN p oldHead a ∧
      LN p oldRest rest := by
  cases related with
  | cons head tail => exact ⟨_, _, rfl, head, tail⟩

theorem LN.vals_cons_inv_right : ∀ {vs : List Val} {a : Admin}
    {rest original : List Admin}, LN p original (vals vs ++ a :: rest) →
    ∃ oldHead oldRest, original = vals vs ++ oldHead :: oldRest ∧ AN p oldHead a ∧
      LN p oldRest rest
  | [], _, _, _, related => LN.cons_inv_right related
  | _ :: _, _, _, _, .cons head tail => by
    obtain ⟨oldHead, oldRest, shape, related, rest⟩ := LN.vals_cons_inv_right tail
    exact ⟨oldHead, oldRest, by rw [head.val_inv_right, shape]; rfl, related, rest⟩

theorem AN.eq_of_flat_right {a b : Admin} (related : AN p a b)
    (nonlabel : ∀ n cont body, b ≠ .label n cont body)
    (nonhandler : ∀ n catches body, b ≠ .handler n catches body)
    (nonframe : ∀ n frame body, b ≠ .frame n frame body) : a = b := by
  cases related with
  | label _ => exact absurd rfl (nonlabel _ _ _)
  | handler _ => exact absurd rfl (nonhandler _ _ _)
  | frame _ => exact absurd rfl (nonframe _ _ _)
  | _ => rfl

theorem LN.flat_inv_right {vs : List Val} {head : Admin} {rest original : List Admin}
    (nonlabel : ∀ n cont body, head ≠ .label n cont body)
    (nonhandler : ∀ n catches body, head ≠ .handler n catches body)
    (nonframe : ∀ n frame body, head ≠ .frame n frame body)
    (related : LN p original (vals vs ++ head :: rest)) :
    ∃ oldRest, original = vals vs ++ head :: oldRest ∧ LN p oldRest rest := by
  obtain ⟨oldHead, oldRest, shape, headRelated, tail⟩ := LN.vals_cons_inv_right related
  rw [AN.eq_of_flat_right headRelated nonlabel nonhandler nonframe] at shape
  exact ⟨oldRest, shape, tail⟩

theorem LN.trap_inv_right {original : List Admin} (related : LN p original [.trap]) :
    original = [.trap] := by
  cases related with
  | cons head tail => cases head; cases tail; rfl

theorem LN.throwing_inv_right {original : List Admin} {a : Nat}
    (related : LN p original (throwing a)) : original = throwing a := by
  obtain ⟨rest, shape, tail⟩ := LN.flat_inv_right
    (vs := [.ref (.exn a)]) (head := .plain .throwRef) (rest := [])
    (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
    (fun _ _ _ h => by cases h) related
  cases tail
  exact shape

/-- Lift a selected generic flat head through its actual values and suffix.
The recovered source suffix may contain changed caller activations; it need
not be syntactically identical to the target suffix. -/
theorem reverse_generic_flat_context (parameters : PrmOk p)
    {s t : Store H} {frame : Frame} {vs args : List Val} {head : Admin}
    {rest original : List Admin} {next : Config H} (stores : SR p s t)
    (related : LN p original (vals vs ++ (vals args ++ head :: rest)))
    (nonlabel : ∀ n cont body, head ≠ .label n cont body)
    (nonhandler : ∀ n catches body, head ≠ .handler n catches body)
    (nonframe : ∀ n frame body, head ≠ .frame n frame body)
    (selected : Det.Head P t frame args head next) :
    ∃ originalNext : Config H,
      Step P Det.noHost ⟨s, frame, original⟩ originalNext ∧
      MR p .gen originalNext
        ⟨next.store, next.frame, vals vs ++ next.code ++ rest⟩ ∧
      SR p originalNext.store next.store := by
  have combined : vals vs ++ (vals args ++ head :: rest) =
      vals (vs ++ args) ++ head :: rest := by simp
  rw [combined] at related
  obtain ⟨oldRest, shape, tail⟩ :=
    LN.flat_inv_right nonlabel nonhandler nonframe related
  obtain ⟨oldNext, step, ⟨sameFrame, codeRelated⟩, nextStores⟩ :=
    reverse_generic_flat_head parameters stores nonlabel nonhandler nonframe selected
  refine ⟨⟨oldNext.store, oldNext.frame, vals vs ++ oldNext.code ++ oldRest⟩,
    ?_, ⟨sameFrame, LN.append (LN.append (LN.of_vals vs) codeRelated) tail⟩, nextStores⟩
  have lifted := Det.lift_instrs vs oldRest _ _ step.toStep
  simpa [shape, List.append_assoc] using lifted

/-- Reconstruct a real source bubble from the chosen target bubble, including
the discarded portion of the original suffix. Related activations in that
suffix need not have identical syntax. -/
theorem reverse_generic_bubble {s t : Store H} {frame : Frame}
    {pp q : List Val} {X u rest original : List Admin}
    (bubble : Det.IsBubble X) (discarded : q ≠ [] ∨ u ≠ [])
    (related : LN p original (vals (pp ++ q) ++ X ++ (u ++ rest)))
    (stores : SR p s t) :
    ∃ originalNext : Config H,
      Step P Det.noHost ⟨s, frame, original⟩ originalNext ∧
      MR p .gen originalNext ⟨t, frame, vals pp ++ X ++ rest⟩ ∧
      SR p originalNext.store t := by
  obtain ⟨left, right, rfl, leftRelated, rightRelated⟩ := LN.append_inv_right related
  obtain ⟨values, oldX, rfl, valuesRelated, bubbleRelated⟩ :=
    LN.append_inv_right leftRelated
  obtain ⟨oldU, oldRest, rfl, uRelated, restRelated⟩ := LN.append_inv_right rightRelated
  rw [LN.vals_inv_right valuesRelated]
  have sameBubble : oldX = X := by
    rcases bubble with rfl | ⟨a, rfl⟩
    · exact LN.trap_inv_right bubbleRelated
    · exact LN.throwing_inv_right bubbleRelated
  subst oldX
  refine ⟨⟨s, frame, vals pp ++ X ++ oldRest⟩,
    Det.Bubble.toStep ⟨pp, q, X, oldU, oldRest, rfl, bubble, ?_, rfl⟩,
    ⟨rfl, LN.append (LN.append (LN.of_vals pp) (LN.refl p X)) restRelated⟩, stores⟩
  rcases discarded with nonempty | nonempty
  · exact .inl nonempty
  · right
    intro empty
    rw [empty] at uRelated
    cases uRelated
    exact nonempty rfl

end Silmaril.Wasm.Binaryen.InlR
