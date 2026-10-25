module

public import Silmaril.Wasm.Binaryen.InlReverseControl

@[expose] public section

/-! # Actual reverse bubbles of relocated callees

`LI` preserves sequence structure in both directions. Consequently every
selected target trap or exception bubble discards corresponding original
values or instructions, and can be replayed as an actual original step.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Validation SingleThreaded InlS

variable {H : Type} {p : Prm} {P : Numerics.Profile}

theorem LI.append_reverse {d : Nat} :
    ∀ {A B original : List Admin}, LI p d original (A ++ B) →
    ∃ oldA oldB, original = oldA ++ oldB ∧ LI p d oldA A ∧ LI p d oldB B
  | [], _, original, related => ⟨[], original, rfl, .nil, related⟩
  | _ :: _, _, _, .cons head tail => by
    obtain ⟨oldA, oldB, rfl, left, right⟩ := LI.append_reverse tail
    exact ⟨_ :: oldA, oldB, rfl, .cons head left, right⟩

/-- Reconstruct the actual original suffix discarded by a selected callee
bubble, preserving its related surviving suffix and both actual stores. -/
theorem reverse_callee_bubble {d : Nat} {L : List (Option Val)}
    {s t : Store H} {F : Frame} {pp q : List Val}
    {kernel discarded rest original : List Admin}
    (moduleEq : F.module = p.mi) (prefixLength : L.length = p.base)
    (locals : F.locals.length = p.ext) (stores : SR p s t)
    (bubble : Det.IsBubble kernel) (nonempty : q ≠ [] ∨ discarded ≠ [])
    (related : LI p d original (vals (pp ++ q) ++ kernel ++ (discarded ++ rest))) :
    ∃ originalNext : Config H,
      Step P Det.noHost ⟨s, F, original⟩ originalNext ∧
      MR p (.i d L) originalNext ⟨t, ⟨L ++ F.locals, p.mi⟩, vals pp ++ kernel ++ rest⟩ ∧
      SR p originalNext.store t := by
  obtain ⟨left, right, rfl, leftRelated, rightRelated⟩ := LI.append_reverse related
  obtain ⟨values, oldKernel, rfl, valuesRelated, kernelRelated⟩ :=
    LI.append_reverse leftRelated
  obtain ⟨oldDiscarded, oldRest, rfl, discardedRelated, restRelated⟩ :=
    LI.append_reverse rightRelated
  rw [LI.vals_reverse valuesRelated]
  have sameKernel : oldKernel = kernel := by
    rcases bubble with rfl | ⟨address, rfl⟩
    · exact LI.trap_reverse kernelRelated
    · exact LI.throwing_reverse kernelRelated
  subst oldKernel
  refine ⟨⟨s, F, vals pp ++ kernel ++ oldRest⟩,
    Det.Bubble.toStep ⟨pp, q, kernel, oldDiscarded, oldRest, rfl, bubble, ?_, rfl⟩,
    ⟨moduleEq, prefixLength, locals, rfl,
      LI.append (LI.append (LI.of_vals d pp) kernelRelated) restRelated⟩, stores⟩
  rcases nonempty with nonempty | nonempty
  · exact .inl nonempty
  · right
    intro empty
    rw [empty] at discardedRelated
    cases discardedRelated
    exact nonempty rfl

end Silmaril.Wasm.Binaryen.InlR
