module

public import Silmaril.Wasm.Component.Reference.Types.Subtype.Defs
public import Silmaril.Wasm.Component.Reference.Types.Basic.Defs

/-!
# `Types.Subtype`: laws of the component reference

Theorems of the component reference copy `Types.Subtype`, refined out of
`Silmaril.Raw.Wasm.Component.Types.Subtype`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Types

universe u v w
variable {R : Type u} {S : Type w} {X : Type v}

theorem Remapping.apply_of_not_mem [DecidableEq R] (m : Remapping R) {binders : List R}
    {r : R} (h : r ∉ binders) : m.apply binders r = r := by
  simp only [Remapping.apply, h, ↓reduceIte]

variable {XSub : X → X → Prop}

theorem Entity.ListSub.of_forall {as : List (String × Entity R X)} :
    ∀ {bs : List (String × Entity R X)},
      (∀ n b, (n, b) ∈ bs → ∃ a, (n, a) ∈ as ∧ Entity.Sub XSub a b) →
        Entity.ListSub XSub as bs
  | [], _ => .nil
  | (n, b) :: bs, h => by
    obtain ⟨a, ha, hs⟩ := h n b List.mem_cons_self
    exact .cons ha hs (Entity.ListSub.of_forall fun n' b' hm =>
      h n' b' (List.mem_cons_of_mem _ hm))

end Silmaril.Wasm.Component.Types
