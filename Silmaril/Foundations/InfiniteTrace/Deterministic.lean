module

public import Silmaril.Foundations.InfiniteTrace

/-! # Right-unique transition relations

A right-unique relation has at most one successor per state, so from a given
state there is one maximal run. Two reachable states that cannot step are
equal, an infinite path passes through every reachable state, and a run that
reaches a state without successors is not infinite.

`reach_final_eq`, `infinite_of_reach` and `not_infinite_of_final` are the facts
proved in the section `Deterministic` of `Silmaril.Wasm.Compile.EndToEnd`,
restated here over arbitrary universes so that code outside the Wasm compiler
can use them without importing it. The copies in `EndToEnd` are left alone:
their statements are part of that file's public interface. `stepFn_rightUnique`
and `of_injective` cover the two ways the machine models present a
deterministic step: a partial function `State → Option State`, and a function
into an outcome type whose "continue" constructor is injective (for example
`step t = .retired t'`).
-/

@[expose] public section

namespace Silmaril.RightUnique

open Relation

variable {α β : Type*} {R : α → α → Prop}

theorem reach_final_eq (hR : Relator.RightUnique R) {a b c : α} (hb : ReflTransGen R a b)
    (hc : ReflTransGen R a c) (fb : ∀ x, ¬ R b x) (fc : ∀ x, ¬ R c x) : b = c := by
  rcases ReflTransGen.total_of_right_unique hR hb hc with h | h
  · rcases h.cases_head with h | ⟨d, hd, -⟩
    · exact h
    · exact absurd hd (fb d)
  · rcases h.cases_head with h | ⟨d, hd, -⟩
    · exact h.symm
    · exact absurd hd (fc d)

theorem infinite_of_reach (hR : Relator.RightUnique R) {a b : α} (h : ReflTransGen R a b)
    (hi : InfiniteTrace R a) : InfiniteTrace R b := by
  induction h with
  | refl => exact hi
  | tail _ hs ih =>
    obtain ⟨c, hc, hc'⟩ := ih.unfold
    rwa [hR hs hc]

theorem not_infinite_of_final (hR : Relator.RightUnique R) {a b : α} (h : ReflTransGen R a b)
    (fb : ∀ x, ¬ R b x) : ¬ InfiniteTrace R a := fun hi => by
  obtain ⟨c, hc, -⟩ := (infinite_of_reach hR h hi).unfold
  exact fb c hc

/-- The graph of a partial step function is right-unique. -/
theorem stepFn_rightUnique (f : α → Option α) :
    Relator.RightUnique (fun a b => f a = some b) := fun _ _ _ hb hc =>
  Option.some_injective _ (hb.symm.trans hc)

/-- `f a = c a'` is right-unique in `a'` when `c` is injective. This covers step
functions into an outcome type, such as `step t = .retired t'`. -/
theorem of_injective (f : α → β) (c : α → β) (hc : Function.Injective c) :
    Relator.RightUnique (fun a a' => f a = c a') := fun _ _ _ hb hc' =>
  hc (hb.symm.trans hc')

end Silmaril.RightUnique
