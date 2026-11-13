module

public import Silmaril.Wasm.Atlas.Variant.Defs

@[expose] public section

/-!
# Stuttering simulations give inclusion of behaviours

`Variant.behavioursR_subset_of_sim` needs one target step per source step. The wider fusion
needs a weaker form: a source step may be matched by **no** target step, provided a measure of
the source configuration decreases (`behavioursR_subset_of_stutter`). Finite runs are then
matched by finite runs, and an infinite source run by an infinite target run, because between
two target steps there are only finitely many stuttering source steps (`next_step`).

New proofs.
-/

namespace Silmaril.Proofs.Wasm.Wasmi.LooseW

open Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Atlas.Variant

variable {H : Type} {S T Rel : Config H → Config H → Prop} {μ : Config H → Nat}

/-- The step obligation of a stuttering simulation: a target step, or no step with a smaller
measure. -/
def StutterStep (S T Rel : Config H → Config H → Prop) (μ : Config H → Nat) : Prop :=
  ∀ (c c' d : Config H), S c c' → Rel c d → ∃ d', Rel c' d' ∧ (T d d' ∨ (d' = d ∧ μ c' < μ c))

/-- Finite source runs are matched by finite target runs. -/
theorem steps_of_stutter (step : StutterStep S T Rel μ) {c c' d : Config H}
    (hs : Relation.ReflTransGen S c c') (h : Rel c d) :
    ∃ d', Relation.ReflTransGen T d d' ∧ Rel c' d' := by
  induction hs with
  | refl => exact ⟨d, .refl, h⟩
  | tail _ hs ih =>
    obtain ⟨d₁, hd₁, hr₁⟩ := ih
    obtain ⟨d₂, hr₂, ht | ⟨he, -⟩⟩ := step _ _ _ hs hr₁
    · exact ⟨d₂, hd₁.tail ht, hr₂⟩
    · exact ⟨d₁, hd₁, he ▸ hr₂⟩

/-- From a diverging source configuration, the target takes a step to a configuration related
to a diverging source configuration (by induction on the measure). -/
theorem next_step (step : StutterStep S T Rel μ) :
    ∀ (n : Nat) {c d : Config H}, μ c = n → Rel c d → InfiniteTrace S c →
      ∃ d', T d d' ∧ ∃ c', Rel c' d' ∧ InfiniteTrace S c' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c d hn h hdiv
  obtain ⟨c', hs, hdiv'⟩ := hdiv.unfold
  obtain ⟨d', hr', ht | ⟨rfl, hlt⟩⟩ := step _ _ _ hs h
  · exact ⟨d', ht, c', hr', hdiv'⟩
  · exact ih _ (hn ▸ hlt) rfl hr' hdiv'

/-- **A stuttering simulation gives inclusion of behaviours.** Every source step is matched by
a target step or by none, the measure decreasing; a terminal source configuration is related
only to a terminal target configuration with the same result. -/
theorem behavioursR_subset_of_stutter (step : StutterStep S T Rel μ)
    (terminal : ∀ {c d : Config H} {r : Result}, Rel c d → c.code = r.toAdmin →
      d.code = r.toAdmin) {c d : Config H} (h : Rel c d) :
    behavioursR S c ⊆ behavioursR T d := by
  rintro b (⟨c', r, hs, hc, rfl⟩ | ⟨rfl, hdiv⟩)
  · obtain ⟨d', hd, hr'⟩ := steps_of_stutter step hs h
    exact Or.inl ⟨d', r, hd, terminal hr' hc, rfl⟩
  · refine Or.inr ⟨rfl, InfiniteTrace.coinduct (fun d => ∃ c, Rel c d ∧ InfiniteTrace S c) ?_
      ⟨c, h, hdiv⟩⟩
    rintro d ⟨c, hr, hc⟩
    exact next_step step _ rfl hr hc

end Silmaril.Proofs.Wasm.Wasmi.LooseW
