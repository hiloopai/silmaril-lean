module

public import Silmaril.Games.DivComp.Defs
public import Silmaril.Games.Composition.Thms

/-!
# Composition of divergence-observing strategies: proofs of the laws

Proofs for `Silmaril.Games.DivComp.Thms`: an infinite interaction moves forever on
one side, composition is monotone, and the least reading `ofStrategy` preserves
composition.
-/

public section

namespace Silmaril.Proofs.Games.DivComp.Laws

open Silmaril.Games Silmaril.Games.DStrategy

universe u

variable {E F G : Sig.{u}}

/-- An infinite interaction moves forever on at least one side. -/
theorem unbounded_or {σ : DStrategy E F} {τ : DStrategy F G}
    (i : InfInteraction σ τ) : i.s.Unbounded ∨ i.t.Unbounded := by
  by_contra h
  simp only [not_or, Chain.Unbounded, not_forall, not_exists, not_le] at h
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h
  obtain ⟨n, hn⟩ := i.unbounded (a + b)
  have := ha n
  have := hb n
  omega

/-- Refinement is a precongruence for composition. -/
theorem comp_mono {σ σ' : DStrategy E F} {τ τ' : DStrategy F G} (hσ : σ ≤ σ') (hτ : τ ≤ τ') :
    σ.comp τ ≤ σ'.comp τ' := by
  let lift : InfInteraction σ τ → InfInteraction σ' τ' := fun i =>
    { i with
      mem_s := fun n => hσ.1 (i.mem_s n)
      mem_t := fun n => hτ.1 (i.mem_t n)
      lim_s := fun h => hσ.2.2 (i.lim_s h)
      lim_t := fun h => hτ.2.2 (i.lim_t h) }
  refine ⟨Strategy.comp_mono hσ.1 hτ.1, ?_, ?_⟩
  · rintro p (⟨s, t, hz, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩ | ⟨i, hi⟩)
    · exact .inl ⟨s, t, hz, .inl ⟨hσ.2.1 hs, hτ.1 ht⟩⟩
    · exact .inl ⟨s, t, hz, .inr ⟨hσ.1 hs, hτ.2.1 ht⟩⟩
    · exact .inr ⟨lift i, hi⟩
  · rintro _ ⟨i, hu, rfl⟩
    exact ⟨lift i, hu, rfl⟩

/-- The least reading preserves composition: strategies without infinite plays
cannot chatter forever. -/
theorem ofStrategy_comp (σ : Strategy E F) (τ : Strategy F G) :
    (ofStrategy σ).comp (ofStrategy τ) = ofStrategy (σ.comp τ) := by
  have none : InfInteraction (ofStrategy σ) (ofStrategy τ) → False := fun i => by
    rcases unbounded_or i with h | h
    · exact i.lim_s h
    · exact i.lim_t h
  refine ext rfl ?_ ?_
  · ext p
    simp only [ofStrategy, Set.mem_empty_iff_false, iff_false]
    rintro (⟨s, t, -, ⟨hs, -⟩ | ⟨-, ht⟩⟩ | ⟨i, -⟩)
    · exact hs
    · exact ht
    · exact none i
  · ext I
    simp only [ofStrategy, Set.mem_empty_iff_false, iff_false]
    rintro ⟨i, -⟩
    exact none i

end Silmaril.Proofs.Games.DivComp.Laws
