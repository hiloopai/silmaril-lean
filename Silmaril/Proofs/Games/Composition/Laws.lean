module

public import Silmaril.Games.Composition.Defs
public import Silmaril.Games.Zip.Thms
public import Silmaril.Games.Strategy.Thms
import Silmaril.Proofs.Games.Composition.Unit

/-!
# Composition and copycat: proofs of the laws

Proofs for `Silmaril.Games.Composition.Thms`: copycat is a two-sided unit (from the
interaction lemmas of `Silmaril.Proofs.Games.Composition.Unit`), composition is
associative (from `Zip.assoc`), and composition preserves nonempty joins in
each argument.
-/

public section

namespace Silmaril.Proofs.Games.Composition

open Silmaril.Games Silmaril.Games.Strategy

universe u

variable {E F G H : Sig.{u}}

/-- Copycat is a left unit. -/
theorem id_comp (σ : Strategy E F) : (Strategy.id E).comp σ = σ := by
  ext p
  constructor
  · rintro ⟨c, ⟨w, hw, hc⟩, s, hs, h⟩
    obtain ⟨x, hx⟩ := σ.legal hs
    rcases id_comp_out hw hc h (.inl rfl) hx with
      hp | ⟨o, y, rfl, hst, ho⟩
    · exact σ.of_prefix hs hp
    · exact σ.receptive hs hx hst ho
  · intro hp
    obtain ⟨x, hx⟩ := σ.legal hp
    exact ⟨_, ⟨_, (lower_alternating hx).1 (.inl rfl),
      List.prefix_refl _⟩, p, hp, zip_double_lower p⟩

/-- Copycat is a right unit. -/
theorem comp_id (σ : Strategy E F) : σ.comp (Strategy.id F) = σ := by
  ext p
  constructor
  · rintro ⟨s, hs, c, ⟨w, hw, hc⟩, h⟩
    obtain ⟨x, hx⟩ := σ.legal hs
    rcases comp_id_out hw hc h hx with
      hp | ⟨o, y, rfl, hst, ho⟩
    · exact σ.of_prefix hs hp
    · exact σ.receptive hs hx hst ho
  · intro hp
    obtain ⟨x, hx⟩ := σ.legal hp
    exact ⟨p, hp, _, ⟨_, (upper_alternating hx).1 rfl,
      List.prefix_refl _⟩, zip_double_upper p⟩

/-- Composition is associative. -/
theorem comp_assoc (σ : Strategy E F) (τ : Strategy F G) (ρ : Strategy G H) :
    (σ.comp τ).comp ρ = σ.comp (τ.comp ρ) := by
  ext p
  constructor
  · rintro ⟨u, ⟨s, hs, t, ht, h₁⟩, r, hr, h₂⟩
    obtain ⟨v, hv₁, hv₂⟩ := Zip.assoc.1 ⟨u, h₁, h₂⟩
    exact ⟨s, hs, v, ⟨t, ht, r, hr, hv₁⟩, hv₂⟩
  · rintro ⟨s, hs, v, ⟨t, ht, r, hr, hv₁⟩, hv₂⟩
    obtain ⟨u, h₁, h₂⟩ := Zip.assoc.2 ⟨v, hv₁, hv₂⟩
    exact ⟨u, ⟨s, hs, t, ht, h₁⟩, r, hr, h₂⟩

/-- Composition preserves nonempty joins on the left. -/
theorem comp_sSup_left {S : Set (Strategy E F)} (hS : S.Nonempty) (τ : Strategy F G) :
    (sSup S).comp τ = sSup ((fun σ => σ.comp τ) '' S) := by
  ext p
  rw [mem_comp, mem_sSup_of_nonempty (hS.image _)]
  constructor
  · rintro ⟨s, hs, t, ht, hz⟩
    obtain ⟨σ, hσ, hs⟩ := (mem_sSup_of_nonempty hS).1 hs
    exact ⟨_, ⟨σ, hσ, rfl⟩, s, hs, t, ht, hz⟩
  · rintro ⟨_, ⟨σ, hσ, rfl⟩, s, hs, t, ht, hz⟩
    exact ⟨s, (mem_sSup_of_nonempty hS).2 ⟨σ, hσ, hs⟩, t, ht, hz⟩

/-- Composition preserves nonempty joins on the right. -/
theorem comp_sSup_right (σ : Strategy E F) {S : Set (Strategy F G)} (hS : S.Nonempty) :
    σ.comp (sSup S) = sSup ((fun τ => σ.comp τ) '' S) := by
  ext p
  rw [mem_comp, mem_sSup_of_nonempty (hS.image _)]
  constructor
  · rintro ⟨s, hs, t, ht, hz⟩
    obtain ⟨τ, hτ, ht⟩ := (mem_sSup_of_nonempty hS).1 ht
    exact ⟨_, ⟨τ, hτ, rfl⟩, s, hs, t, ht, hz⟩
  · rintro ⟨_, ⟨τ, hτ, rfl⟩, s, hs, t, ht, hz⟩
    exact ⟨s, hs, t, (mem_sSup_of_nonempty hS).2 ⟨τ, hτ, ht⟩, hz⟩

end Silmaril.Proofs.Games.Composition
