module

public import Silmaril.Games.Composition.Defs
public import Silmaril.Games.Zip.Thms
public import Silmaril.Games.Strategy.Thms
import Silmaril.Proofs.Games.Composition.Laws

/-!
# Composition and copycat: laws

* Refinement is a precongruence: `Strategy.comp_mono`.
* Copycat is a two-sided unit: `Strategy.id_comp`, `Strategy.comp_id`.
* Composition is associative: `Strategy.comp_assoc`, a direct consequence of
  the associativity of interaction (`Zip.assoc`).
* Composition preserves nonempty joins in each argument
  (`Strategy.comp_sSup_left`, `Strategy.comp_sSup_right`). It does not
  preserve the empty join: `⊥.comp τ` lets `τ` run until its first call.

The unit laws need receptiveness (see `Silmaril.Games.Strategy.Defs`); their
proofs are in `Silmaril.Proofs.Games.Composition.Unit`; the header proofs of the
unit, associativity and join laws are in `Silmaril.Proofs.Games.Composition.Laws`.
-/

public section

namespace Silmaril.Games.Strategy

universe u

variable {E F G H : Sig.{u}}

/-- Composition is monotone in its left argument. -/
theorem comp_mono_left {σ σ' : Strategy E F} (h : σ ≤ σ') (τ : Strategy F G) :
    σ.comp τ ≤ σ'.comp τ :=
  fun _ ⟨s, hs, t, ht, hz⟩ => ⟨s, h hs, t, ht, hz⟩

/-- Composition is monotone in its right argument. -/
theorem comp_mono_right (σ : Strategy E F) {τ τ' : Strategy F G} (h : τ ≤ τ') :
    σ.comp τ ≤ σ.comp τ' :=
  fun _ ⟨s, hs, t, ht, hz⟩ => ⟨s, hs, t, h ht, hz⟩

/-- Refinement is a precongruence for composition. -/
theorem comp_mono {σ σ' : Strategy E F} {τ τ' : Strategy F G} (hσ : σ ≤ σ') (hτ : τ ≤ τ') :
    σ.comp τ ≤ σ'.comp τ' :=
  (comp_mono_left hσ τ).trans (comp_mono_right σ' hτ)

/-- Copycat is a left unit. -/
theorem id_comp (σ : Strategy E F) : (Strategy.id E).comp σ = σ :=
  Silmaril.Proofs.Games.Composition.id_comp σ

/-- Copycat is a right unit. -/
theorem comp_id (σ : Strategy E F) : σ.comp (Strategy.id F) = σ :=
  Silmaril.Proofs.Games.Composition.comp_id σ

/-- Composition is associative. -/
theorem comp_assoc (σ : Strategy E F) (τ : Strategy F G) (ρ : Strategy G H) :
    (σ.comp τ).comp ρ = σ.comp (τ.comp ρ) :=
  Silmaril.Proofs.Games.Composition.comp_assoc σ τ ρ

/-- Composition preserves nonempty joins on the left. -/
theorem comp_sSup_left {S : Set (Strategy E F)} (hS : S.Nonempty) (τ : Strategy F G) :
    (sSup S).comp τ = sSup ((fun σ => σ.comp τ) '' S) :=
  Silmaril.Proofs.Games.Composition.comp_sSup_left hS τ

/-- Composition preserves nonempty joins on the right. -/
theorem comp_sSup_right (σ : Strategy E F) {S : Set (Strategy F G)} (hS : S.Nonempty) :
    σ.comp (sSup S) = sSup ((fun τ => σ.comp τ) '' S) :=
  Silmaril.Proofs.Games.Composition.comp_sSup_right σ hS

end Silmaril.Games.Strategy
