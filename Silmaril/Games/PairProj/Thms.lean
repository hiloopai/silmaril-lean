module

public import Silmaril.Games.Pair.Defs
public import Silmaril.Games.Handler.Thms
import Silmaril.Proofs.Games.PairProj.Inr

/-!
# Right projection of a pairing

* **`Strategy.pair_restrict_inr`**: restricting a pairing to its right interface gives the
  right component, `(σ₁.pair σ₂).restrict (Sig.Hom.inr F₁ F₂) = σ₂`. This is the counterpart of
  `Strategy.pair_restrict_inl` (`Silmaril.Games.Pair.Thms`). The left component, which receives no
  question, may be any strategy, also a stateful one.
* `Strategy.pair_comp_ofHom_inr`: the same, as a composition with the forwarding handler.

Proofs in `Silmaril.Proofs.Games.PairProj.Inr`, by mutual simulation as for the left projection.
-/

public section

namespace Silmaril.Games

universe u

variable {E F₁ F₂ : Sig.{u}}

namespace Strategy

/-- **Restricting a pairing to its right interface gives the right component.** -/
theorem pair_restrict_inr (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) :
    (σ₁.pair σ₂).restrict (Sig.Hom.inr F₁ F₂) = σ₂ :=
  Silmaril.Proofs.Games.PairProj.pair_restrict_inr σ₁ σ₂

/-- The right projection, as a composition with the forwarding handler. -/
theorem pair_comp_ofHom_inr (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) :
    (σ₁.pair σ₂).comp (ofHandler (Handler.ofHom (Sig.Hom.inr F₁ F₂))) = σ₂ :=
  pair_restrict_inr σ₁ σ₂

end Strategy

end Silmaril.Games
