module

public import Silmaril.Games.Pair.Defs
public import Silmaril.Games.Handler.Thms
import Silmaril.Proofs.Games.Pair.LTS
import Silmaril.Proofs.Games.Pair.Cp
import Silmaril.Proofs.Games.Pair.Dist
import Silmaril.Proofs.Games.Pair.Proj
import Silmaril.Proofs.Games.Pair.Sum
import Silmaril.Proofs.Games.Pair.Flat

/-!
# Laws of pairing

Here `σ₁ ∥ σ₂` is `Strategy.pair` and `≫` is `Strategy.comp`.

* `Strategy.ofHandler_pair_ofHandler`: the pairing of two handlers is the
  handler of their copairing.
* `Strategy.ofHandler_comp_pair`: a handler below a pairing is duplicated,
  `h ≫ (σ₁ ∥ σ₂) = (h ≫ σ₁) ∥ (h ≫ σ₂)`. This uses that handlers keep no
  state between questions; it fails for stateful strategies in place of `h`.
* `Strategy.pair_comp_sumMap`: a sum of handlers above a pairing acts side by
  side, `(σ₁ ∥ σ₂) ≫ (h₁ ⊕ h₂) = (σ₁ ≫ h₁) ∥ (σ₂ ≫ h₂)`.
* `Strategy.pair_restrict_inl`: restricting a pairing to its left interface
  gives the left component.
* `Strategy.pair_comp_pair_fst`: re-association with a stateless left
  component, `(h ∥ σ) ≫ (fst ∥ τ) = h ∥ ((h ∥ σ) ≫ τ)`.

All five are proved by exhibiting mutual weak simulations between transition
systems denoting the two sides (`LTS.Denotes`): strategies are denoted by
their own transition systems (`Strategy.toLTS`), handlers by their reduction
semantics, composition by `LTS.comp` and pairing by `LTS.pair`
(`LTS.Denotes.pair`). Proofs are in `Silmaril.Proofs.Games.Pair`.
-/

public section

namespace Silmaril.Games

universe u

variable {E F F₁ F₂ G G₁ G₂ : Sig.{u}}

/-- The pairing of transition systems denotes the pairing of strategies. -/
theorem LTS.Denotes.pair {L₁ : LTS E F₁} {L₂ : LTS E F₂} {σ₁ : Strategy E F₁}
    {σ₂ : Strategy E F₂} (h₁ : L₁.Denotes σ₁) (h₂ : L₂.Denotes σ₂) :
    (L₁.pair L₂).Denotes (σ₁.pair σ₂) :=
  Silmaril.Proofs.Games.Pair.denotes_pair h₁ h₂

namespace Strategy

/-- The pairing of two handlers is the handler of their copairing. -/
theorem ofHandler_pair_ofHandler (h₁ : Handler E F₁) (h₂ : Handler E F₂) :
    (ofHandler h₁).pair (ofHandler h₂) = ofHandler (Handler.copair h₁ h₂) :=
  Silmaril.Proofs.Games.Pair.ofHandler_pair_ofHandler h₁ h₂

/-- A handler below a pairing is duplicated. -/
theorem ofHandler_comp_pair (h : Handler E F) (σ₁ : Strategy F F₁) (σ₂ : Strategy F F₂) :
    (ofHandler h).comp (σ₁.pair σ₂) = ((ofHandler h).comp σ₁).pair ((ofHandler h).comp σ₂) :=
  Silmaril.Proofs.Games.Pair.ofHandler_comp_pair h σ₁ σ₂

/-- A sum of handlers above a pairing acts side by side. -/
theorem pair_comp_sumMap (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) (h₁ : Handler F₁ G₁)
    (h₂ : Handler F₂ G₂) :
    (σ₁.pair σ₂).comp (ofHandler (Handler.sumMap h₁ h₂)) =
      (σ₁.comp (ofHandler h₁)).pair (σ₂.comp (ofHandler h₂)) :=
  Silmaril.Proofs.Games.Pair.pair_comp_sumMap σ₁ σ₂ h₁ h₂

/-- Restricting a pairing to its left interface gives the left component. -/
theorem pair_restrict_inl (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) :
    (σ₁.pair σ₂).restrict (Sig.Hom.inl F₁ F₂) = σ₁ :=
  Silmaril.Proofs.Games.Pair.pair_restrict_inl σ₁ σ₂

/-- Re-association of a pairing with a stateless left component. -/
theorem pair_comp_pair_fst (h : Handler E F₁) (σ : Strategy E F₂)
    (τ : Strategy (F₁ ⊕ₛ F₂) G) :
    ((ofHandler h).pair σ).comp ((ofHandler (Handler.ofHom (Sig.Hom.inl F₁ F₂))).pair τ) =
      (ofHandler h).pair (((ofHandler h).pair σ).comp τ) :=
  Silmaril.Proofs.Games.Pair.pair_comp_pair_fst h σ τ

end Strategy

end Silmaril.Games
