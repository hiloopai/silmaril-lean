module

public import Silmaril.Games.Pair.Defs

/-!
# Swapping the two sides of a pairing: definitions

* `Sig.Hom.swap F₁ F₂ : Sig.Hom (F₂ ⊕ₛ F₁) (F₁ ⊕ₛ F₂)`: the renaming that exchanges the two
  summands (`Sig.Hom.case` of the injections).
* `Split.swapMove`: the same exchange on the moves of `E ↠ F₂ ⊕ₛ F₁`; lower moves are unchanged.

`Silmaril.Games.PairSwap.Thms` proves that restricting `σ₁.pair σ₂` along `Sig.Hom.swap` is
`σ₂.pair σ₁` (`Strategy.pair_restrict_swap`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Games

universe u

/-- The renaming exchanging the summands of a sum of signatures. -/
def Sig.Hom.swap (F₁ F₂ : Sig.{u}) : Sig.Hom (F₂ ⊕ₛ F₁) (F₁ ⊕ₛ F₂) :=
  Sig.Hom.case (Sig.Hom.inr F₁ F₂) (Sig.Hom.inl F₁ F₂)

namespace Split

variable {E F₁ F₂ : Sig.{u}}

/-- Exchange the sides of a move of `E ↠ F₂ ⊕ₛ F₁`. -/
def swapMove : Move E (F₂ ⊕ₛ F₁) → Move E (F₁ ⊕ₛ F₂)
  | .inl e => .inl e
  | .inr (.ask (.inl q)) => .inr (.ask (.inr q))
  | .inr (.ask (.inr q)) => .inr (.ask (.inl q))
  | .inr (.ans (.inl q) r) => .inr (.ans (.inr q) r)
  | .inr (.ans (.inr q) r) => .inr (.ans (.inl q) r)

end Split

end Silmaril.Games
