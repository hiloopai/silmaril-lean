module

public import Silmaril.Games.Pair.Thms
public import Silmaril.Games.PairSwap.Thms
import Silmaril.Proofs.Games.PairMap.Sim

/-!
# Pairing is functorial

Write `σ₁ ∥ σ₂` for `Strategy.pair`, `≫` for `Strategy.comp`, and `inl`, `inr` for the
forwarding handlers of the injections `Sig.Hom.inl F₁ F₂`, `Sig.Hom.inr F₁ F₂` (so `inl ≫ τ`
is `τ : Strategy F₁ G` running over the lower interface `F₁ ⊕ₛ F₂`, on its left summand).

* **`Strategy.pair_comp_mapLeft`**: `(σ₁ ∥ σ₂) ≫ ((inl ≫ τ) ∥ inr) = (σ₁ ≫ τ) ∥ σ₂`. Running
  `τ` on the left factor of a pairing, and forwarding the right factor, is pairing `σ₁ ≫ τ`
  with `σ₂`.
* `Strategy.pair_comp_cross`: the same with the summands of the result exchanged,
  `(σ₁ ∥ σ₂) ≫ (inr ∥ (inl ≫ τ)) = σ₂ ∥ (σ₁ ≫ τ)` (by `Strategy.pair_restrict_swap`).

No hypothesis on `σ₁`, `σ₂` or `τ`: unlike `Strategy.pair_comp_pair_fst`, nothing is shared,
since `σ₁` is only reached through `τ` and `σ₂` only through the forwarding. This is what
lets two stateful instances sharing a stateless environment be reordered
(`Silmaril.Wasm.Component.Algebra.ParComm`).

The proof (`Silmaril.Proofs.Games.PairMap.Sim`) exhibits mutual simulations between the
transition systems of the two sides, with the same plays of `σ₁`, `τ` and `σ₂`; the plays of
`inl ≫ τ` are those of `τ` with renamed lower moves (`Silmaril.Proofs.Games.PairMap.Lift`, from
`Game.mem_reduct_iff_rel`).
-/

public section

namespace Silmaril.Games

universe u

variable {E F₁ F₂ G : Sig.{u}}

namespace Strategy

/-- **Pairing is functorial in its left factor.** -/
theorem pair_comp_mapLeft (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) (τ : Strategy F₁ G) :
    (σ₁.pair σ₂).comp
        (((ofHandler (Handler.ofHom (Sig.Hom.inl F₁ F₂))).comp τ).pair
          (ofHandler (Handler.ofHom (Sig.Hom.inr F₁ F₂)))) =
      (σ₁.comp τ).pair σ₂ :=
  Silmaril.Proofs.Games.PairMap.pair_comp_mapLeft σ₁ σ₂ τ

/-- **Pairing is functorial in its left factor**, with the summands of the result exchanged. -/
theorem pair_comp_cross (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) (τ : Strategy F₁ G) :
    (σ₁.pair σ₂).comp
        ((ofHandler (Handler.ofHom (Sig.Hom.inr F₁ F₂))).pair
          ((ofHandler (Handler.ofHom (Sig.Hom.inl F₁ F₂))).comp τ)) =
      σ₂.pair (σ₁.comp τ) := by
  have hs : ((((ofHandler (Handler.ofHom (Sig.Hom.inl F₁ F₂))).comp τ).pair
      (ofHandler (Handler.ofHom (Sig.Hom.inr F₁ F₂)))).comp
        (ofHandler (Handler.ofHom (Sig.Hom.swap G F₂)))) =
      (ofHandler (Handler.ofHom (Sig.Hom.inr F₁ F₂))).pair
        ((ofHandler (Handler.ofHom (Sig.Hom.inl F₁ F₂))).comp τ) :=
    pair_comp_ofHom_swap _ _
  rw [← hs, ← comp_assoc, pair_comp_mapLeft, pair_comp_ofHom_swap]

end Strategy

end Silmaril.Games
