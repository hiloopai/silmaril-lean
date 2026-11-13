module

public import Silmaril.Wasm.Component.Wiring.Thms
public import Silmaril.Games.Pair.Thms

/-!
# Laws of pairing

The structural component passes (dead instance elimination, flattening of
nested components, inlining of stateless wiring into instances) need five
laws relating `Strategy.pair` to composition. They are bundled as `PairLaws`
and proved in `Silmaril.Games.Pair.Thms`; `pairLaws : PairLaws` is the proof.
Results taking `(L : PairLaws)` as an explicit argument are kept; their
unconditional versions apply them to `pairLaws`.

* `hdist` — a *handler* below a pairing is duplicated:
  `ofHandler h ≫ (σ₁ ∥ σ₂) = (ofHandler h ≫ σ₁) ∥ (ofHandler h ≫ σ₂)`. True
  in this model because a handler keeps no state between questions; it fails
  for stateful strategies (the left side shares one instance).
* `psum` — handlers above a pairing that keep the two sides apart act on
  each side: `(σ₁ ∥ σ₂) ≫ ofHandler (h₁ ⊕ h₂) = (σ₁ ≫ h₁) ∥ (σ₂ ≫ h₂)`.
* `pproj` — projection: restricting a pairing to its left interface
  gives the left component.
* `gflat` — re-association with a stateless left component:
  `(h ∥ σ) ≫ (fst ∥ τ) = h ∥ ((h ∥ σ) ≫ τ)` for a handler `h`. This is what
  flattening a nested component into its parent needs.
* `cp` — the pairing of two handlers is the handler of their copairing.

Here `∥` is `Strategy.pair` and `≫` is `Strategy.comp`. In `Silmaril.Games` they are
`Strategy.ofHandler_comp_pair`, `Strategy.pair_comp_sumMap`,
`Strategy.pair_restrict_inl`, `Strategy.pair_comp_pair_fst` and
`Strategy.ofHandler_pair_ofHandler`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open Silmaril.Games

/-- The sum of two handlers: each side is implemented on its own side. -/
def Handler.sum {F₁ F₂ G₁ G₂ : Sig.{0}} (h₁ : Handler F₁ G₁) (h₂ : Handler F₂ G₂) :
    Handler (F₁ ⊕ₛ F₂) (G₁ ⊕ₛ G₂)
  | .inl q => (h₁ q).interp (Handler.ofHom (Sig.Hom.inl F₁ F₂))
  | .inr q => (h₂ q).interp (Handler.ofHom (Sig.Hom.inr F₁ F₂))

/-- The copairing of two handlers with a common lower interface. -/
def Handler.case {E F₁ F₂ : Sig.{0}} (h₁ : Handler E F₁) (h₂ : Handler E F₂) :
    Handler E (F₁ ⊕ₛ F₂)
  | .inl q => h₁ q
  | .inr q => h₂ q

/-- The five laws of pairing used by the structural passes. They are proved
in `Silmaril.Games.Pair.Thms`; `pairLaws` bundles the proofs. Results stated with
an explicit `(L : PairLaws)` hypothesis remain available, and are applied to
`pairLaws` by their unconditional versions. -/
structure PairLaws : Prop where
  /-- Handlers are duplicated below a pairing. -/
  hdist : ∀ {E F F₁ F₂ : Sig.{0}} (h : Handler E F) (σ₁ : Strategy F F₁) (σ₂ : Strategy F F₂),
    (Strategy.ofHandler h).comp (σ₁.pair σ₂) =
      ((Strategy.ofHandler h).comp σ₁).pair ((Strategy.ofHandler h).comp σ₂)
  /-- Sum handlers above a pairing act side by side. -/
  psum : ∀ {E F₁ F₂ G₁ G₂ : Sig.{0}} (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂)
    (h₁ : Handler F₁ G₁) (h₂ : Handler F₂ G₂),
    (σ₁.pair σ₂).comp (Strategy.ofHandler (Handler.sum h₁ h₂)) =
      (σ₁.comp (Strategy.ofHandler h₁)).pair (σ₂.comp (Strategy.ofHandler h₂))
  /-- The left projection of a pairing. -/
  pproj : ∀ {E F₁ F₂ : Sig.{0}} (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂),
    (σ₁.pair σ₂).restrict (Sig.Hom.inl F₁ F₂) = σ₁
  /-- Re-association of a pairing with a stateless left component. -/
  gflat : ∀ {E F₁ F₂ G : Sig.{0}} (h : Handler E F₁) (σ : Strategy E F₂)
    (τ : Strategy (F₁ ⊕ₛ F₂) G),
    ((Strategy.ofHandler h).pair σ).comp
        ((Strategy.ofHandler (Handler.ofHom (Sig.Hom.inl F₁ F₂))).pair τ) =
      (Strategy.ofHandler h).pair (((Strategy.ofHandler h).pair σ).comp τ)
  /-- The pairing of two handlers is the handler of their copairing. -/
  cp : ∀ {E F₁ F₂ : Sig.{0}} (h₁ : Handler E F₁) (h₂ : Handler E F₂),
    (Strategy.ofHandler h₁).pair (Strategy.ofHandler h₂) =
      Strategy.ofHandler (Handler.case h₁ h₂)

/-- `Handler.case` is the copairing of `Silmaril.Games`. -/
theorem Handler.case_eq_copair {E F₁ F₂ : Sig.{0}} (h₁ : Handler E F₁) (h₂ : Handler E F₂) :
    Handler.case h₁ h₂ = Handler.copair h₁ h₂ := by
  funext q
  rcases q with q | q <;> rfl

/-- `Handler.sum` is the sum of handlers of `Silmaril.Games`. -/
theorem Handler.sum_eq_sumMap {F₁ F₂ G₁ G₂ : Sig.{0}} (h₁ : Handler F₁ G₁)
    (h₂ : Handler F₂ G₂) : Handler.sum h₁ h₂ = Handler.sumMap h₁ h₂ := by
  funext q
  rcases q with q | q <;> rfl

/-- **The pairing laws hold** (`Silmaril.Games.Pair.Thms`). -/
theorem pairLaws : PairLaws where
  hdist := Strategy.ofHandler_comp_pair
  psum σ₁ σ₂ h₁ h₂ := by rw [Handler.sum_eq_sumMap]; exact Strategy.pair_comp_sumMap σ₁ σ₂ h₁ h₂
  pproj := Strategy.pair_restrict_inl
  gflat := Strategy.pair_comp_pair_fst
  cp h₁ h₂ := by rw [Handler.case_eq_copair]; exact Strategy.ofHandler_pair_ofHandler h₁ h₂

end Silmaril.Wasm.Component
