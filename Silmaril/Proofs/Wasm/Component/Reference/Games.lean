module

public import Silmaril.Games.Handler.Thms
public import Silmaril.Games.LTS.Thms
public import Silmaril.Games.Pair.Defs

/-!
# Two-move plays through compositions, handlers and pairings

Small lemmas producing the play `ask q · ans q a` of a composite strategy from the plays of
its parts: a handler that answers `q` by one call (`four_ofHandler_call`) or at once
(`two_ofHandler_pure`), composition through one call (`two_comp`) or without calls
(`two_comp_upper`), and pairing (`two_pair_inr`).
-/

public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Games

universe u

variable {E F G : Sig.{u}}

/-- The two-move play answering `q` with `a`. -/
abbrev two (q : F.Op) (a : F.Ar q) : List (Move E F) := [.inr (.ask q), .inr (.ans q a)]

/-- The four-move play answering `q` with `a` through one call `q'` answered `a'`. -/
abbrev four (q : G.Op) (q' : F.Op) (a' : F.Ar q') (a : G.Ar q) : List (Move F G) :=
  [.inr (.ask q), .inl (.ask q'), .inl (.ans q' a'), .inr (.ans q a)]

theorem legal_two (q : F.Op) (a : F.Ar q) : Legal (two (E := E) q a) :=
  ⟨_, .cons (.ask q) (.cons (.ret q a) (.nil _))⟩

theorem legal_four (q : G.Op) (q' : F.Op) (a' : F.Ar q') (a : G.Ar q) : Legal (four q q' a' a) :=
  ⟨_, .cons (.ask q) (.cons (.call q q') (.cons (.reply q q' a') (.cons (.ret q a) (.nil _))))⟩

/-- A handler answering `q` at once. -/
theorem two_ofHandler_pure {h : Handler E F} {q : F.Op} {a : F.Ar q} (hq : h q = .pure a) :
    two q a ∈ Strategy.ofHandler h := by
  exact Strategy.mem_ofHandler.mpr ⟨Reduction.State.idle,
    .vis (.ask q) (.vis (.ret (show h q = .pure a from hq)) (.nil _))⟩

/-- A handler answering `q` through one call. -/
theorem four_ofHandler_call {h : Handler F G} {q : G.Op} {q' : F.Op} {k : F.Ar q' → Prog F (G.Ar q)}
    {a' : F.Ar q'} {a : G.Ar q} (hq : h q = .call q' k) (hk : k a' = .pure a) :
    four q q' a' a ∈ Strategy.ofHandler h := by
  exact Strategy.mem_ofHandler.mpr ⟨Reduction.State.idle,
    .vis (.ask q) (.vis (.call (show h q = .call q' k from hq))
      (.vis (Reduction.Step.resume (R := h.toReduction) q q' k a') (.vis (.ret (show k a' = .pure a from hk)) (.nil _))))⟩

/-- Composition through one call. -/
theorem two_comp {σ : Strategy E F} {τ : Strategy F G} {q : G.Op} {q' : F.Op} {a' : F.Ar q'}
    {a : G.Ar q} (hσ : two q' a' ∈ σ) (hτ : four q q' a' a ∈ τ) : two q a ∈ σ.comp τ :=
  ⟨_, hσ, _, hτ, .right _ (.sync _ (.sync _ (.right _ .nil)))⟩

/-- Composition without calls. -/
theorem two_comp_upper {σ : Strategy E F} {τ : Strategy F G} {q : G.Op} {a : G.Ar q}
    (hτ : two q a ∈ τ) : two q a ∈ σ.comp τ :=
  ⟨[], σ.nil_mem, _, hτ, .right _ (.right _ .nil)⟩

/-- A play of the right component of a pairing. -/
theorem two_pair_inr {F₁ F₂ : Sig.{u}} {σ₁ : Strategy E F₁} {σ₂ : Strategy E F₂} {q : F₂.Op}
    {a : F₂.Ar q} (h : two q a ∈ σ₂) :
    two (F := F₁ ⊕ₛ F₂) (.inr q) a ∈ σ₁.pair σ₂ :=
  ⟨legal_two _ _, σ₁.nil_mem, h⟩

end Silmaril.Proofs.Wasm.Component.Reference
