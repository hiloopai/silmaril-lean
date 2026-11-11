module

public import Silmaril.Games.Strategy.Defs
public import Mathlib.Order.GaloisConnection.Defs

/-!
# Strategies that observe divergence and infinite behaviour

A `Silmaril.Games.Strategy` is a prefix-closed receptive set of *finite* plays.
It cannot tell a component that diverges from one that has not answered yet,
and composition hides infinite internal chatter. This module adds the two
missing observations, in the style of the failures/divergences/infinite-traces
models of CSP (Roscoe, *The Theory and Practice of Concurrency*, §8.3–8.4,
the model `FDI`), specialised to sequential games.

A divergence-observing strategy `δ : DStrategy E F` has three components:

* `δ.toStrategy`: its finite plays, an ordinary strategy;
* `δ.div`: the plays after which `δ` *may diverge*, i.e. compute forever
  without another visible move. Only the component that has control can
  diverge, so every divergent play ends in a running position
  (`Pos.run q`, `div_run`). Divergence is a *terminal observation*: nothing
  is assumed about what follows a divergent play (no "divergence is chaos"
  closure). This matches Wasm, where `Behaviour.diverges` is one outcome
  among others;
* `δ.inf`: its *infinite* plays. An infinite play is presented by the set of
  its finite prefixes, a prefix-closed, totally ordered, unbounded set of
  lists (`IsInfPlay`). This keeps infinite plays canonical (two chains
  presenting the same infinite play give the same set) and makes all limits
  set-theoretic.

**Why infinite plays are needed.** Composition must create divergence from
infinite hidden interaction: a server that answers every call at once and a
client that calls it forever are both divergence-free, yet their composite
diverges. Seeing this needs the infinite plays of both components; the
finite plays alone are not enough, because a component may have arbitrarily
long finite plays without having the infinite one (unbounded
nondeterminism, e.g. "pick `n`, then call `n` times"). Hence `inf` is part of
the data and not computed from `toStrategy`. See `Silmaril.Games.DivComp`.

**Refinement** is componentwise inclusion (`δ ≤ δ'`): every finite play,
every divergence and every infinite play of `δ` is allowed by `δ'`. This is
the "may" order of `Silmaril.Games.Strategy` extended to the new observations;
divergence is an observation like any other, not the top element. It is the
order of Wasm's `Behaviours.Refines Eq` lifted to plays.

**Embeddings.** `forget δ = δ.toStrategy` forgets the new observations.
Ordinary strategies embed in two extreme ways, giving Galois connections
`ofStrategy ⊣ forget ⊣ chaos`:

* `ofStrategy σ`: no divergence, no infinite play (the least reading);
* `chaos σ`: diverges after every running play, and has every infinite play
  whose prefixes are plays (the greatest reading).

Between them, `limits σ` (no divergence, every limit of plays is an infinite
play) is the divergence-free reading used for copycat. The finite-play part
is unchanged by all three (`forget_ofStrategy`, …).
-/

@[expose] public section

namespace Silmaril.Games

universe u v

/-! ## Chains and infinite plays -/

/-- A sequence of finite traces, used to present infinite behaviour. -/
abbrev Chain (α : Type v) : Type v := ℕ → List α

namespace Chain

variable {α : Type v}

/-- Each trace extends the previous one. -/
def Mono (c : Chain α) : Prop := ∀ n, c n <+: c (n + 1)

/-- The traces get arbitrarily long. -/
def Unbounded (c : Chain α) : Prop := ∀ k, ∃ n, k ≤ (c n).length

/-- The limit of a chain: the prefixes of its members. -/
def lim (c : Chain α) : Set (List α) := {q | ∃ n, q <+: c n}

end Chain

/-- `I` presents an infinite trace: the set of its finite prefixes. -/
structure IsInfPlay {α : Type v} (I : Set (List α)) : Prop where
  /-- Prefix closed. -/
  of_prefix : ∀ {s t}, t ∈ I → s <+: t → s ∈ I
  /-- Totally ordered by the prefix order. -/
  total : ∀ {s t}, s ∈ I → t ∈ I → s <+: t ∨ t <+: s
  /-- Arbitrarily long. -/
  unbounded : ∀ k, ∃ s ∈ I, k ≤ s.length

/-! ## Divergence-observing strategies -/

/-- A divergence-observing strategy for `E ↠ F`: finite plays, divergent plays
and infinite plays. See the module documentation. -/
structure DStrategy (E F : Sig.{u}) : Type u where
  /-- The finite plays. -/
  toStrategy : Strategy E F
  /-- The plays after which the strategy may diverge. -/
  div : Set (List (Move E F))
  /-- The infinite plays, each given by its set of finite prefixes. -/
  inf : Set (Set (List (Move E F)))
  /-- A divergent play is a play. -/
  div_mem : ∀ {s}, s ∈ div → s ∈ toStrategy
  /-- Only a running component diverges. -/
  div_run : ∀ {s}, s ∈ div → ∃ q, Path .idle s (.run q)
  /-- Infinite plays are infinite traces. -/
  inf_isInf : ∀ {I}, I ∈ inf → IsInfPlay I
  /-- The prefixes of an infinite play are plays. -/
  inf_sub : ∀ {I}, I ∈ inf → I ⊆ toStrategy.plays

namespace DStrategy

variable {E F : Sig.{u}}

/-- Two divergence-observing strategies with the same components are equal. -/
@[ext] theorem ext {δ δ' : DStrategy E F} (h₁ : δ.toStrategy = δ'.toStrategy)
    (h₂ : δ.div = δ'.div) (h₃ : δ.inf = δ'.inf) : δ = δ' := by
  cases δ; cases δ'; cases h₁; cases h₂; cases h₃; rfl

/-- Refinement: componentwise inclusion. -/
instance : PartialOrder (DStrategy E F) where
  le δ δ' := δ.toStrategy ≤ δ'.toStrategy ∧ δ.div ⊆ δ'.div ∧ δ.inf ⊆ δ'.inf
  le_refl _ := ⟨le_rfl, subset_rfl, subset_rfl⟩
  le_trans _ _ _ h h' := ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.trans h'.2.2⟩
  le_antisymm _ _ h h' :=
    ext (le_antisymm h.1 h'.1) (h.2.1.antisymm h'.2.1) (h.2.2.antisymm h'.2.2)

/-- Unfolding refinement. -/
theorem le_def {δ δ' : DStrategy E F} :
    δ ≤ δ' ↔ δ.toStrategy ≤ δ'.toStrategy ∧ δ.div ⊆ δ'.div ∧ δ.inf ⊆ δ'.inf := Iff.rfl

/-! ## Embeddings of ordinary strategies -/

/-- Forget divergence and infinite plays. -/
def forget (δ : DStrategy E F) : Strategy E F := δ.toStrategy

/-- The least reading of an ordinary strategy: no divergence, no infinite play. -/
def ofStrategy (σ : Strategy E F) : DStrategy E F where
  toStrategy := σ
  div := ∅
  inf := ∅
  div_mem h := h.elim
  div_run h := h.elim
  inf_isInf h := h.elim
  inf_sub h := h.elim

/-- The divergence-free reading in which every limit of plays is an infinite
play. -/
def limits (σ : Strategy E F) : DStrategy E F where
  toStrategy := σ
  div := ∅
  inf := {I | IsInfPlay I ∧ I ⊆ σ.plays}
  div_mem h := h.elim
  div_run h := h.elim
  inf_isInf h := h.1
  inf_sub h := h.2

/-- The greatest reading of an ordinary strategy: it may diverge after every
running play and has every infinite play whose prefixes are plays. -/
def chaos (σ : Strategy E F) : DStrategy E F where
  toStrategy := σ
  div := {s | s ∈ σ ∧ ∃ q, Path .idle s (.run q)}
  inf := {I | IsInfPlay I ∧ I ⊆ σ.plays}
  div_mem h := h.1
  div_run h := h.2
  inf_isInf h := h.1
  inf_sub h := h.2

@[simp] theorem forget_ofStrategy (σ : Strategy E F) : (ofStrategy σ).forget = σ := rfl
@[simp] theorem forget_limits (σ : Strategy E F) : (limits σ).forget = σ := rfl
@[simp] theorem forget_chaos (σ : Strategy E F) : (chaos σ).forget = σ := rfl

/-- `forget` is monotone. -/
theorem forget_mono {δ δ' : DStrategy E F} (h : δ ≤ δ') : δ.forget ≤ δ'.forget := h.1

/-- `ofStrategy ⊣ forget`. -/
theorem gc_ofStrategy_forget : GaloisConnection (ofStrategy (E := E) (F := F)) forget :=
  fun _ _ => ⟨fun h => h.1, fun h => ⟨h, fun _ h => h.elim, fun _ h => h.elim⟩⟩

/-- `forget ⊣ chaos`. -/
theorem gc_forget_chaos : GaloisConnection (forget (E := E) (F := F)) chaos :=
  fun δ _ => ⟨fun h => ⟨h, fun _ hs => ⟨h (δ.div_mem hs), δ.div_run hs⟩,
      fun _ hI => ⟨δ.inf_isInf hI, fun _ hs => h (δ.inf_sub hI hs)⟩⟩, fun h => h.1⟩

/-- The three readings are ordered. -/
theorem ofStrategy_le_limits (σ : Strategy E F) : ofStrategy σ ≤ limits σ :=
  ⟨le_rfl, fun _ h => h.elim, fun _ h => h.elim⟩

/-- The three readings are ordered. -/
theorem limits_le_chaos (σ : Strategy E F) : limits σ ≤ chaos σ :=
  ⟨le_rfl, fun _ h => h.elim, fun _ h => h⟩

/-- Every divergence-observing strategy lies between the least and the
greatest reading of its finite plays. -/
theorem ofStrategy_forget_le (δ : DStrategy E F) : ofStrategy δ.forget ≤ δ :=
  (gc_ofStrategy_forget _ _).2 le_rfl

/-- Every divergence-observing strategy lies between the least and the
greatest reading of its finite plays. -/
theorem le_chaos_forget (δ : DStrategy E F) : δ ≤ chaos δ.forget :=
  (gc_forget_chaos _ _).1 le_rfl

/-- A strategy without infinite plays or divergence is the least reading of
its finite plays. -/
theorem eq_ofStrategy_iff {δ : DStrategy E F} : δ = ofStrategy δ.forget ↔ δ.div = ∅ ∧ δ.inf = ∅ :=
  ⟨fun h => by rw [h]; exact ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ => ext rfl h₁ h₂⟩

end DStrategy

end Silmaril.Games
