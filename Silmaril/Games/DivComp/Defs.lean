module

public import Silmaril.Games.Div.Thms
public import Silmaril.Games.Composition.Defs
import Silmaril.Proofs.Games.DivComp.Pos

/-!
# Composition of divergence-observing strategies

`σ.comp τ : DStrategy E G` for `σ : DStrategy E F` and `τ : DStrategy F G`
(diagrammatic order, as `Strategy.comp`).

* **Finite plays** are those of `Strategy.comp` (`forget_comp` is `rfl`).
* **Infinite interactions** (`InfInteraction σ τ`) are increasing sequences of
  finite interactions `Zip (s n) (t n) (p n)` whose total length grows
  without bound, such that each side that grows without bound converges to
  one of that side's infinite plays (`lim_s`, `lim_t`), and each side that
  stops growing ends in one of its finite plays (`mem_s`, `mem_t`).
* **Divergence** of the composite after `p` arises in two ways:
  - *local divergence*: `p` is the visible part of a finite interaction in
    which one component reaches a divergent play;
  - *infinite hidden chatter*: an infinite interaction whose visible part
    stays `p` forever. Then both components make infinitely many moves at the
    shared interface (`InfInteraction.chatter_inf` in `Thms`), and hiding
    them yields divergence. This is the clause that ordinary composition
    lacks.
* **Infinite plays** of the composite are the visible limits of infinite
  interactions whose visible part grows without bound.

Every divergent play of the composite ends in a running position:
`Silmaril.Proofs.Games.DivComp.run_of_div_left`/`run_of_div_right` for local
divergence, and `run_of_chatter` for hidden chatter (a composite that is idle
or waiting for its environment cannot be chattering internally).

`DStrategy.id E` is copycat with all its infinite plays and no divergence
(`limits (Strategy.id E)`).
-/

@[expose] public section

namespace Silmaril.Games

universe u

namespace DStrategy

variable {E F G : Sig.{u}}

/-- An infinite interaction of `σ` and `τ`; see the module documentation. -/
structure InfInteraction (σ : DStrategy E F) (τ : DStrategy F G) : Type u where
  /-- The lower component's plays. -/
  s : Chain (Move E F)
  /-- The upper component's plays. -/
  t : Chain (Move F G)
  /-- The visible plays. -/
  p : Chain (Move E G)
  /-- Each stage is an interaction. -/
  zip : ∀ n, Zip (s n) (t n) (p n)
  /-- The lower stages are plays of `σ`. -/
  mem_s : ∀ n, s n ∈ σ.toStrategy
  /-- The upper stages are plays of `τ`. -/
  mem_t : ∀ n, t n ∈ τ.toStrategy
  mono_s : s.Mono
  mono_t : t.Mono
  mono_p : p.Mono
  /-- The interaction never stops. -/
  unbounded : ∀ k, ∃ n, k ≤ (s n).length + (t n).length
  /-- If `σ` moves forever, it plays one of its infinite plays. -/
  lim_s : s.Unbounded → s.lim ∈ σ.inf
  /-- If `τ` moves forever, it plays one of its infinite plays. -/
  lim_t : t.Unbounded → t.lim ∈ τ.inf

/-- The divergent plays of a composite. -/
def compDiv (σ : DStrategy E F) (τ : DStrategy F G) : Set (List (Move E G)) :=
  {p | (∃ s t, Zip s t p ∧ ((s ∈ σ.div ∧ t ∈ τ.toStrategy) ∨ (s ∈ σ.toStrategy ∧ t ∈ τ.div))) ∨
    ∃ i : InfInteraction σ τ, ∀ n, i.p n = p}

theorem compDiv_run {σ : DStrategy E F} {τ : DStrategy F G} {p : List (Move E G)}
    (h : p ∈ compDiv σ τ) : ∃ g, Path .idle p (.run g) := by
  rcases h with ⟨s, t, hz, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩ | ⟨i, hi⟩
  · obtain ⟨f, hf⟩ := σ.div_run hs
    exact Silmaril.Proofs.Games.DivComp.run_of_div_left hz hf (τ.toStrategy.legal ht)
  · obtain ⟨g, hg⟩ := τ.div_run ht
    exact Silmaril.Proofs.Games.DivComp.run_of_div_right hz (σ.toStrategy.legal hs) hg
  · exact Silmaril.Proofs.Games.DivComp.run_of_chatter (p := p) (fun n => hi n ▸ i.zip n)
      (fun n => σ.toStrategy.legal (i.mem_s n)) (fun n => τ.toStrategy.legal (i.mem_t n))
      i.mono_s i.mono_t i.unbounded

/-- Composition of divergence-observing strategies (first `σ`, then `τ`). -/
def comp (σ : DStrategy E F) (τ : DStrategy F G) : DStrategy E G where
  toStrategy := σ.toStrategy.comp τ.toStrategy
  div := compDiv σ τ
  inf := {I | ∃ i : InfInteraction σ τ, i.p.Unbounded ∧ I = i.p.lim}
  div_mem := by
    rintro p (⟨s, t, hz, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩ | ⟨i, hi⟩)
    · exact ⟨s, σ.div_mem hs, t, ht, hz⟩
    · exact ⟨s, hs, t, τ.div_mem ht, hz⟩
    · exact ⟨_, i.mem_s 0, _, i.mem_t 0, hi 0 ▸ i.zip 0⟩
  div_run := compDiv_run
  inf_isInf := by
    rintro _ ⟨i, hu, rfl⟩
    exact Chain.isInfPlay_lim i.mono_p hu
  inf_sub := by
    rintro _ ⟨i, -, rfl⟩ q ⟨n, hq⟩
    exact (σ.toStrategy.comp τ.toStrategy).of_prefix ⟨_, i.mem_s n, _, i.mem_t n, i.zip n⟩ hq

/-- Copycat: no divergence, and every limit of copycat plays is an infinite
play. -/
protected def id (E : Sig.{u}) : DStrategy E E := limits (Strategy.id E)

/-- Finite plays of a composite are those of the composite of finite plays. -/
@[simp] theorem forget_comp (σ : DStrategy E F) (τ : DStrategy F G) :
    (σ.comp τ).forget = σ.forget.comp τ.forget := rfl

/-- The finite plays of copycat. -/
@[simp] theorem forget_id (E : Sig.{u}) : (DStrategy.id E).forget = Strategy.id E := rfl

end DStrategy

end Silmaril.Games
