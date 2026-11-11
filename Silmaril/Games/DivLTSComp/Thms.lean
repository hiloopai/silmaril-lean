module

public import Silmaril.Games.DivLTSComp.Defs
public import Silmaril.Games.DivComp.Thms
public import Silmaril.Games.DivLTS.Thms
import Silmaril.Proofs.Games.DivLTSComp.Laws

/-!
# The divergence-observing strategy of a composite system

**`DStrategy.ofLTS_comp`**: for transition systems `L₁ : LTS E F` and
`L₂ : LTS F G` that denote their strategies (`LTS.Denotes`: their traces are
exactly the plays) and diverge only in running positions (`LTS.DivRunning`),

  `DStrategy.ofLTS (L₁.comp L₂) = (DStrategy.ofLTS L₁).comp (DStrategy.ofLTS L₂)`.

This generalises `LTS.Denotes.comp` (finite plays) to divergence and infinite
plays: the divergences of the composite system, including those created by
infinitely many hidden synchronisations, are exactly the divergences of
`DStrategy.comp` (local divergence of a side, or an infinite interaction with
constant visible part), and its infinite runs are exactly the infinite
interactions with unbounded visible part. Components:

* `ofLTS_comp_div`, `ofLTS_comp_inf`: the two observations, separately.
* `LTS.silentRunning_of_pos`: `SilentRunning` (hence `DivRunning`) from a
  map of states to game positions.
* The `DivRunning` hypothesis is needed: a component diverging while idle or
  waiting has no divergent play in `DStrategy.ofLTS`, but makes the composite
  diverge while its partner runs. `LTS.SilentRunning` implies it.

Proofs: `Silmaril.Proofs.Games.DivLTSComp.{Basic,Follow,Proj,Main}` (new; the
restated `comp_run`/`run_comp` and `zip_drop` follow
`Silmaril.Proofs.Games.LTS.Comp` and `Silmaril.Proofs.Games.DivComp.ZipChain`).
-/

public section

namespace Silmaril.Games

universe u

namespace DStrategy

open Silmaril.Proofs.Games.DivLTSComp

variable {E F G : Sig.{u}} {L₁ : LTS E F} {L₂ : LTS F G} {σ : Strategy E F} {τ : Strategy F G}

/-- The divergent plays of a composite system are those of the composite strategy. -/
theorem ofLTS_comp_div (h₁ : L₁.Denotes σ) (h₂ : L₂.Denotes τ) (d₁ : L₁.DivRunning)
    (d₂ : L₂.DivRunning) :
    (ofLTS (L₁.comp L₂)).div = compDiv (ofLTS L₁) (ofLTS L₂) :=
  Laws.ofLTS_comp_div h₁ h₂ d₁ d₂

/-- The infinite plays of a composite system are those of the composite strategy. -/
theorem ofLTS_comp_inf (h₁ : L₁.Denotes σ) (h₂ : L₂.Denotes τ) :
    (ofLTS (L₁.comp L₂)).inf = ((ofLTS L₁).comp (ofLTS L₂)).inf :=
  Laws.ofLTS_comp_inf h₁ h₂

/-- **The divergence-observing strategy of a composite system is the composite of the
divergence-observing strategies.** -/
theorem ofLTS_comp (h₁ : L₁.Denotes σ) (h₂ : L₂.Denotes τ) (d₁ : L₁.DivRunning)
    (d₂ : L₂.DivRunning) :
    ofLTS (L₁.comp L₂) = (ofLTS L₁).comp (ofLTS L₂) := by
  have hfin : Strategy.ofLTS (L₁.comp L₂) = (Strategy.ofLTS L₁).comp (Strategy.ofLTS L₂) := by
    rw [h₁.ofLTS_eq, h₂.ofLTS_eq]
    exact (h₁.comp h₂).ofLTS_eq
  exact ext hfin (ofLTS_comp_div h₁ h₂ d₁ d₂) (ofLTS_comp_inf h₁ h₂)

end DStrategy

namespace LTS

variable {E F : Sig.{u}}

/-- Runs follow the legality automaton along a position map that moves by game steps on
visible steps and stays on silent steps. -/
theorem path_of_run_pos {L : LTS E F} (pos : L.State → Pos E F)
    (hvis : ∀ {x y o}, L.step x (some o) y → Step (pos x) o (pos y))
    (htau : ∀ {x y}, L.step x none y → pos y = pos x) {x y : L.State} {s : List (Move E F)}
    (h : L.Run x s y) : Path (pos x) s (pos y) := by
  induction h with
  | nil x => exact .nil _
  | tau hs _ ih => exact htau hs ▸ ih
  | vis hs _ ih => exact .cons (hvis hs) ih

/-- **Silent steps only in running positions**, from a position map: the initial state is
idle, visible steps are game steps, and silent steps happen only in running positions and keep
the position. -/
theorem silentRunning_of_pos {L : LTS E F} (pos : L.State → Pos E F) (hinit : pos L.init = .idle)
    (hvis : ∀ {x y o}, L.step x (some o) y → Step (pos x) o (pos y))
    (htau : ∀ {x y}, L.step x none y → pos y = pos x)
    (hrun : ∀ {x y}, L.step x none y → ∃ q, pos x = .run q) : L.SilentRunning := by
  intro s x y hr hs
  obtain ⟨q, hq⟩ := hrun hs
  have hp : Path (pos L.init) s (pos x) := path_of_run_pos pos hvis htau hr
  rw [hinit, hq] at hp
  exact ⟨q, hp⟩

end LTS

end Silmaril.Games
