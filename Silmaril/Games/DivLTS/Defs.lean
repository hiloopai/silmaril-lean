module

public import Silmaril.Games.Div.Thms
public import Silmaril.Games.LTS.Thms
public import Silmaril.Games.Handler.Defs
public import Silmaril.Foundations.InfiniteTrace

/-!
# Divergence-observing strategies of transition systems

* `LTS.Diverges L x`: `L` has an infinite run of silent steps from `x`
  (`Silmaril.InfiniteTrace`, the notion silmaril uses for Wasm's
  `Execution.Core.Diverges`).
* `LTS.InfRun L`: an infinite run from the initial state, presented by states
  `st n` and increasing traces `tr n` with `L.Run (st n) w (st (n+1))` for
  `tr (n+1) = tr n ++ w`. Its visible behaviour is infinite when `tr` grows
  without bound; otherwise the run is eventually silent.
* `DStrategy.ofLTS L`: finite plays are `Strategy.ofLTS L` (so the finite part
  is the old semantics *by definition*, `forget_ofLTS`); a legal trace `s`
  ending in a running position is divergent when some run reading `s` reaches
  a diverging state; the infinite plays are the limits of infinite runs with
  unbounded legal traces.
* `DStrategy.ofReduction R = ofLTS R.toLTS` and
  `DStrategy.ofHandler h = ofReduction h.toReduction` (handlers never diverge,
  `ofHandler_div` in `Thms`).
* **Divergence-sensitive simulations.** A weak simulation may match a silent
  step by no step at all, so it does not preserve divergence. An
  `LTS.DivSimulation` additionally requires that each silent step is matched
  either by at least one silent step, or by none while a well-founded measure
  on source states decreases (the "stuttering with measure" condition of
  CompCert's forward simulations). `Reduction.DivSimulation` is the same
  condition for reduction semantics, question by question. Both imply
  refinement of the divergence-observing strategies (`Thms`).

As in `Silmaril.Games.LTS`, Opponent moves are inputs: an LTS refusing one is
completed by receptiveness in the finite plays. Divergence and infinite plays
are taken from the LTS as is.
-/

@[expose] public section

namespace Silmaril.Games

universe u

namespace LTS

variable {E F : Sig.{u}}

/-- Silent steps. -/
def Silent (L : LTS E F) (x y : L.State) : Prop := L.step x none y

/-- `L` may compute forever silently from `x`. -/
def Diverges (L : LTS E F) (x : L.State) : Prop := Silmaril.InfiniteTrace L.Silent x

/-- An infinite run from the initial state; see the module documentation. -/
structure InfRun (L : LTS E F) : Type u where
  /-- The states reached. -/
  st : ℕ → L.State
  /-- The visible traces read so far. -/
  tr : Chain (Move E F)
  st_zero : st 0 = L.init
  tr_zero : tr 0 = []
  /-- Each stage extends the previous one by a run. -/
  step : ∀ n, ∃ w, tr (n + 1) = tr n ++ w ∧ L.Run (st n) w (st (n + 1))

/-- The traces of an infinite run increase. -/
theorem InfRun.mono {L : LTS E F} (r : L.InfRun) : r.tr.Mono := fun n => by
  obtain ⟨w, h, -⟩ := r.step n
  exact ⟨w, h.symm⟩

/-- Each stage of an infinite run is a run from the initial state. -/
theorem InfRun.run {L : LTS E F} (r : L.InfRun) (n : ℕ) : L.Run L.init (r.tr n) (r.st n) := by
  induction n with
  | zero => rw [r.st_zero, r.tr_zero]; exact .nil _
  | succ n ih =>
    obtain ⟨w, h, hr⟩ := r.step n
    rw [h]
    exact ih.append hr

/-- Traces after which `L` may diverge. -/
def DivTraces (L : LTS E F) : Set (List (Move E F)) :=
  {s | ∃ y, L.Run L.init s y ∧ L.Diverges y}

/-- Infinite traces of `L`: limits of infinite runs with unbounded traces. -/
def InfTraces (L : LTS E F) : Set (Set (List (Move E F))) :=
  {I | ∃ r : L.InfRun, r.tr.Unbounded ∧ I = r.tr.lim}

/-- A divergence-sensitive weak forward simulation; see the module
documentation. -/
structure DivSimulation (L₁ L₂ : LTS E F) extends L₁.Simulation L₂ where
  /-- The measure on source states. -/
  lt : L₁.State → L₁.State → Prop
  wf : WellFounded lt
  /-- Silent steps make progress on the target, or stutter while the measure
  decreases. -/
  tau : ∀ {x x' : L₁.State} {y : L₂.State}, R x y → L₁.step x none x' →
    (∃ y', Relation.TransGen L₂.Silent y y' ∧ R x' y') ∨ (R x' y ∧ lt x' x)

end LTS

namespace DStrategy

variable {E F : Sig.{u}}

/-- The divergence-observing strategy of a transition system. -/
def ofLTS (L : LTS E F) : DStrategy E F where
  toStrategy := Strategy.ofLTS L
  div := {s | s ∈ L.DivTraces ∧ ∃ q, Path .idle s (.run q)}
  inf := {I | I ∈ L.InfTraces ∧ ∀ s ∈ I, Legal s}
  div_mem := fun ⟨⟨y, hr, _⟩, _, hp⟩ => Strategy.mem_ofLTS_of_mem_traces ⟨y, hr⟩ ⟨_, hp⟩
  div_run h := h.2
  inf_isInf := by
    rintro _ ⟨⟨r, hu, rfl⟩, -⟩
    exact Chain.isInfPlay_lim r.mono hu
  inf_sub := by
    rintro _ ⟨⟨r, -, rfl⟩, hl⟩ q hq
    obtain ⟨n, hn⟩ := hq
    exact Strategy.mem_ofLTS_of_mem_traces
      (LTS.traces_of_prefix ⟨_, r.run n⟩ hn) (hl q ⟨n, hn⟩)

/-- The divergence-observing strategy of a reduction semantics. -/
def ofReduction (R : Reduction E F) : DStrategy E F := ofLTS R.toLTS

/-- The divergence-observing strategy of a handler. -/
def ofHandler (h : Handler E F) : DStrategy E F := ofReduction h.toReduction

end DStrategy

/-- A divergence-sensitive simulation of reduction semantics: a
`Reduction.Simulation` whose internal steps are matched by at least one
internal step, or by none while a well-founded measure decreases. -/
structure Reduction.DivSimulation {E F : Sig.{u}} (R₁ R₂ : Reduction E F)
    extends R₁.Simulation R₂ where
  /-- The measure on source configurations, per question. -/
  lt : ∀ {q : F.Op}, R₁.Conf q → R₁.Conf q → Prop
  wf : ∀ q, WellFounded (@lt q)
  /-- Internal steps make progress on the target, or stutter while the
  measure decreases. -/
  tau : ∀ {q} {c c' : R₁.Conf q} {d : R₂.Conf q}, rel c d → R₁.step c c' →
    (∃ d', Relation.TransGen R₂.step d d' ∧ rel c' d') ∨ (rel c' d ∧ lt c' c)

end Silmaril.Games
