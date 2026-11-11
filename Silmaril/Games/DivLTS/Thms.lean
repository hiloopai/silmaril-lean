module

public import Silmaril.Games.DivLTS.Defs
public import Silmaril.Games.Handler.Thms
import Silmaril.Proofs.Games.DivLTS.Sim

/-!
# Divergence-observing strategies of transition systems: theorems

* **Consistency with the old semantics**: the finite plays of
  `DStrategy.ofLTS L`, `ofReduction R` and `ofHandler h` are
  `Strategy.ofLTS L`, `Strategy.ofReduction R` and `Strategy.ofHandler h`
  (`forget_ofLTS`, `forget_ofReduction`, `forget_ofHandler`, all `rfl`).
* **Adequacy for divergence and infinite runs**: a silent infinite run after
  a legal trace ending in a running position yields a divergent play
  (`mem_div_ofLTS_of_run`), and an infinite run with unbounded legal traces
  yields an infinite play (`lim_mem_inf_ofLTS`); `mem_div_ofLTS`,
  `mem_inf_ofLTS` are the characterizations.
* For a reduction semantics, divergence right after a question `q` is
  divergence of `R.start q` (`div_ask_ofReduction_iff`).
* **Simulation implies refinement**: a weak simulation preserves finite and
  infinite plays (`LTS.Simulation.inf_subset`); a divergence-sensitive
  simulation also preserves divergence, hence refinement of the
  divergence-observing strategies (`LTS.DivSimulation.ofLTS_le`,
  `Reduction.DivSimulation.ofReduction_le`).
* **Handlers never diverge** (`ofHandler_div`).

Proofs are in `Silmaril.Proofs.Games.DivLTS.Sim`.
-/

public section

namespace Silmaril.Games

universe u

variable {E F : Sig.{u}}

namespace DStrategy

/-- **Consistency**: the finite plays of the divergence-observing semantics
of an LTS are its old semantics. -/
@[simp] theorem forget_ofLTS (L : LTS E F) : (ofLTS L).forget = Strategy.ofLTS L := rfl

/-- Consistency for reduction semantics. -/
@[simp] theorem forget_ofReduction (R : Reduction E F) :
    (ofReduction R).forget = Strategy.ofReduction R := rfl

/-- Consistency for handlers. -/
@[simp] theorem forget_ofHandler (h : Handler E F) : (ofHandler h).forget = Strategy.ofHandler h :=
  rfl

/-- Divergent plays of a transition system. -/
theorem mem_div_ofLTS {L : LTS E F} {s : List (Move E F)} :
    s ∈ (ofLTS L).div ↔ (∃ y, L.Run L.init s y ∧ L.Diverges y) ∧ ∃ q, Path .idle s (.run q) :=
  Iff.rfl

/-- **An infinite silent run yields divergence.** -/
theorem mem_div_ofLTS_of_run {L : LTS E F} {s : List (Move E F)} {y : L.State}
    (hr : L.Run L.init s y) (hd : L.Diverges y) {q : F.Op} (hq : Path .idle s (.run q)) :
    s ∈ (ofLTS L).div :=
  ⟨⟨y, hr, hd⟩, q, hq⟩

/-- Infinite plays of a transition system. -/
theorem mem_inf_ofLTS {L : LTS E F} {I : Set (List (Move E F))} :
    I ∈ (ofLTS L).inf ↔ (∃ r : L.InfRun, r.tr.Unbounded ∧ I = r.tr.lim) ∧ ∀ s ∈ I, Legal s :=
  Iff.rfl

/-- **An infinite visible run yields an infinite play.** -/
theorem lim_mem_inf_ofLTS {L : LTS E F} (r : L.InfRun) (hu : r.tr.Unbounded)
    (hl : ∀ n, Legal (r.tr n)) : r.tr.lim ∈ (ofLTS L).inf :=
  ⟨⟨r, hu, rfl⟩, fun _ ⟨n, hq⟩ => (hl n).of_prefix hq⟩

/-- Inclusion of traces, divergent traces and infinite traces implies
refinement. -/
theorem ofLTS_le_of {L₁ L₂ : LTS E F} (h₁ : L₁.Traces ⊆ L₂.Traces)
    (h₂ : L₁.DivTraces ⊆ L₂.DivTraces) (h₃ : L₁.InfTraces ⊆ L₂.InfTraces) :
    ofLTS L₁ ≤ ofLTS L₂ :=
  ⟨Strategy.ofLTS_mono h₁, fun _ ⟨hd, hq⟩ => ⟨h₂ hd, hq⟩, fun _ ⟨hI, hl⟩ => ⟨h₃ hI, hl⟩⟩

/-- Divergence right after a question of a reduction semantics is divergence
of the question's initial configuration. -/
theorem div_ask_ofReduction_iff {R : Reduction E F} {q : F.Op} :
    [.inr (.ask q)] ∈ (ofReduction R).div ↔ Silmaril.InfiniteTrace (R.step (q := q)) (R.start q) :=
  Silmaril.Proofs.Games.DivLTS.div_ask_iff

/-- **Handlers never diverge.** -/
theorem ofHandler_div (h : Handler E F) : (ofHandler h).div = ∅ := by
  ext s
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨y, -, hd⟩, -⟩
  obtain ⟨_, hst, -⟩ := hd.unfold
  cases hst with
  | tau hc => exact hc

end DStrategy

/-- A weak simulation preserves infinite traces. -/
theorem LTS.Simulation.infTraces_subset {L₁ L₂ : LTS E F} (S : L₁.Simulation L₂) :
    L₁.InfTraces ⊆ L₂.InfTraces := by
  rintro _ ⟨r, hu, rfl⟩
  obtain ⟨r', hr⟩ := Silmaril.Proofs.Games.DivLTS.infRun_of_simulation S r
  exact ⟨r', hr ▸ hu, by rw [hr]⟩

/-- A weak simulation preserves infinite plays. -/
theorem LTS.Simulation.inf_subset {L₁ L₂ : LTS E F} (S : L₁.Simulation L₂) :
    (DStrategy.ofLTS L₁).inf ⊆ (DStrategy.ofLTS L₂).inf :=
  fun _ ⟨hI, hl⟩ => ⟨S.infTraces_subset hI, hl⟩

/-- A divergence-sensitive simulation preserves divergent traces. -/
theorem LTS.DivSimulation.divTraces_subset {L₁ L₂ : LTS E F} (S : L₁.DivSimulation L₂) :
    L₁.DivTraces ⊆ L₂.DivTraces := by
  rintro s ⟨y, hr, hd⟩
  obtain ⟨y', hr', hR⟩ := Silmaril.Proofs.Games.DivLTS.simulation_run S.toSimulation hr S.init
  exact ⟨y', hr', Silmaril.Proofs.Games.DivLTS.diverges_of_divSimulation S hR hd⟩

/-- **Divergence-sensitive simulation implies refinement.** -/
theorem LTS.DivSimulation.ofLTS_le {L₁ L₂ : LTS E F} (S : L₁.DivSimulation L₂) :
    DStrategy.ofLTS L₁ ≤ DStrategy.ofLTS L₂ :=
  DStrategy.ofLTS_le_of S.toSimulation.traces_subset S.divTraces_subset
    S.toSimulation.infTraces_subset

/-- A divergence-sensitive simulation of reduction semantics is one of their
transition systems. -/
theorem Reduction.DivSimulation.nonempty_toLTS {R₁ R₂ : Reduction E F} (S : R₁.DivSimulation R₂) :
    Nonempty (LTS.DivSimulation R₁.toLTS R₂.toLTS) :=
  ⟨Silmaril.Proofs.Games.DivLTS.toLTSDivSimulation S⟩

/-- **Divergence-sensitive simulation of reduction semantics implies
refinement.** -/
theorem Reduction.DivSimulation.ofReduction_le {R₁ R₂ : Reduction E F} (S : R₁.DivSimulation R₂) :
    DStrategy.ofReduction R₁ ≤ DStrategy.ofReduction R₂ :=
  (Silmaril.Proofs.Games.DivLTS.toLTSDivSimulation S).ofLTS_le

end Silmaril.Games
