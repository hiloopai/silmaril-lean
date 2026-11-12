module

public import Silmaril.Games.LTS.Defs
public import Silmaril.Games.Composition.Defs
import Silmaril.Proofs.Games.LTS.Basic
import Silmaril.Proofs.Games.LTS.Comp

/-!
# Transition systems: theorems

* Runs compose and split (`LTS.Run.append`, `LTS.Run.of_append`).
* `Strategy.ofLTS L` is the least strategy containing the legal traces of `L`
  (`Strategy.ofLTS_le_iff`); it is monotone in the traces.
* Simulation implies refinement: `LTS.Simulation.ofLTS_le` and, for reduction
  semantics, `Reduction.Simulation.ofReduction_le`.

* `LTS.Denotes L σ` (the traces of `L` are the plays of `σ`): a strategy is
  denoted by its own transition system (`Strategy.denotes_toLTS`), parallel
  composition denotes composition (`LTS.Denotes.comp`), and mutual simulation
  between denoting systems proves equality of strategies
  (`LTS.Denotes.eq_of_simulation`).

Proofs are in `Silmaril.Proofs.Games.LTS.Basic` and `Silmaril.Proofs.Games.LTS.Comp`.
-/

public section

namespace Silmaril.Games

universe u

variable {E F : Sig.{u}}

namespace LTS

/-- Runs compose. -/
theorem Run.append {L : LTS E F} {x y z : L.State} {s t : List (Move E F)}
    (h₁ : L.Run x s y) (h₂ : L.Run y t z) : L.Run x (s ++ t) z :=
  Silmaril.Proofs.Games.LTS.run_append h₁ h₂

/-- Runs split along concatenation. -/
theorem Run.of_append {L : LTS E F} {x z : L.State} {s t : List (Move E F)}
    (h : L.Run x (s ++ t) z) : ∃ y, L.Run x s y ∧ L.Run y t z :=
  Silmaril.Proofs.Games.LTS.run_of_append h

/-- A single step is a run. -/
theorem Run.of_step {L : LTS E F} {x y : L.State} {l : Option (Move E F)}
    (h : L.step x l y) : L.Run x l.toList y :=
  Silmaril.Proofs.Games.LTS.run_of_step h

/-- The first visible move of a run, after silent steps. -/
theorem Run.cons_inv {L : LTS E F} {x z : L.State} {o : Move E F} {s : List (Move E F)}
    (h : L.Run x (o :: s) z) : ∃ x₁ x₂, L.Run x [] x₁ ∧ L.step x₁ (some o) x₂ ∧ L.Run x₂ s z :=
  Silmaril.Proofs.Games.LTS.run_cons_inv h

/-- Traces are closed under prefixes. -/
theorem traces_of_prefix {L : LTS E F} {s t : List (Move E F)} (ht : t ∈ L.Traces)
    (h : s <+: t) : s ∈ L.Traces := by
  obtain ⟨u, rfl⟩ := h
  obtain ⟨z, hz⟩ := ht
  obtain ⟨y, hy, -⟩ := Run.of_append hz
  exact ⟨y, hy⟩

/-- A simulation includes traces. -/
theorem Simulation.traces_subset {L₁ L₂ : LTS E F} (S : L₁.Simulation L₂) :
    L₁.Traces ⊆ L₂.Traces :=
  Silmaril.Proofs.Games.LTS.simulation_traces S

end LTS

namespace Strategy

/-- Legal traces are plays of the strategy of a transition system. -/
theorem mem_ofLTS_of_mem_traces {L : LTS E F} {s : List (Move E F)} (hs : s ∈ L.Traces)
    (hl : Legal s) : s ∈ ofLTS L :=
  subset_generate hs hl

/-- `ofLTS L` is the least strategy containing the legal traces of `L`. -/
theorem ofLTS_le_iff {L : LTS E F} {σ : Strategy E F} :
    ofLTS L ≤ σ ↔ ∀ s ∈ L.Traces, Legal s → s ∈ σ :=
  ⟨fun h _ hs hl => h (mem_ofLTS_of_mem_traces hs hl), generate_le⟩

/-- Trace inclusion implies refinement. -/
theorem ofLTS_mono {L₁ L₂ : LTS E F} (h : L₁.Traces ⊆ L₂.Traces) : ofLTS L₁ ≤ ofLTS L₂ :=
  generate_mono h

end Strategy

/-- Simulation implies refinement. -/
theorem LTS.Simulation.ofLTS_le {L₁ L₂ : LTS E F} (S : L₁.Simulation L₂) :
    Strategy.ofLTS L₁ ≤ Strategy.ofLTS L₂ :=
  Strategy.ofLTS_mono S.traces_subset

/-- A simulation of reduction semantics is a simulation of their transition
systems. -/
theorem Reduction.Simulation.nonempty_toLTS {R₁ R₂ : Reduction E F} (S : R₁.Simulation R₂) :
    Nonempty (LTS.Simulation R₁.toLTS R₂.toLTS) :=
  ⟨Silmaril.Proofs.Games.LTS.toLTSSimulation S⟩

/-- Simulation of reduction semantics implies refinement of their strategies. -/
theorem Reduction.Simulation.ofReduction_le {R₁ R₂ : Reduction E F} (S : R₁.Simulation R₂) :
    Strategy.ofReduction R₁ ≤ Strategy.ofReduction R₂ :=
  (Silmaril.Proofs.Games.LTS.toLTSSimulation S).ofLTS_le

namespace LTS

variable {G : Sig.{u}}

/-- A strategy is denoted by its own transition system. -/
theorem _root_.Silmaril.Games.Strategy.denotes_toLTS (σ : Strategy E F) : σ.toLTS.Denotes σ :=
  Silmaril.Proofs.Games.LTS.denotes_toLTS σ

/-- Parallel composition denotes composition. -/
theorem Denotes.comp {L₁ : LTS E F} {L₂ : LTS F G} {σ : Strategy E F} {τ : Strategy F G}
    (h₁ : L₁.Denotes σ) (h₂ : L₂.Denotes τ) : (L₁.comp L₂).Denotes (σ.comp τ) :=
  Silmaril.Proofs.Games.LTS.denotes_comp h₁ h₂

/-- Silent steps of the lower system lift to the composition. -/
theorem comp_taus₁ {L₁ : LTS E F} {L₂ : LTS F G} {x x' : L₁.State} (y : L₂.State)
    (h : L₁.Run x [] x') : (L₁.comp L₂).Run (x, y) [] (x', y) :=
  Silmaril.Proofs.Games.LTS.comp_taus₁ y h

/-- Silent steps of the upper system lift to the composition. -/
theorem comp_taus₂ {L₁ : LTS E F} {L₂ : LTS F G} (x : L₁.State) {y y' : L₂.State}
    (h : L₂.Run y [] y') : (L₁.comp L₂).Run (x, y) [] (x, y') :=
  Silmaril.Proofs.Games.LTS.comp_taus₂ x h

/-- Two systems denoting strategies that simulate each other denote the same
strategy. -/
theorem Denotes.eq_of_simulation {L₁ L₂ : LTS E F} {σ τ : Strategy E F} (h₁ : L₁.Denotes σ)
    (h₂ : L₂.Denotes τ) (S : L₁.Simulation L₂) (S' : L₂.Simulation L₁) : σ = τ := by
  ext p
  rw [← h₁ p, ← h₂ p]
  exact ⟨fun h => S.traces_subset h, fun h => S'.traces_subset h⟩

/-- A system denoting a strategy generates it. -/
theorem Denotes.ofLTS_eq {L : LTS E F} {σ : Strategy E F} (h : L.Denotes σ) :
    Strategy.ofLTS L = σ := by
  apply le_antisymm
  · exact Strategy.ofLTS_le_iff.2 fun s hs _ => (h s).1 hs
  · intro p hp
    exact Strategy.mem_ofLTS_of_mem_traces ((h p).2 hp) (σ.legal hp)

end LTS

end Silmaril.Games
