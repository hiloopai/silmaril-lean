module

public import Silmaril.Games.Abstract.Machine.Defs
public import Silmaril.Games.Abstract.Game.Thms
import Silmaril.Proofs.Games.Abstract.Machine.Basic
import Silmaril.Proofs.Games.Abstract.Machine.Counterexample

/-!
# Abstract state machines: erasure, determinism, bisimulation

* Traces are prefix-closed (`tracesFrom_of_prefix`); a machine whose traces are
  already closed denotes exactly its traces (`coe_denote`).
* Strategy-deterministic machines denote deterministic trace models
  (`SDet.denote_det`). Strategy determinism is relative to the history, inputs
  included; see `Silmaril.Games.Abstract.Machine.Defs`.
* State erasure respects bisimulation (`traces_eq_of_bisim`), and for
  deterministic labelled transition systems it reflects it
  (`lDet_bisim_iff_traces`): on the bisimulation quotient of deterministic
  machines, `traces` is injective. A strategy-deterministic machine without
  silent steps is one (`SDet.lDet`).
* Nondeterministic machines with equal traces need not be bisimilar
  (`exists_traces_eq_not_bisim`): `a.b + a.c` against `a.(b + c)`. The trace
  set is then a quotient that forgets branching, which is the intended reading
  for may-testing contexts, not an injection of machines.
-/

public section

namespace Silmaril.Games.Abstract.Machine

universe u

variable {G : Game.{u}} {M N : Machine G}

/-- Runs compose. -/
theorem Run.append {x y z : M.State} {s t : List G.Move} (h₁ : M.Run x s y) (h₂ : M.Run y t z) :
    M.Run x (s ++ t) z :=
  Silmaril.Proofs.Games.Abstract.Machine.Run.append h₁ h₂

/-- Runs split along concatenation. -/
theorem Run.of_append {x z : M.State} {s t : List G.Move} (h : M.Run x (s ++ t) z) :
    ∃ y, M.Run x s y ∧ M.Run y t z :=
  Silmaril.Proofs.Games.Abstract.Machine.Run.of_append h

/-- A run through a nonempty list: silent steps, the first move, the rest. -/
theorem Run.cons_inv {x z : M.State} {o : G.Move} {s : List G.Move} (h : M.Run x (o :: s) z) :
    ∃ x₁ y₁, M.Run x [] x₁ ∧ M.step x₁ (some o) y₁ ∧ M.Run y₁ s z :=
  Silmaril.Proofs.Games.Abstract.Machine.Run.cons_inv h

/-- A step with an optional label, then a run. -/
theorem Run.step_opt {x y z : M.State} {o : Option G.Move} {s : List G.Move}
    (h : M.step x o y) (r : M.Run y s z) : M.Run x (o.toList ++ s) z := by
  cases o with
  | none => exact .tau h r
  | some m => exact .vis h r

/-- The empty play is a trace. -/
theorem nil_mem_tracesFrom (x : M.State) : [] ∈ M.tracesFrom x := ⟨x, .nil x⟩

/-- Traces are closed under prefixes. -/
theorem tracesFrom_of_prefix {x : M.State} {s t : List G.Move} (ht : t ∈ M.tracesFrom x)
    (h : s <+: t) : s ∈ M.tracesFrom x :=
  Silmaril.Proofs.Games.Abstract.Machine.tracesFrom_of_prefix ht h

/-- Every legal trace is a play of the denotation. -/
theorem mem_denote_of_mem_traces {s : List G.Move} (hs : s ∈ M.traces) (hl : s ∈ G.Legal) :
    s ∈ M.denote :=
  TraceModel.subset_generate hs hl

/-- A machine whose traces satisfy the closure conditions denotes exactly its
traces. -/
theorem coe_denote (h : G.Closed M.traces) : (M.denote : Set (List G.Move)) = M.traces :=
  congrArg (fun T : TraceModel G => (T : Set (List G.Move))) (TraceModel.generate_coe ⟨_, h⟩)

/-- Strategy-deterministic machines denote deterministic models. -/
theorem SDet.denote_det (hM : M.SDet) : M.denote.Det :=
  Silmaril.Proofs.Games.Abstract.Machine.SDet.denote_det hM

/-- A strategy-deterministic machine without silent steps is a deterministic
labelled transition system. -/
theorem SDet.lDet (hM : M.SDet) (htau : ∀ {x y : M.State}, ¬ M.step x none y) : M.LDet :=
  Silmaril.Proofs.Games.Abstract.Machine.SDet.lDet hM htau

/-- Bisimilar machines have the same traces. -/
theorem traces_eq_of_bisim (h : M.Bisim N) : M.traces = N.traces :=
  Silmaril.Proofs.Games.Abstract.Machine.traces_eq_of_bisim h

/-- Bisimilar machines have the same denotation. -/
theorem denote_eq_of_bisim (h : M.Bisim N) : M.denote = N.denote := by
  rw [denote, denote, traces_eq_of_bisim h]

/-- For deterministic labelled transition systems, bisimilarity is trace
equality: state erasure is injective on their bisimulation quotient. -/
theorem lDet_bisim_iff_traces (hM : M.LDet) (hN : N.LDet) : M.Bisim N ↔ M.traces = N.traces :=
  ⟨traces_eq_of_bisim, Silmaril.Proofs.Games.Abstract.Machine.LDet.bisim_of_traces hM hN⟩

/-- For deterministic labelled transition systems with closed traces,
bisimilarity is equality of denotations. -/
theorem lDet_bisim_iff_denote (hM : M.LDet) (hN : N.LDet) (hMc : G.Closed M.traces)
    (hNc : G.Closed N.traces) : M.Bisim N ↔ M.denote = N.denote := by
  rw [lDet_bisim_iff_traces hM hN, ← coe_denote hMc, ← coe_denote hNc]
  exact ⟨fun h => SetLike.coe_injective h, fun h => by rw [h]⟩

/-- Without determinism, equal traces do not give bisimilarity. -/
theorem exists_traces_eq_not_bisim :
    ∃ (G : Game.{0}) (M N : Machine G), M.traces = N.traces ∧ N.LDet ∧ ¬ M.Bisim N :=
  Silmaril.Proofs.Games.Abstract.Machine.Counterexample.exists_traces_eq_not_bisim

end Silmaril.Games.Abstract.Machine
