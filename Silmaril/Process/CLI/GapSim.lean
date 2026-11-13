module

public import Silmaril.Process.CLI.Spec

/-! # Filling the gaps of a model

A model point `N` that decodes more instructions than `M` is usually **not** above `M` in the
simulation order (`Model.Le`): where `M` stops with the `unmodeled` fault, `N` retires an
instruction, and `Isa.Sim` must match faults. But `unmodeled` is not behaviour, it is a gap,
and `Agrees` ignores it. `Isa.GapSim I J` is `Isa.Sim` except at the `unmodeled` steps of `I`,
which `J` may answer in any way (`Sim.toGapSim`: every simulation is one).

Along a gap simulation every finite run, every exit and every infinite run of `M` is one of `N`
(`Proc.runs_gapSim`, `Proc.exited_gapSim`, `Proc.diverges_gapSim`). So

* `Agrees`, `Halts` and `Bounded` move **down** from `N` to `M` (`Agrees.of_gapLe`,
  `Halts.of_gapLe`, `Bounded.of_gapLe`): a statement proved at the larger model holds at the
  smaller one;
* a run of `M` that exits is a run of `N` that exits, so nonvacuity witnesses move **up**
  (`Model.GapSim.exits`);
* `Covered` does not move either way: `M`'s `unmodeled` stops are the gaps `N` fills.
-/

@[expose] public section

namespace Silmaril.Process.CLI

open Silmaril.Process.Syscall Silmaril.Machine.Trace

namespace Isa

/-- `J` simulates `I` wherever `I` does not stop with the `unmodeled` fault. -/
structure GapSim (I J : Isa) where
  rel : I.Core → J.Core → Prop
  step : ∀ {c d m o}, rel c d → I.step c m o → o ≠ .fault .unmodeled →
    ∃ o', J.step d m o' ∧ StepRel rel o o'
  request : ∀ {c d}, rel c d → I.request c = J.request d
  resume : ∀ {c d r c'}, rel c d → I.resume c r c' → ∃ d', J.resume d r d' ∧ rel c' d'

/-- Every simulation is a gap simulation. -/
def Sim.toGapSim {I J : Isa} (sim : Sim I J) : GapSim I J where
  rel := sim.rel
  step h step _ := sim.step h step
  request := sim.request
  resume := sim.resume

end Isa

namespace Model

/-- A gap simulation of models: of their instruction sets, and a simulation of the rest. -/
structure GapSim (M N : Model) where
  isa : Isa.GapSim M.isa N.isa
  env : Env.Sim M.env N.env
  envInit : ∀ {input m s}, M.envInit input m s → ∃ t, N.envInit input m t ∧ env.rel s t
  load : ∀ {image input c m}, M.load image input c m → ∃ d, N.load image input d m ∧ isa.rel c d

/-- `N` fills the gaps of `M`. -/
def GapLe (M N : Model) : Prop := Nonempty (GapSim M N)

/-- Every simulation of models is a gap simulation. -/
def Sim.toGapSim {M N : Model} (sim : Sim M N) : GapSim M N where
  isa := sim.isa.toGapSim
  env := sim.env
  envInit := sim.envInit
  load := sim.load

theorem GapLe.of_le {M N : Model} (le : M.Le N) : M.GapLe N :=
  let ⟨sim⟩ := le
  ⟨sim.toGapSim⟩

end Model

/-- A retirement or a trap is not the `unmodeled` fault. -/
theorem retired_ne_unmodeled {C : Type} {c : C} {m : Memory} :
    (Step.retired c m : Step C) ≠ .fault .unmodeled := nofun

theorem syscall_ne_unmodeled {C : Type} {c : C} : (Step.syscall c : Step C) ≠ .fault .unmodeled :=
  nofun

namespace Proc

variable {I J : Isa} {E F : Env}

/-- Related process states. -/
def GapRelated (si : Isa.GapSim I J) (se : Env.Sim E F) (x : PState I E) (y : PState J F) :
    Prop :=
  si.rel x.core y.core ∧ se.rel x.env y.env

theorem step_gapSim (si : Isa.GapSim I J) (se : Env.Sim E F)
    {x x' : PState I E} {y : PState J F} {events : List Event}
    (related : GapRelated si se x y) (step : Step I E x events x') :
    ∃ y', Step J F y events y' ∧ GapRelated si se x' y' := by
  obtain ⟨rc, re⟩ := related
  cases step with
  | retire running step =>
    obtain ⟨o', step', rel⟩ := si.step rc ((se.memory re) ▸ step) retired_ne_unmodeled
    cases rel with
    | retired h =>
      exact ⟨_, .retire ((se.exited re) ▸ running) step', h, se.withMemory _ re⟩
  | call running step request effect resume =>
    obtain ⟨o', step', rel⟩ := si.step rc ((se.memory re) ▸ step) syscall_ne_unmodeled
    cases rel with
    | syscall h =>
      obtain ⟨t', effect', re'⟩ := se.step re effect
      obtain ⟨d', resume', rc'⟩ := si.resume h resume
      exact ⟨_, .call ((se.exited re) ▸ running) step' ((si.request h) ▸ request) effect' resume',
        rc', re'⟩
  | exit running step request effect =>
    obtain ⟨o', step', rel⟩ := si.step rc ((se.memory re) ▸ step) syscall_ne_unmodeled
    cases rel with
    | syscall h =>
      obtain ⟨t', effect', re'⟩ := se.step re effect
      exact ⟨_, .exit ((se.exited re) ▸ running) step' ((si.request h) ▸ request) effect', h, re'⟩

/-- A gap simulation is a (lockstep) trace refinement of processes. -/
theorem refines_gapSim (si : Isa.GapSim I J) (se : Env.Sim E F) :
    Machine.Trace.Refines (Step I E) (Step J F) (GapRelated si se) := by
  intro x y events x' related step
  obtain ⟨y', step', related'⟩ := step_gapSim si se related step
  exact ⟨y', .single step', related'⟩

theorem runs_gapSim (si : Isa.GapSim I J) (se : Env.Sim E F)
    {x x' : PState I E} {y : PState J F} {events : List Event}
    (run : Runs I E x events x') (related : GapRelated si se x y) :
    ∃ y', Runs J F y events y' ∧ GapRelated si se x' y' :=
  (refines_gapSim si se).runs run related

/-- An exit is an exit of every related state (a gap is never an exit). -/
theorem exited_gapSim (si : Isa.GapSim I J) (se : Env.Sim E F)
    {x : PState I E} {y : PState J F} {status : Nat} (related : GapRelated si se x y)
    (stop : Stop I E x (.exited status)) : Stop J F y (.exited status) :=
  .exited ((se.exited related.2) ▸ stop.exited_status)

theorem diverges_gapSim (si : Isa.GapSim I J) (se : Env.Sim E F)
    {x : PState I E} {y : PState J F} (related : GapRelated si se x y)
    (diverges : Diverges I E x) : Diverges J F y := by
  apply InfiniteTrace.coinduct
    (fun y => ∃ x, GapRelated si se x y ∧ Diverges I E x) ?_ ⟨x, related, diverges⟩
  rintro y ⟨x, related, diverges⟩
  obtain ⟨x', ⟨events, step⟩, tail⟩ := diverges.unfold
  obtain ⟨y', step', related'⟩ := step_gapSim si se related step
  exact ⟨y', ⟨events, step'⟩, x', related', tail⟩

theorem RunsN.gapSim (si : Isa.GapSim I J) (se : Env.Sim E F)
    {n : Nat} {x y : PState I E} {x' : PState J F} {events : List Event}
    (run : RunsN n x events y) (related : GapRelated si se x x') :
    ∃ y', RunsN n x' events y' := by
  induction run generalizing x' with
  | refl => exact ⟨x', .refl x'⟩
  | cons step _ ih =>
    obtain ⟨z, step', related'⟩ := step_gapSim si se related step
    obtain ⟨y', rest⟩ := ih related'
    exact ⟨y', .cons step' rest⟩

end Proc

namespace Model

theorem GapSim.init {M N : Model} (sim : GapSim M N) {image : Image} {input : ProcInput}
    {x : PState M.isa M.env} (init : M.Init image input x) :
    ∃ y, N.Init image input y ∧ Proc.GapRelated sim.isa sim.env x y := by
  obtain ⟨m, load, envInit⟩ := init
  obtain ⟨d, load', rc⟩ := sim.load load
  obtain ⟨t, envInit', re⟩ := sim.envInit envInit
  exact ⟨⟨d, t⟩, ⟨m, load', envInit'⟩, rc, re⟩

/-- **Nonvacuity moves up**: a launch of `M` with a run that exits gives a launch of `N` with
a run that has the same events and exits with the same status. -/
theorem GapSim.exits {M N : Model} (sim : GapSim M N) {image : Image} {input : ProcInput}
    {x y : PState M.isa M.env} {events : List Event} {status : Nat}
    (init : M.Init image input x) (run : Proc.Runs M.isa M.env x events y)
    (stop : Proc.Stop M.isa M.env y (.exited status)) :
    ∃ x' y', N.Init image input x' ∧ Proc.Runs N.isa N.env x' events y' ∧
      Proc.Stop N.isa N.env y' (.exited status) := by
  obtain ⟨x', init', related⟩ := sim.init init
  obtain ⟨y', run', related'⟩ := Proc.runs_gapSim sim.isa sim.env run related
  exact ⟨x', y', init', run', Proc.exited_gapSim sim.isa sim.env related' stop⟩

end Model

variable {M N : Model} {image : Image}

/-- **`Agrees` moves down a gap simulation.** -/
theorem Agrees.of_gapLe {S : CliSpec} (le : M.GapLe N) (h : Agrees N image S) :
    Agrees M image S := by
  obtain ⟨sim⟩ := le
  intro input x valid init events y run
  obtain ⟨x', init', related⟩ := sim.init init
  obtain ⟨y', run', related'⟩ := Proc.runs_gapSim sim.isa sim.env run related
  obtain ⟨ok, exits⟩ := h input x' valid init' events y' run'
  exact ⟨ok, fun status stop => exits status (Proc.exited_gapSim sim.isa sim.env related' stop)⟩

/-- **`Halts` moves down a gap simulation.** -/
theorem Halts.of_gapLe {domain : ProcInput → Prop} (le : M.GapLe N) (h : Halts N image domain) :
    Halts M image domain := by
  obtain ⟨sim⟩ := le
  intro input x valid inDomain init diverges
  obtain ⟨x', init', related⟩ := sim.init init
  exact h input x' valid inDomain init' (Proc.diverges_gapSim sim.isa sim.env related diverges)

/-- **`Bounded` moves down a gap simulation.** -/
theorem Bounded.of_gapLe {domain : ProcInput → Prop} {budget : ProcInput → Nat}
    {perRefusal : Nat} (le : M.GapLe N) (h : Bounded N image domain budget perRefusal) :
    Bounded M image domain budget perRefusal := by
  obtain ⟨sim⟩ := le
  intro input x valid inDomain init n events y run
  obtain ⟨x', init', related⟩ := sim.init init
  obtain ⟨y', run'⟩ := run.gapSim sim.isa sim.env related
  exact h input x' valid inDomain init' n events y' run'

end Silmaril.Process.CLI
