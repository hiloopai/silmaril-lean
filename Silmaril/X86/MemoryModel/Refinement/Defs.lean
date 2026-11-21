module

public import Silmaril.Semantics.MemoryRefinement.Defs
public import Silmaril.X86.Concurrency.Lift.Defs
public import Silmaril.X86.MemoryModel.Lattice.Defs

/-! # Two uses of the x86 consistency models

`guarded` checks a program's candidate executions *before* filtering by
consistency. `under` uses the existing single-thread memory-event reading of a
successful machine run. Neither construction changes the ISA or the loader.
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Refinement

open Silmaril.Semantics.MemoryRefinement
open Silmaril.Machine.Execution (run)
open Silmaril.X86.Concurrency
open Silmaril.X86.MemoryModel.Axiomatic (Exec)
open Silmaril.X86.MemoryModel.Litmus (XAct)

/-- An entry supplies all candidates of a client. Do not check races only on SC executions. -/
def guarded (allowed good : Exec → Prop) : Model Exec where
  Entry := Exec → Prop
  may candidates exec := candidates exec ∧ allowed exec
  ub candidates := ¬ ∀ exec, candidates exec → good exec

def raceFree (exec : Exec) : Prop := exec.Unsplit ∧ exec.DrfL

variable {State Obs : Type}

/-- A finite sequential observation. A fault before the requested endpoint is not a success. -/
def sequential (step : State → Option State) (count : Nat) (see : State → State → Obs) : Model Obs :=
  ofEval fun start => (run step count start).map (see start)

/-- The same endpoint, required to have a `Lift.RunUnder` certificate: its trace exists and has
exactly the final backing memory as its one-thread behaviour. Failure means there is no such endpoint. -/
def under (step : State → Option State) (mem : State → Cir.Mem) (events : State → List XAct → Prop)
    (model : Exec → Prop) (count : Nat) (see : State → State → Obs) : Model Obs :=
  let completes := fun start stop => run step count start = some stop ∧ Lift.RunUnder model step mem events start stop
  ⟨State, fun start out => ∃ stop, completes start stop ∧ see start stop = out,
    fun start => ¬ ∃ stop, completes start stop⟩

end Silmaril.X86.MemoryModel.Refinement
