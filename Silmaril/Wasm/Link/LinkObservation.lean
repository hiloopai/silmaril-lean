module

public import Silmaril.Wasm.Link.WholeSimulation
public import Silmaril.Wasm.SingleThreaded.Exec.StatusComplete

/-! # Every terminal linked execution has the proved outcome

Whole-run simulation constructs a related target execution. Host-free
confluence identifies any other terminal target execution with that witness,
including its exact final store and frame.

## Grow oracles

The agreement theorems hold for every deterministic profile `profile o`, with
source and linked runs consulting the *same* grow oracle `o`. `memory.grow` and
`table.grow` ask `o` about `(kind, address, current size, delta)`; the hard
limits are enforced separately, so `o` can only add failures. Sharing `o` is
sound because the linker profile rejects memories and tables: grows happen only
in ambient code, whose memory/table addresses `StoreRelation.Related` requires
to be equal, and ordinary preparation permutes only global addresses. The
original `neverFail` statements are the instances `o := neverFail`.

A renaming-aware form (target oracle `o'` with `o' k (ρ a) = o k a` for a
memory/table address renaming `ρ`) is not stated: with `ρ` the identity it
collapses to `o' = o`. It is the intended hook once memories or tables enter
the linker profile and the store relation starts renaming their addresses.

## Nondeterministic profile

`spec_result` is the forward inclusion for `Profile.spec false {}` (which every
deterministic profile refines, `Step.deterministic_refines`): each terminal
source outcome is achieved by some linked run with the same result. The
converse inclusion does not follow from confluence, which fails for this
profile. It needs a backward simulation, or an occurrence-indexed oracle: a
fixed `(kind, address, size, delta)` oracle cannot replay a run in which the
same grow first fails and later succeeds.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.LinkObservation

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det
open AdminRelation Simulation

variable {o : GrowOracle}

def Terminal {H : Type} (c : Config H) : Prop := ∃ result : Result, c.code = result.toAdmin

theorem result_terminal {H : Type} {P : Profile} {c : Config H} {result : Result}
    (returned : c.code = result.toAdmin) : ∀ final, ¬ Step P Simulation.noHost c final := by
  rcases c with ⟨s,f,code⟩
  change code = result.toAdmin at returned
  subst code
  cases result with
  | values vs => exact fun _ h => not_step_vals h
  | throw a => exact fun _ h => not_step_throwing h
  | trap => exact fun _ h => not_step_trap h

theorem Terminal.no_step {H : Type} {P : Profile} {c : Config H} (terminal : Terminal c) :
    ∀ final, ¬ Step P Simulation.noHost c final := by
  obtain ⟨result,returned⟩ := terminal
  exact result_terminal returned

theorem terminal_unique {H : Type} {initial final other : Config H}
    (run : Steps (profile o) Simulation.noHost initial final)
    (otherRun : Steps (profile o) Simulation.noHost initial other)
    (terminal : Terminal final) (otherTerminal : Terminal other) : final = other :=
  nf_unique_of_join (fun a b => Det.DStep.join' a b) run otherRun
    terminal.no_step otherTerminal.no_step

theorem result_code_injective : Function.Injective Result.toAdmin := by
  intro left right equal
  cases left with
  | values vs =>
    cases right with
    | values ws => exact congrArg Result.values (vals_inj.mp equal)
    | throw a =>
      dsimp only [Result.toAdmin] at equal
      have member : Admin.plain .throwRef ∈ vals vs := by rw [equal]; simp
      exact False.elim (mem_vals member rfl)
    | trap =>
      dsimp only [Result.toAdmin] at equal
      have member : Admin.trap ∈ vals vs := by rw [equal]; simp
      exact False.elim (mem_vals member rfl)
  | throw a =>
    cases right with
    | values vs =>
      dsimp only [Result.toAdmin] at equal
      have member : Admin.plain .throwRef ∈ vals vs := by rw [← equal]; simp
      exact False.elim (mem_vals member rfl)
    | throw b =>
      have addresses : a = b := by simpa only [Result.toAdmin,List.cons.injEq,
        Admin.ref.injEq,Ref.exn.injEq,and_true] using equal
      exact congrArg Result.throw addresses
    | trap => simp only [Result.toAdmin,List.cons.injEq,reduceCtorEq,false_and] at equal
  | trap =>
    cases right with
    | values vs =>
      dsimp only [Result.toAdmin] at equal
      have member : Admin.trap ∈ vals vs := by rw [← equal]; simp
      exact False.elim (mem_vals member rfl)
    | throw a => simp only [Result.toAdmin,List.cons.injEq,reduceCtorEq,false_and] at equal
    | trap => rfl

theorem paired_result {H : Type} {source target : Config H} {mode : Mode} {result : Result}
    (matching : Matching mode source target) (returned : source.code = result.toAdmin) :
    target.code = result.toAdmin := by
  have control := matching.code
  rw [returned] at control
  cases result with
  | values vs => exact control.values_left
  | throw a => exact control.throwing_left
  | trap => exact control.trap_singleton

/-- A terminal target run must end at the related target configuration
constructed from the typed source run. No target success premise is needed. -/
theorem terminal_result {H : Type} {source sourceFinal target targetFinal : Config H} {mode : Mode}
    {types : List CValType} {result : Result}
    (sourceRun : Steps (profile o) Simulation.noHost source sourceFinal)
    (typed : ConfigOk source types) (matching : Matching mode source target)
    (returned : sourceFinal.code = result.toAdmin)
    (targetRun : Steps (profile o) Simulation.noHost target targetFinal)
    (terminal : Terminal targetFinal) :
    Matching mode sourceFinal targetFinal ∧ targetFinal.code = result.toAdmin := by
  obtain ⟨constructed,constructedRun,paired⟩ := WholeSimulation.steps sourceRun typed matching
  have constructedResult := paired_result paired returned
  have equal := terminal_unique constructedRun targetRun ⟨result,constructedResult⟩ terminal
  subst targetFinal
  exact ⟨paired,constructedResult⟩

/-- Every terminal target outcome equals the source outcome, and its actual
final store and frame retain the linking relation. -/
theorem result_agreement {H : Type} {source sourceFinal target targetFinal : Config H} {mode : Mode}
    {types : List CValType} {result observed : Result}
    (sourceRun : Steps (profile o) Simulation.noHost source sourceFinal)
    (typed : ConfigOk source types) (matching : Matching mode source target)
    (returned : sourceFinal.code = result.toAdmin)
    (targetRun : Steps (profile o) Simulation.noHost target targetFinal)
    (observedResult : targetFinal.code = observed.toAdmin) :
    observed = result ∧ Matching mode sourceFinal targetFinal := by
  obtain ⟨paired,targetResult⟩ := terminal_result sourceRun typed matching returned targetRun
    ⟨observed,observedResult⟩
  exact ⟨(result_code_injective (targetResult.symm.trans observedResult)).symm,paired⟩

theorem values_result {H : Type} {source sourceFinal target targetFinal : Config H} {mode : Mode}
    {types : List CValType} {vs : List Val} {observed : Result}
    (sourceRun : Steps (profile o) Simulation.noHost source sourceFinal)
    (typed : ConfigOk source types) (matching : Matching mode source target)
    (returned : sourceFinal.code = vals vs)
    (targetRun : Steps (profile o) Simulation.noHost target targetFinal)
    (observedResult : targetFinal.code = observed.toAdmin) :
    observed = .values vs ∧ Matching mode sourceFinal targetFinal :=
  result_agreement sourceRun typed matching returned targetRun observedResult

theorem trap_result {H : Type} {source sourceFinal target targetFinal : Config H} {mode : Mode}
    {types : List CValType} {observed : Result}
    (sourceRun : Steps (profile o) Simulation.noHost source sourceFinal)
    (typed : ConfigOk source types) (matching : Matching mode source target)
    (trapped : sourceFinal.code = [.trap])
    (targetRun : Steps (profile o) Simulation.noHost target targetFinal)
    (observedResult : targetFinal.code = observed.toAdmin) :
    observed = .trap ∧ Matching mode sourceFinal targetFinal :=
  result_agreement sourceRun typed matching trapped targetRun observedResult

/-- Deterministic runs are runs of the nondeterministic spec profile. -/
theorem spec_steps {H : Type} {initial final : Config H}
    (run : Steps (profile o) Simulation.noHost initial final) :
    Steps (Profile.spec false {}) Simulation.noHost initial final := by
  induction run with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (Step.deterministic_refines step)

/-- Forward inclusion for the nondeterministic spec profile: every terminal
outcome of a typed source run is achieved by some linked run with the same
result, retaining the linking relation.

Only this direction is proved. The converse (every terminal linked outcome is a
source outcome) needs a backward simulation or an occurrence-indexed grow
oracle; a fixed `(kind, address, size, delta)` oracle cannot replay a run that
fails and then succeeds the same grow. -/
theorem spec_result {H : Type} {source sourceFinal target : Config H} {mode : Mode}
    {types : List CValType} {result : Result}
    (sourceRun : Steps (Profile.spec false {}) Simulation.noHost source sourceFinal)
    (typed : ConfigOk source types) (matching : Matching mode source target)
    (returned : sourceFinal.code = result.toAdmin) :
    ∃ targetFinal, Steps (Profile.spec false {}) Simulation.noHost target targetFinal ∧
      Matching mode sourceFinal targetFinal ∧ targetFinal.code = result.toAdmin := by
  obtain ⟨targetFinal,targetRun,paired⟩ := WholeSimulation.steps sourceRun typed matching
  exact ⟨targetFinal,targetRun,paired,paired_result paired returned⟩

/-- A terminal deterministic source run under any grow oracle is matched by a
linked run of the nondeterministic spec profile with the same result. -/
theorem profile_spec_result {H : Type} {source sourceFinal target : Config H} {mode : Mode}
    {types : List CValType} {result : Result}
    (sourceRun : Steps (profile o) Simulation.noHost source sourceFinal)
    (typed : ConfigOk source types) (matching : Matching mode source target)
    (returned : sourceFinal.code = result.toAdmin) :
    ∃ targetFinal, Steps (Profile.spec false {}) Simulation.noHost target targetFinal ∧
      Matching mode sourceFinal targetFinal ∧ targetFinal.code = result.toAdmin :=
  spec_result (spec_steps sourceRun) typed matching returned

end Silmaril.Wasm.Link.GC.LinkObservation
