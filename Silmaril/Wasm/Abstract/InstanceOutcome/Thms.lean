module

public import Silmaril.Wasm.Abstract.InstanceOutcome.Defs
public import Silmaril.Wasm.Abstract.Instance.Thms
public import Silmaril.Games.Abstract.TrapCut.Thms
import Silmaril.Proofs.Wasm.Abstract.InstanceOutcome.Basic

/-!
# Scalar Wasm instances with visible divergence: theorems

* `traces_omachine`: silent host-free steps change no trace; the instance
  machine with them has exactly the traces of the existing one.
* `strategyIso_strategy_omachine`: hence state erasure is still the
  existing instance strategy `I.strategy P s`.
* `div_mem_obs_iff`: after the trace `tr`, the instance shows `div` exactly
  when it is running an export call whose thread has an infinite host-free
  run. Divergence is now an observation, distinct from a trap answer (a
  move) and from being stuck.
* `tagEquiv_cut`: the sensitive equivalence implies the trap ≈ divergence
  one (`CutEquiv (trapMove I)`).

The generic `Silmaril.Games.Abstract.OMachine.exists_cut_not_tag` shows the two
notions differ: a call answered by a trap against a call that loops silently.
A concrete pair of Core 3.0 modules exhibiting this, with the trap and the loop
proved by reduction, is not formalised here.
-/

public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Game
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Store)

variable {I : ScalarInstance} {P : Profile} {s : Store Nat}

/-- Silent host-free steps change no trace. -/
theorem traces_omachine : (omachine I P s).traces = (machine I P s).traces :=
  Silmaril.Proofs.Wasm.Abstract.InstanceOutcome.traces_omachine

/-- State erasure of the instance with silent steps is the instance strategy. -/
theorem strategyIso_strategy_omachine :
    SigBridge.strategyIso (I.strategy P s) = (omachine I P s).toMachine.denote := by
  rw [strategyIso_strategy]
  unfold Machine.denote
  rw [show (omachine I P s).toMachine.traces = (machine I P s).traces from traces_omachine]

/-- The `div` observations are exactly the host-free divergences of export
calls. -/
theorem div_mem_obs_iff {tr : List (Move I.E I.F)} :
    Obs.fin tr .div ∈ (omachine I P s).obs ↔
      ∃ f st t, (omachine I P s).Run (omachine I P s).init tr
        (show (omachine I P s).State from .running f st t) ∧
        ∃ g : Nat → Store Nat × Silmaril.Wasm.SingleThreaded.Thread,
          g 0 = (st, t) ∧ ∀ n, InternalP P (g n) (g (n + 1)) := by
  constructor
  · intro h
    cases h with
    | fin y hr hs =>
      obtain ⟨f, st, t, rfl, g, h0, hg⟩ :=
        (Silmaril.Proofs.Wasm.Abstract.InstanceOutcome.divergesFrom_iff).1 hs
      exact ⟨f, st, t, hr, g, h0, hg⟩
  · rintro ⟨f, st, t, hr, g, h0, hg⟩
    exact .fin _ hr
      ((Silmaril.Proofs.Wasm.Abstract.InstanceOutcome.divergesFrom_iff).2 ⟨f, st, t, rfl, g, h0, hg⟩)

/-- The sensitive equivalence implies the trap ≈ divergence one. -/
theorem tagEquiv_cut {s' : Store Nat} {P' : Profile} (h : (omachine I P s).TagEquiv (omachine I P' s')) :
    (omachine I P s).CutEquiv (trapMove I) (omachine I P' s') :=
  OMachine.TagEquiv.cut _ h

end Silmaril.Wasm.Abstract
