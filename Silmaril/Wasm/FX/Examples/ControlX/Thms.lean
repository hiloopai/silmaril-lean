module

public import Silmaril.Wasm.FX.Examples.Control.Thms
public import Silmaril.Wasm.FX.Examples.ControlX.Defs
public import Silmaril.Wasm.Models.FXTRunX.Thms
public import Silmaril.Wasm.Models.FXLComp.Defs

/-!
# The one-shot program `twiceP`, compiled to `StepFXT`: a trap

`Silmaril.Wasm.FX.Examples.ControlT` carries four `control0`/`prompt0` programs to `StepFXT`, but
not `twiceP`, whose second `resume` of the same continuation traps, because `checkT` checks only
runs that finish with no values. With the trap steps of `Silmaril.Wasm.Models.FXTRunX`:

* **`twice_fxt`**: the compiled `twiceP` prints `1 2` and traps under `StepFXT`, at every profile
  and host (the cell of `$k` still holds the continuation reference after the first `resume`;
  the second `resume` finds it consumed: `resumeUsed`, then the trap leaves every frame);
* **`twice_sim`**: the only `StepFXL` behaviour of `twiceP` (`twice_beh`) is matched by this
  `StepFXT` behaviour.

Membership only, as for the other four programs. **Why not exact sets**: `StepFXT` is not
deterministic on these programs. At the `control0` of each of the five programs, the `suspend`
may take the payload `h` (the interpreter's step) or the empty payload; both are `StepFXT`
steps from a reachable configuration, with different results (`abort_split`, `resume_split`,
`escape_split`, `outside_split`, `twice_split`, from `split_of_check`). The empty payload leaves
one value for the `br 0` out of a label of arity `2`, where the interpreter has no step. So an
exact behaviour set needs, besides the computed run, an inversion of every `StepFXT` step along
it (Core head steps, intrinsic calls, `seq` decompositions), a proof that each other split is a
dead end, and the absence of infinite runs; none of that is done here.

A Silmaril addition (Follow-up 5 workflow, track fx).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Examples.ControlX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FXT Silmaril.Wasm.Models.FXLComp
open Silmaril.Wasm.Models.FXTRunX Silmaril.Proofs.Wasm.Models.FXTRunX Silmaril.Wasm.FX.Examples.Control
open Silmaril.Wasm.Models.FXTRun Silmaril.Proofs.Wasm.Models.FXTRun
open Silmaril.Wasm.Models.FXL (beh Obs init)
open Silmaril.Wasm.Numerics (Profile)

theorem twice_check :
    checkTrapX ctlAr (fxOf twiceP 1) (intrOf twiceP) 40 400 (initT twiceP 1 5) (logV twiceLog) =
      true := by
  decide +kernel

/-- **One-shot, compiled**: prints `1 2` and traps under `StepFXT`. -/
theorem twice_fxt (P : Profile) (host : HostSemantics Nat) :
    ObsT.ret (logV twiceLog) .traps ∈
      behavioursT P host (fxOf twiceP 1) (intrOf twiceP) (initT twiceP 1 5) :=
  checkTrapX_mem twice_check

/-- The `StepFXL` behaviour of `twiceP` is a `StepFXT` behaviour of its compilation. -/
theorem twice_sim (P : Profile) (host : HostSemantics Nat) :
    ∀ o ∈ beh twiceP ctlAr (init twiceP 5), ∃ l, o = Obs.trap l ∧
      ObsT.ret (logV l) .traps ∈
        behavioursT P host (fxOf twiceP 1) (intrOf twiceP) (initT twiceP 1 5) := by
  intro o ho
  rw [twice_beh] at ho
  exact ⟨_, ho, twice_fxt P host⟩

/-! ## `StepFXT` is not deterministic at `control0` -/

/-- **Two different `StepFXT` steps from a reachable configuration**, when `splitAt` holds. -/
theorem split_of_check {P : Silmaril.Wasm.Models.FXL.Prog} {m n : Nat} (h : splitAt P m n = true)
    (Pr : Profile) (host : HostSemantics Nat) :
    ∃ c c₁ c₂, StepsT Pr host (fxOf P 1) (intrOf P) (initT P 1 m) c ∧
      StepFXT Pr host (fxOf P 1) (intrOf P) c c₁ ∧ StepFXT Pr host (fxOf P 1) (intrOf P) c c₂ ∧
      c₁ ≠ c₂ := by
  unfold splitAt at h
  cases h₁ : stepC ctlAr (fxOf P 1) (intrOf P) 40 (cfgAt P m n) with
  | none => simp [h₁] at h
  | some c₁ =>
    cases h₂ : stepC (fun _ => 0) (fxOf P 1) (intrOf P) 40 (cfgAt P m n) with
    | none => simp [h₁, h₂] at h
    | some c₂ =>
      have hs : (stepC ctlAr (fxOf P 1) (intrOf P) 40 c₁).isSome = true ∧
          stepC ctlAr (fxOf P 1) (intrOf P) 40 c₂ = none := by
        simpa [h₁, h₂] using h
      refine ⟨cfgAt P m n, c₁, c₂, runT_sound n _, stepC_sound h₁, stepC_sound h₂, ?_⟩
      intro heq
      have hc : (stepC ctlAr (fxOf P 1) (intrOf P) 40 c₂).isSome = true := heq ▸ hs.1
      rw [hs.2] at hc
      cases hc

theorem abort_check2 : splitAt abortP 5 15 = true := by decide +kernel
theorem resume_check2 : splitAt resumeP 5 15 = true := by decide +kernel
theorem escape_check2 : splitAt escapeP 6 28 = true := by decide +kernel
theorem outside_check2 : splitAt outsideP 6 28 = true := by decide +kernel
theorem twice_check2 : splitAt twiceP 5 15 = true := by decide +kernel

/-- `abortP`, compiled: two different `StepFXT` steps at its `control0`. -/
theorem abort_split (Pr : Profile) (host : HostSemantics Nat) :
    ∃ c c₁ c₂, StepsT Pr host (fxOf abortP 1) (intrOf abortP) (initT abortP 1 5) c ∧
      StepFXT Pr host (fxOf abortP 1) (intrOf abortP) c c₁ ∧
      StepFXT Pr host (fxOf abortP 1) (intrOf abortP) c c₂ ∧ c₁ ≠ c₂ :=
  split_of_check abort_check2 Pr host

/-- `resumeP`, compiled: two different `StepFXT` steps at its `control0`. -/
theorem resume_split (Pr : Profile) (host : HostSemantics Nat) :
    ∃ c c₁ c₂, StepsT Pr host (fxOf resumeP 1) (intrOf resumeP) (initT resumeP 1 5) c ∧
      StepFXT Pr host (fxOf resumeP 1) (intrOf resumeP) c c₁ ∧
      StepFXT Pr host (fxOf resumeP 1) (intrOf resumeP) c c₂ ∧ c₁ ≠ c₂ :=
  split_of_check resume_check2 Pr host

/-- `escapeP`, compiled: two different `StepFXT` steps at its first `control0`. -/
theorem escape_split (Pr : Profile) (host : HostSemantics Nat) :
    ∃ c c₁ c₂, StepsT Pr host (fxOf escapeP 1) (intrOf escapeP) (initT escapeP 1 6) c ∧
      StepFXT Pr host (fxOf escapeP 1) (intrOf escapeP) c c₁ ∧
      StepFXT Pr host (fxOf escapeP 1) (intrOf escapeP) c c₂ ∧ c₁ ≠ c₂ :=
  split_of_check escape_check2 Pr host

/-- `outsideP`, compiled: two different `StepFXT` steps at its first `control0`. -/
theorem outside_split (Pr : Profile) (host : HostSemantics Nat) :
    ∃ c c₁ c₂, StepsT Pr host (fxOf outsideP 1) (intrOf outsideP) (initT outsideP 1 6) c ∧
      StepFXT Pr host (fxOf outsideP 1) (intrOf outsideP) c c₁ ∧
      StepFXT Pr host (fxOf outsideP 1) (intrOf outsideP) c c₂ ∧ c₁ ≠ c₂ :=
  split_of_check outside_check2 Pr host

/-- `twiceP`, compiled: two different `StepFXT` steps at its `control0`. -/
theorem twice_split (Pr : Profile) (host : HostSemantics Nat) :
    ∃ c c₁ c₂, StepsT Pr host (fxOf twiceP 1) (intrOf twiceP) (initT twiceP 1 5) c ∧
      StepFXT Pr host (fxOf twiceP 1) (intrOf twiceP) c c₁ ∧
      StepFXT Pr host (fxOf twiceP 1) (intrOf twiceP) c c₂ ∧ c₁ ≠ c₂ :=
  split_of_check twice_check2 Pr host

end Silmaril.Wasm.FX.Examples.ControlX
