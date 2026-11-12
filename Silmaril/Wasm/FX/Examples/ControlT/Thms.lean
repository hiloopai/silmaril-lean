module

public import Silmaril.Wasm.FX.Examples.Control.Thms
public import Silmaril.Wasm.Models.FXTRun.Thms
public import Silmaril.Wasm.Models.FXLComp.Defs

/-!
# `control0`/`prompt0` compiled to `StepFXT`

The `StepFXL` programs of `Silmaril.Wasm.FX.Examples.Control`, compiled by
`Silmaril.Wasm.Models.FXLComp` (locals, so `$h` and `$k` of `$apply` and `$k` of the handler
functions, become continuation cells; `print_i32` is the `log` intrinsic), print the same logs
under `StepFXT`, at every profile and host. Each run is computed by the sound interpreter
`Silmaril.Wasm.Models.FXTRun` and checked by the kernel (`decide +kernel`):

* **`abort_fxt`**, **`resume_fxt`**, **`escape_fxt`**, **`outside_fxt`**;
* `…_sim`: the only `StepFXL` behaviour of the source is matched by this `StepFXT` behaviour of
  its compilation.

Membership only: that the compiled program has no other `StepFXT` behaviour is not proved. The
one-shot program `twiceP` traps, and `checkT` checks only runs that finish, so it is not carried
over. Cells are shared by the activations of a function; in `escapeP` and `outsideP` two
`$prompt`s and two `$apply`s are active at once, which is harmless here because neither reads a
local after a nested activation could have written it (and the check is a computation of the
compiled program itself).

A Silmaril addition (Follow-up 5 workflow, track fx).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Examples.ControlT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FXT Silmaril.Wasm.Models.FXLComp
open Silmaril.Wasm.Models.FXTRun Silmaril.Proofs.Wasm.Models.FXTRun Silmaril.Wasm.FX.Examples.Control
open Silmaril.Wasm.Models.FXL (beh Obs init)
open Silmaril.Wasm.Numerics (Profile)

theorem abort_check :
    checkT ctlAr (fxOf abortP 1) (intrOf abortP) 40 400 (initT abortP 1 5) (logV abortLog) =
      true := by
  decide +kernel

/-- **Abort, compiled**: prints `1 2 4` under `StepFXT`. -/
theorem abort_fxt (P : Profile) (host : HostSemantics Nat) :
    ObsT.ret (logV abortLog) (.returns []) ∈
      behavioursT P host (fxOf abortP 1) (intrOf abortP) (initT abortP 1 5) :=
  checkT_mem abort_check

theorem resume_check :
    checkT ctlAr (fxOf resumeP 1) (intrOf resumeP) 40 400 (initT resumeP 1 5) (logV resumeLog) =
      true := by
  decide +kernel

/-- **Resume once, compiled**: prints `1 2 3 4 5` under `StepFXT`. -/
theorem resume_fxt (P : Profile) (host : HostSemantics Nat) :
    ObsT.ret (logV resumeLog) (.returns []) ∈
      behavioursT P host (fxOf resumeP 1) (intrOf resumeP) (initT resumeP 1 5) :=
  checkT_mem resume_check

theorem escape_check :
    checkT ctlAr (fxOf escapeP 1) (intrOf escapeP) 40 800 (initT escapeP 1 6) (logV escapeLog) =
      true := by
  decide +kernel

/-- **The continuation excludes the prompt, compiled**: prints `1 2 3 5 9 10` under
`StepFXT`. -/
theorem escape_fxt (P : Profile) (host : HostSemantics Nat) :
    ObsT.ret (logV escapeLog) (.returns []) ∈
      behavioursT P host (fxOf escapeP 1) (intrOf escapeP) (initT escapeP 1 6) :=
  checkT_mem escape_check

theorem outside_check :
    checkT ctlAr (fxOf outsideP 1) (intrOf outsideP) 40 800 (initT outsideP 1 6)
      (logV outsideLog) = true := by
  decide +kernel

/-- **The handler runs outside the prompt, compiled**: prints `1 2 3 4 5` under `StepFXT`. -/
theorem outside_fxt (P : Profile) (host : HostSemantics Nat) :
    ObsT.ret (logV outsideLog) (.returns []) ∈
      behavioursT P host (fxOf outsideP 1) (intrOf outsideP) (initT outsideP 1 6) :=
  checkT_mem outside_check

/-- The `StepFXL` behaviour of `abortP` is a `StepFXT` behaviour of its compilation. -/
theorem abort_sim (P : Profile) (host : HostSemantics Nat) :
    ∀ o ∈ beh abortP ctlAr (init abortP 5), ∃ l, o = Obs.done l [] ∧
      ObsT.ret (logV l) (.returns []) ∈
        behavioursT P host (fxOf abortP 1) (intrOf abortP) (initT abortP 1 5) := by
  intro o ho
  rw [abort_beh] at ho
  exact ⟨_, ho, abort_fxt P host⟩

/-- The `StepFXL` behaviour of `resumeP` is a `StepFXT` behaviour of its compilation. -/
theorem resume_sim (P : Profile) (host : HostSemantics Nat) :
    ∀ o ∈ beh resumeP ctlAr (init resumeP 5), ∃ l, o = Obs.done l [] ∧
      ObsT.ret (logV l) (.returns []) ∈
        behavioursT P host (fxOf resumeP 1) (intrOf resumeP) (initT resumeP 1 5) := by
  intro o ho
  rw [resume_beh] at ho
  exact ⟨_, ho, resume_fxt P host⟩

/-- The `StepFXL` behaviour of `escapeP` is a `StepFXT` behaviour of its compilation. -/
theorem escape_sim (P : Profile) (host : HostSemantics Nat) :
    ∀ o ∈ beh escapeP ctlAr (init escapeP 6), ∃ l, o = Obs.done l [] ∧
      ObsT.ret (logV l) (.returns []) ∈
        behavioursT P host (fxOf escapeP 1) (intrOf escapeP) (initT escapeP 1 6) := by
  intro o ho
  rw [escape_beh] at ho
  exact ⟨_, ho, escape_fxt P host⟩

/-- The `StepFXL` behaviour of `outsideP` is a `StepFXT` behaviour of its compilation. -/
theorem outside_sim (P : Profile) (host : HostSemantics Nat) :
    ∀ o ∈ beh outsideP ctlAr (init outsideP 6), ∃ l, o = Obs.done l [] ∧
      ObsT.ret (logV l) (.returns []) ∈
        behavioursT P host (fxOf outsideP 1) (intrOf outsideP) (initT outsideP 1 6) := by
  intro o ho
  rw [outside_beh] at ho
  exact ⟨_, ho, outside_fxt P host⟩

end Silmaril.Wasm.FX.Examples.ControlT
