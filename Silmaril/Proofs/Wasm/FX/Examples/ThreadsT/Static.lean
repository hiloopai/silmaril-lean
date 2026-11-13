module

public import Silmaril.Wasm.Models.FXTRun.Thms
public import Silmaril.Wasm.Models.FXLComp.Defs
public import Silmaril.Wasm.FX.Examples.Threads.Thms

/-!
# The static lightweight threads under `StepFXT`

The explainer's static example (`Silmaril.Wasm.FX.Examples.Threads.staticP`), compiled by
`Silmaril.Wasm.Models.FXLComp`, prints `-1 10 20 30 11 21 31 12 22 32 -2` under `StepFXT`:
`static_fxt` (a checked run of the sound interpreter `Silmaril.Wasm.Models.FXTRun`), and
`static_sim`: the only `StepFXL` behaviour is matched.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Examples.ThreadsT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FXT Silmaril.Wasm.Models.FXLComp
open Silmaril.Wasm.Models.FXTRun Silmaril.Proofs.Wasm.Models.FXTRun Silmaril.Wasm.FX.Examples.Threads
open Silmaril.Wasm.Models.FXL (beh Obs init)
open Silmaril.Wasm.Numerics (Profile)

/-- The computed `StepFXT` run of the compiled `static` example ends with its log. -/
theorem static_check :
    checkT staticAr (fxOf staticP 1) (intrOf staticP) 40 400 (initT staticP 1 4) (logV staticLog) = true := by
  decide +kernel

/-- **The compiled `static` example prints its documented output under `StepFXT`**, at every
profile and host. -/
theorem static_fxt (P : Profile) (host : HostSemantics Nat) :
    ObsT.ret (logV staticLog) (.returns []) ∈
      behavioursT P host (fxOf staticP 1) (intrOf staticP) (initT staticP 1 4) :=
  checkT_mem static_check

/-- **The `StepFXL` behaviour of `static` is a `StepFXT` behaviour of its compilation**
(read through `logV`). -/
theorem static_sim (P : Profile) (host : HostSemantics Nat) :
    ∀ o ∈ beh staticP staticAr (init staticP 4), ∃ l, o = Obs.done l [] ∧
      ObsT.ret (logV l) (.returns []) ∈
        behavioursT P host (fxOf staticP 1) (intrOf staticP) (initT staticP 1 4) := by
  intro o ho
  rw [static_beh] at ho
  exact ⟨_, ho, static_fxt P host⟩

end Silmaril.Proofs.Wasm.FX.Examples.ThreadsT
