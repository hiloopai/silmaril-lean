module

public import Silmaril.Wasm.Models.FXTRun.Thms
public import Silmaril.Wasm.Models.FXLComp.Defs
public import Silmaril.Wasm.FX.Examples.Threads.Thms

/-!
# The kt scheduler alone under `StepFXT`

The explainer's scheduler `kt` (no yield on fork, continuation first), run alone on `cont.new $main` (function `11` of
`Silmaril.Wasm.FX.Examples.Threads.dynP`) and compiled by `Silmaril.Wasm.Models.FXLComp`, prints its
block of the documented output under `StepFXT`: `kt_fxt`, `kt_sim`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Examples.ThreadsT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FXT Silmaril.Wasm.Models.FXLComp
open Silmaril.Wasm.Models.FXTRun Silmaril.Proofs.Wasm.Models.FXTRun Silmaril.Wasm.FX.Examples.Threads
open Silmaril.Wasm.Models.FXL (beh Obs init)
open Silmaril.Wasm.Numerics (Profile)

/-- The computed `StepFXT` run of the compiled `kt` example ends with its log. -/
theorem kt_check :
    checkT dynAr (fxOf dynP 2) (intrOf dynP) 40 400 (initT dynP 2 11) (logV ktLog) = true := by
  decide +kernel

/-- **The compiled `kt` example prints its documented output under `StepFXT`**, at every
profile and host. -/
theorem kt_fxt (P : Profile) (host : HostSemantics Nat) :
    ObsT.ret (logV ktLog) (.returns []) ∈
      behavioursT P host (fxOf dynP 2) (intrOf dynP) (initT dynP 2 11) :=
  checkT_mem kt_check

/-- **The `StepFXL` behaviour of `kt` is a `StepFXT` behaviour of its compilation**
(read through `logV`). -/
theorem kt_sim (P : Profile) (host : HostSemantics Nat) :
    ∀ o ∈ beh dynP dynAr (init dynP 11), ∃ l, o = Obs.done l [] ∧
      ObsT.ret (logV l) (.returns []) ∈
        behavioursT P host (fxOf dynP 2) (intrOf dynP) (initT dynP 2 11) := by
  intro o ho
  rw [kt_beh] at ho
  exact ⟨_, ho, kt_fxt P host⟩

end Silmaril.Proofs.Wasm.FX.Examples.ThreadsT
