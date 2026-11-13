module

public import Silmaril.Wasm.Models.FXTRun.Thms
public import Silmaril.Wasm.Models.FXLComp.Defs
public import Silmaril.Wasm.FX.Examples.Threads.Thms

/-!
# The ytk scheduler alone under `StepFXT`

The explainer's scheduler `ytk` (yield on fork, new thread first), run alone on `cont.new $main` (function `14` of
`Silmaril.Wasm.FX.Examples.Threads.dynP`) and compiled by `Silmaril.Wasm.Models.FXLComp`, prints its
block of the documented output under `StepFXT`: `ytk_fxt`, `ytk_sim`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Examples.ThreadsT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FXT Silmaril.Wasm.Models.FXLComp
open Silmaril.Wasm.Models.FXTRun Silmaril.Proofs.Wasm.Models.FXTRun Silmaril.Wasm.FX.Examples.Threads
open Silmaril.Wasm.Models.FXL (beh Obs init)
open Silmaril.Wasm.Numerics (Profile)

/-- The computed `StepFXT` run of the compiled `ytk` example ends with its log. -/
theorem ytk_check :
    checkT dynAr (fxOf dynP 2) (intrOf dynP) 40 400 (initT dynP 2 14) (logV ytkLog) = true := by
  decide +kernel

/-- **The compiled `ytk` example prints its documented output under `StepFXT`**, at every
profile and host. -/
theorem ytk_fxt (P : Profile) (host : HostSemantics Nat) :
    ObsT.ret (logV ytkLog) (.returns []) ∈
      behavioursT P host (fxOf dynP 2) (intrOf dynP) (initT dynP 2 14) :=
  checkT_mem ytk_check

/-- **The `StepFXL` behaviour of `ytk` is a `StepFXT` behaviour of its compilation**
(read through `logV`). -/
theorem ytk_sim (P : Profile) (host : HostSemantics Nat) :
    ∀ o ∈ beh dynP dynAr (init dynP 14), ∃ l, o = Obs.done l [] ∧
      ObsT.ret (logV l) (.returns []) ∈
        behavioursT P host (fxOf dynP 2) (intrOf dynP) (initT dynP 2 14) := by
  intro o ho
  rw [ytk_beh] at ho
  exact ⟨_, ho, ytk_fxt P host⟩

end Silmaril.Proofs.Wasm.FX.Examples.ThreadsT
