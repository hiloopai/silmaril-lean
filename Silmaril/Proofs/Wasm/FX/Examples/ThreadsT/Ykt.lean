module

public import Silmaril.Wasm.Models.FXTRun.Thms
public import Silmaril.Wasm.Models.FXLComp.Defs
public import Silmaril.Wasm.FX.Examples.Threads.Thms

/-!
# The ykt scheduler alone under `StepFXT`

The explainer's scheduler `ykt` (yield on fork, continuation first), run alone on `cont.new $main` (function `13` of
`Silmaril.Wasm.FX.Examples.Threads.dynP`) and compiled by `Silmaril.Wasm.Models.FXLComp`, prints its
block of the documented output under `StepFXT`: `ykt_fxt`, `ykt_sim`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Examples.ThreadsT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FXT Silmaril.Wasm.Models.FXLComp
open Silmaril.Wasm.Models.FXTRun Silmaril.Proofs.Wasm.Models.FXTRun Silmaril.Wasm.FX.Examples.Threads
open Silmaril.Wasm.Models.FXL (beh Obs init)
open Silmaril.Wasm.Numerics (Profile)

/-- The computed `StepFXT` run of the compiled `ykt` example ends with its log. -/
theorem ykt_check :
    checkT dynAr (fxOf dynP 2) (intrOf dynP) 40 400 (initT dynP 2 13) (logV yktLog) = true := by
  decide +kernel

/-- **The compiled `ykt` example prints its documented output under `StepFXT`**, at every
profile and host. -/
theorem ykt_fxt (P : Profile) (host : HostSemantics Nat) :
    ObsT.ret (logV yktLog) (.returns []) ∈
      behavioursT P host (fxOf dynP 2) (intrOf dynP) (initT dynP 2 13) :=
  checkT_mem ykt_check

/-- **The `StepFXL` behaviour of `ykt` is a `StepFXT` behaviour of its compilation**
(read through `logV`). -/
theorem ykt_sim (P : Profile) (host : HostSemantics Nat) :
    ∀ o ∈ beh dynP dynAr (init dynP 13), ∃ l, o = Obs.done l [] ∧
      ObsT.ret (logV l) (.returns []) ∈
        behavioursT P host (fxOf dynP 2) (intrOf dynP) (initT dynP 2 13) := by
  intro o ho
  rw [ykt_beh] at ho
  exact ⟨_, ho, ykt_fxt P host⟩

end Silmaril.Proofs.Wasm.FX.Examples.ThreadsT
