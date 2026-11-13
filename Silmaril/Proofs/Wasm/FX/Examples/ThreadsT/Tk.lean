module

public import Silmaril.Wasm.Models.FXTRun.Thms
public import Silmaril.Wasm.Models.FXLComp.Defs
public import Silmaril.Wasm.FX.Examples.Threads.Thms

/-!
# The tk scheduler alone under `StepFXT`

The explainer's scheduler `tk` (no yield on fork, new thread first), run alone on `cont.new $main` (function `12` of
`Silmaril.Wasm.FX.Examples.Threads.dynP`) and compiled by `Silmaril.Wasm.Models.FXLComp`, prints its
block of the documented output under `StepFXT`: `tk_fxt`, `tk_sim`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Examples.ThreadsT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FXT Silmaril.Wasm.Models.FXLComp
open Silmaril.Wasm.Models.FXTRun Silmaril.Proofs.Wasm.Models.FXTRun Silmaril.Wasm.FX.Examples.Threads
open Silmaril.Wasm.Models.FXL (beh Obs init)
open Silmaril.Wasm.Numerics (Profile)

/-- The computed `StepFXT` run of the compiled `tk` example ends with its log. -/
theorem tk_check :
    checkT dynAr (fxOf dynP 2) (intrOf dynP) 40 400 (initT dynP 2 12) (logV tkLog) = true := by
  decide +kernel

/-- **The compiled `tk` example prints its documented output under `StepFXT`**, at every
profile and host. -/
theorem tk_fxt (P : Profile) (host : HostSemantics Nat) :
    ObsT.ret (logV tkLog) (.returns []) ∈
      behavioursT P host (fxOf dynP 2) (intrOf dynP) (initT dynP 2 12) :=
  checkT_mem tk_check

/-- **The `StepFXL` behaviour of `tk` is a `StepFXT` behaviour of its compilation**
(read through `logV`). -/
theorem tk_sim (P : Profile) (host : HostSemantics Nat) :
    ∀ o ∈ beh dynP dynAr (init dynP 12), ∃ l, o = Obs.done l [] ∧
      ObsT.ret (logV l) (.returns []) ∈
        behavioursT P host (fxOf dynP 2) (intrOf dynP) (initT dynP 2 12) := by
  intro o ho
  rw [tk_beh] at ho
  exact ⟨_, ho, tk_fxt P host⟩

end Silmaril.Proofs.Wasm.FX.Examples.ThreadsT
