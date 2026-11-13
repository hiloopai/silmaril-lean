module

public import Silmaril.Wasm.Models.FXTRun.Thms
public import Silmaril.Wasm.Models.FXLComp.Defs
public import Silmaril.Wasm.FX.Examples.Threads.Thms
public import Silmaril.Wasm.FX.Examples.ThreadsT.Defs
public import Silmaril.Proofs.Wasm.FX.Examples.ThreadsT.Dyn0
public import Silmaril.Proofs.Wasm.FX.Examples.ThreadsT.Dyn1
public import Silmaril.Proofs.Wasm.FX.Examples.ThreadsT.Dyn2
public import Silmaril.Proofs.Wasm.FX.Examples.ThreadsT.Dyn3

/-!
# The dynamic lightweight threads (full `run`) under `StepFXT`

The explainer's dynamic `run` (`Silmaril.Wasm.FX.Examples.Threads.dynP`, function `9`: the five
schedulers in sequence), compiled by `Silmaril.Wasm.Models.FXLComp`, prints the documented output
under `StepFXT`: `dyn_fxt`, `dyn_sim`. The run is checked in five segments: four to the
checkpoints `dynMid 1` … `dynMid 4` (modules `Dyn0` … `Dyn3`), and the last one here.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Examples.ThreadsT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FXT Silmaril.Wasm.Models.FXLComp
open Silmaril.Wasm.Models.FXTRun Silmaril.Proofs.Wasm.Models.FXTRun Silmaril.Wasm.FX.Examples.Threads
open Silmaril.Wasm.Models.FXL (beh Obs init)
open Silmaril.Wasm.FX.Examples.ThreadsT
open Silmaril.Wasm.Numerics (Profile)

/-- The checked last segment: from `dynMid 4` the run ends with the whole log. -/
theorem dyn_last_check :
    checkT dynAr (fxOf dynP 2) (intrOf dynP) 40 400 (dynMid 4) (logV dynLog) = true := by
  decide +kernel

/-- **The compiled `dyn` example prints its documented output under `StepFXT`**, at every
profile and host. -/
theorem dyn_fxt (P : Profile) (host : HostSemantics Nat) :
    ObsT.ret (logV dynLog) (.returns []) ∈
      behavioursT P host (fxOf dynP 2) (intrOf dynP) (initT dynP 2 9) :=
  mem_of_stepsT
    (((dyn_seg0 P host).trans (dyn_seg1 P host)).trans ((dyn_seg2 P host).trans (dyn_seg3 P host)))
    (checkT_mem dyn_last_check)

/-- **The `StepFXL` behaviour of `dyn` is a `StepFXT` behaviour of its compilation**
(read through `logV`). -/
theorem dyn_sim (P : Profile) (host : HostSemantics Nat) :
    ∀ o ∈ beh dynP dynAr (init dynP 9), ∃ l, o = Obs.done l [] ∧
      ObsT.ret (logV l) (.returns []) ∈
        behavioursT P host (fxOf dynP 2) (intrOf dynP) (initT dynP 2 9) := by
  intro o ho
  rw [dyn_beh] at ho
  exact ⟨_, ho, dyn_fxt P host⟩

end Silmaril.Proofs.Wasm.FX.Examples.ThreadsT
