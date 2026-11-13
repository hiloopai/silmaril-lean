module

public import Silmaril.Wasm.Models.FXTRun.Thms
public import Silmaril.Wasm.Models.FXLComp.Defs
public import Silmaril.Wasm.FX.Examples.Threads.Thms

/-!
# The sync scheduler alone under `StepFXT`

The explainer's scheduler `sync` (forking enqueues the new thread, yielding carries on), run alone on `cont.new $main` (function `10` of
`Silmaril.Wasm.FX.Examples.Threads.dynP`) and compiled by `Silmaril.Wasm.Models.FXLComp`, prints its
block of the documented output under `StepFXT`: `sync_fxt`, `sync_sim`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Examples.ThreadsT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FXT Silmaril.Wasm.Models.FXLComp
open Silmaril.Wasm.Models.FXTRun Silmaril.Proofs.Wasm.Models.FXTRun Silmaril.Wasm.FX.Examples.Threads
open Silmaril.Wasm.Models.FXL (beh Obs init)
open Silmaril.Wasm.Numerics (Profile)

/-- The computed `StepFXT` run of the compiled `sync` example ends with its log. -/
theorem sync_check :
    checkT dynAr (fxOf dynP 2) (intrOf dynP) 40 400 (initT dynP 2 10) (logV syncLog) = true := by
  decide +kernel

/-- **The compiled `sync` example prints its documented output under `StepFXT`**, at every
profile and host. -/
theorem sync_fxt (P : Profile) (host : HostSemantics Nat) :
    ObsT.ret (logV syncLog) (.returns []) ∈
      behavioursT P host (fxOf dynP 2) (intrOf dynP) (initT dynP 2 10) :=
  checkT_mem sync_check

/-- **The `StepFXL` behaviour of `sync` is a `StepFXT` behaviour of its compilation**
(read through `logV`). -/
theorem sync_sim (P : Profile) (host : HostSemantics Nat) :
    ∀ o ∈ beh dynP dynAr (init dynP 10), ∃ l, o = Obs.done l [] ∧
      ObsT.ret (logV l) (.returns []) ∈
        behavioursT P host (fxOf dynP 2) (intrOf dynP) (initT dynP 2 10) := by
  intro o ho
  rw [sync_beh] at ho
  exact ⟨_, ho, sync_fxt P host⟩

end Silmaril.Proofs.Wasm.FX.Examples.ThreadsT
