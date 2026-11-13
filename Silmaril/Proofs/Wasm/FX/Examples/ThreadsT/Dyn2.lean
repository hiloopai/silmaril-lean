module

public import Silmaril.Wasm.Models.FXTRun.Thms
public import Silmaril.Wasm.Models.FXLComp.Defs
public import Silmaril.Wasm.FX.Examples.Threads.Thms
public import Silmaril.Wasm.FX.Examples.ThreadsT.Defs

/-!
# The dynamic `run` under `StepFXT`, segment 2

Segment 2 of the dynamic `run` (`Silmaril.Wasm.FX.Examples.Threads.dynP`, function `9`) compiled
by `Silmaril.Wasm.Models.FXLComp`: 348 steps of the sound interpreter from `dynMid 2` reach
`dynMid 3` (`Silmaril.Wasm.FX.Examples.ThreadsT`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Examples.ThreadsT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FXT Silmaril.Wasm.Models.FXLComp
open Silmaril.Wasm.Models.FXTRun Silmaril.Proofs.Wasm.Models.FXTRun Silmaril.Wasm.FX.Examples.Threads
open Silmaril.Wasm.Models.FXL (beh Obs init)
open Silmaril.Wasm.FX.Examples.ThreadsT
open Silmaril.Wasm.Numerics (Profile)

/-- The checked segment 2. -/
theorem dyn_seg2_check :
    segT dynAr (fxOf dynP 2) (intrOf dynP) 40 348 (dynMid 2) (dynMid 3) = true := by
  decide +kernel

/-- **Segment 2 of the dynamic `run`** is a `StepFXT` run. -/
theorem dyn_seg2 (P : Profile) (host : HostSemantics Nat) :
    StepsT P host (fxOf dynP 2) (intrOf dynP) (dynMid 2) (dynMid 3) :=
  segT_steps dyn_seg2_check rfl rfl

end Silmaril.Proofs.Wasm.FX.Examples.ThreadsT
