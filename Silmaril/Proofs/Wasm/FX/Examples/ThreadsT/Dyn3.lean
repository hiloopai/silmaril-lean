module

public import Silmaril.Wasm.Models.FXTRun.Thms
public import Silmaril.Wasm.Models.FXLComp.Defs
public import Silmaril.Wasm.FX.Examples.Threads.Thms
public import Silmaril.Wasm.FX.Examples.ThreadsT.Defs

/-!
# The dynamic `run` under `StepFXT`, segment 3

Segment 3 of the dynamic `run` (`Silmaril.Wasm.FX.Examples.Threads.dynP`, function `9`) compiled
by `Silmaril.Wasm.Models.FXLComp`: 360 steps of the sound interpreter from `dynMid 3` reach
`dynMid 4` (`Silmaril.Wasm.FX.Examples.ThreadsT`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Examples.ThreadsT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FXT Silmaril.Wasm.Models.FXLComp
open Silmaril.Wasm.Models.FXTRun Silmaril.Proofs.Wasm.Models.FXTRun Silmaril.Wasm.FX.Examples.Threads
open Silmaril.Wasm.Models.FXL (beh Obs init)
open Silmaril.Wasm.FX.Examples.ThreadsT
open Silmaril.Wasm.Numerics (Profile)

/-- The checked segment 3. -/
theorem dyn_seg3_check :
    segT dynAr (fxOf dynP 2) (intrOf dynP) 40 360 (dynMid 3) (dynMid 4) = true := by
  decide +kernel

/-- **Segment 3 of the dynamic `run`** is a `StepFXT` run. -/
theorem dyn_seg3 (P : Profile) (host : HostSemantics Nat) :
    StepsT P host (fxOf dynP 2) (intrOf dynP) (dynMid 3) (dynMid 4) :=
  segT_steps dyn_seg3_check rfl rfl

end Silmaril.Proofs.Wasm.FX.Examples.ThreadsT
