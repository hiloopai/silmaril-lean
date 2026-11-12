module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VInv.Rest

/-!
# Round 7, memory SIMD: the target from `OpenRMRestMS`

`openRMRest_of_MS`: `MemSimd.OpenRMRest` follows from `OpenRMRestMS`, whose backward field is only
`RestMS` (the obligations where memory SIMD code occurs), since `rest` holds on `NoMSDom`
(`rest_of_restMS`). `wholeStepValidRM_of_restMS`: the frozen `Round7.Task.wholeStepValidRM`
from `OpenRMRestMS` at every injective encoding, finite `HostOk` host and spec profile. A
reduction: no field of `OpenRMRestMS` is proved here.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VInv

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)

variable {H : Type}

/-- **`OpenRMRest` from `OpenRMRestMS`.** -/
theorem openRMRest_of_MS {hn : H → String} {P : Profile} {host : HostSemantics H}
    (hinj : Function.Injective hn) (hf : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    (O : OpenRMRestMS hn P host) : Round7.MemSimd.OpenRMRest hn P host where
  forward := O.forward
  rest := rest_of_restMS hinj hf hPs hPf O.restMS
  castsFwd := O.castsFwd
  castsBwd := O.castsBwd

/-- **`Round7.Task.wholeStepValidRM` from `OpenRMRestMS`.** -/
theorem wholeStepValidRM_of_restMS
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), OpenRMRestMS hn (Profile.spec nd r) host) :
    Round7.MemSimd.Task.wholeStepValidRM :=
  Round7.MemSimd.wholeStepValidRM_of_rest fun H hn hinj host hfin hok nd r =>
    openRMRest_of_MS hinj hfin (Round5.BwdStep.growMaySucceed_spec nd r) (fun _ _ _ _ => trivial)
      (h H hn hinj host hfin hok nd r)

end Silmaril.Wasm.SpecTec.Sim.Round7.VInv
