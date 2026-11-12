module

public import Silmaril.Wasm.SpecTec.Sim.Round7.RMRed.Defs

/-!
# Round 7, `BD`: `OpenRMRestDR` gives `OpenRMRestDC`, and the target

* `openRMRestDC_of_R`: at a spec profile, an injective encoding and a finite `HostOk` host,
  `OpenRMRestDR` gives `NullHost.OpenRMRestDC`. Each field splits on `Easy` (and `forward` also on
  `HCtx.CallCtxStep`); the proved cases are `HStep.forwardD_noMS`, `HCtx.forwardD_callCtx`,
  `HCasts.castsFwdD_noMS` and `HCasts.castsBwdD_noMS`.
* `wholeStepValidRM_of_restDR`: **`Round7.MemSimd.Task.wholeStepValidRM` from `OpenRMRestDR`**.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.RMRed

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)

variable {H : Type} {hn : H → String} {host : HostSemantics H}

/-- **`OpenRMRestDR` gives `NullHost.OpenRMRestDC`.** -/
theorem openRMRestDC_of_R {nd : Bool} {r : RelaxedChoice} (hinj : Function.Injective hn)
    (hf : HostFinite host) (hh : HostOk host) (O : OpenRMRestDR hn (Profile.spec nd r) host) :
    NullHost.OpenRMRestDC hn (Profile.spec nd r) host where
  forward c c' ts hc hb hsucc hx hs := by
    by_cases hE : Easy hn (Profile.spec nd r) host c
    · exact HStep.forwardD_noMS hinj hf hh hc hb hsucc hx hE.1 hE.2.1 hE.2.2 hs
    by_cases hH : HCtx.CallCtxStep (Profile.spec nd r) host c c'
    · exact HCtx.forwardD_callCtx hinj hf hh hc hb hsucc hH
    exact O.forward c c' ts hc hb hsucc hx hE hs hH
  restMSHC := O.restMSHC
  castsFwd c c' ts hc hb hsucc hx hs := by
    by_cases hE : Easy hn (Profile.spec nd r) host c
    · exact HCasts.castsFwdD_noMS hinj hf hh hc hb hsucc hx hE.1 hE.2.1 hE.2.2 hs
    exact O.castsFwd c c' ts hc hb hsucc hx hE hs
  castsBwd c ts w hc hb hx hs := by
    by_cases hE : Easy hn (Profile.spec nd r) host c
    · exact HCasts.castsBwdD_noMS hinj hf hh hc hb hx hE.1 hE.2.1 hE.2.2 hs
    exact O.castsBwd c ts w hc hb hx hE hs

/-- **`Round7.MemSimd.Task.wholeStepValidRM` from `OpenRMRestDR`.** -/
theorem wholeStepValidRM_of_restDR
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), OpenRMRestDR hn (Profile.spec nd r) host) :
    Round7.MemSimd.Task.wholeStepValidRM :=
  NullHost.wholeStepValidRM_of_restDC fun H hn hinj host hf hh nd r =>
    openRMRestDC_of_R hinj hf hh (h H hn hinj host hf hh nd r)

end Silmaril.Wasm.SpecTec.Sim.Round7.RMRed
