module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.RMCode.Rules

/-!
# Round 8, memory SIMD: the reduction to `OpenRMRestDPQ`

`RestMSHCQ` gives round 8 pass 1's `RMHost.RestMSHCP` at every profile in which growth may both
succeed and fail: at memory-SIMD-free code, the `Step_read` and `Step` obligations come from
`FiresEraseD` (`read_of_firesErase`, `step_of_firesErase`); `Step` rule 7 and code holding memory
SIMD instructions are asked as before. So `Round7.MemSimd.Task.wholeStepValidRM` follows from
`OpenRMRestDPQ` (`wholeStepValidRM_of_restDPQ`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.RMCode

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round6.MemSimd (AdminsMS)

variable {H : Type} {hn : H → String} {P : Profile}

/-- **`RestMSHCQ` gives `RMHost.RestMSHCP`.** -/
theorem restMSHCP_of_Q {host : HostSemantics H}
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    (h : RestMSHCQ hn P host) : RMHost.RestMSHCP hn P host where
  pure := h.pure
  read i hi c w hV hT hF := by
    by_cases hms : AdminsMS c.code
    · exact read_of_firesErase hPs hPf hi (h.firesRead i hi) c w hms hV hT hF
    · exact h.read i hi c w hms hV hT hF
  step i h6 hmsr h8 h9 c w hV hT hF := by
    by_cases h7 : i = 7
    · exact h.step i h6 hmsr h8 h9 c w (.inr h7) hV hT hF
    by_cases hms : AdminsMS c.code
    · exact step_of_firesErase hPs hPf h6 hmsr h8 h9 (h.firesStep i h6 hmsr h7 h8 h9) c w hms hV
        hT hF
    · exact h.step i h6 hmsr h8 h9 c w (.inl hms) hV hT hF

/-- **`OpenRMRestDPQ` gives `RMHost.OpenRMRestDPP`.** -/
theorem openRMRestDPP_of_Q {host : HostSemantics H}
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    (O : OpenRMRestDPQ hn P host) : RMHost.OpenRMRestDPP hn P host :=
  ⟨O.forward, restMSHCP_of_Q hPs hPf O.restMSHC, O.castsFwd, O.castsBwd⟩

/-- **`Round7.MemSimd.Task.wholeStepValidRM` from `OpenRMRestDPQ`.** -/
theorem wholeStepValidRM_of_restDPQ
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice),
          OpenRMRestDPQ hn (Profile.spec nd r) host) :
    Round7.MemSimd.Task.wholeStepValidRM :=
  RMHost.wholeStepValidRM_of_restDPP fun H hn hinj host hf hh nd r =>
    openRMRestDPP_of_Q (Round5.BwdStep.growMaySucceed_spec nd r) (fun _ _ _ _ => trivial)
      (h H hn hinj host hf hh nd r)

end Silmaril.Wasm.SpecTec.Sim.Round8.RMCode
