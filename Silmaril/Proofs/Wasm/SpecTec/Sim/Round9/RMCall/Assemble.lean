module

public import Silmaril.Wasm.SpecTec.Sim.Round9.RMCall.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.RMCall.Rule7
public import Silmaril.Wasm.SpecTec.Sim.Round8.FiresC.Thms

/-!
# Round 9, rm: the reduction without `Step` rule 7

`bwd_callRefFuncD_builtins` discharges rule 7 of `FiresC.RestMSHCF.step` at every configuration,
so `RestMSHCF` follows from `RestMSHCG` and `Round7.MemSimd.Task.wholeStepValidRM` from
`OpenRMRestDPG`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMCall

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **`RestMSHCG` gives `FiresC.RestMSHCF`**: rule 7 by `bwd_callRefFuncD_builtins`, the other
rules from `RestMSHCG.step` (which `RestMSHCF` asks for only at code holding memory SIMD, or at
rule 7). -/
theorem restMSHCF_of_G (h : RestMSHCG hn P host) : Round8.FiresC.RestMSHCF hn P host where
  pure := h.pure
  read := h.read
  step := by
    intro i h6 hms h8 h9 c w hor hv ht hf
    by_cases h7 : i = 7
    · subst h7
      exact bwd_callRefFuncD_builtins c w hf
    · have hcode : ¬ Round6.MemSimd.AdminsMS c.code := hor.resolve_right h7
      exact h.step i h6 hms h7 h8 h9 c w hcode hv ht hf
  firesRead := h.firesRead

/-- **`OpenRMRestDPG` gives `FiresC.OpenRMRestDPF`.** -/
theorem openRMRestDPF_of_G (O : OpenRMRestDPG hn P host) : Round8.FiresC.OpenRMRestDPF hn P host :=
  ⟨O.forward, restMSHCF_of_G O.restMSHC, O.castsFwd, O.castsBwd⟩

/-- **`Round7.MemSimd.Task.wholeStepValidRM` from `OpenRMRestDPG`.** -/
theorem wholeStepValidRM_of_restDPG
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice),
          OpenRMRestDPG hn (Profile.spec nd r) host) :
    Round7.MemSimd.Task.wholeStepValidRM :=
  Round8.FiresC.wholeStepValidRM_of_restDPF fun H hn hinj host hf hh nd r =>
    openRMRestDPF_of_G (h H hn hinj host hf hh nd r)

end Silmaril.Wasm.SpecTec.Sim.Round9.RMCall
