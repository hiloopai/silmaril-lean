module

public import Silmaril.Wasm.SpecTec.Sim.Round9.RMPure.Defs
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.RMPure.Counted

/-!
# Round 9, rm: every `Step_pure` rule at memory SIMD code

The 15 rules of `RMAtom.structPure` hold backward at `adminsToVD` in every `simEnv B`
(`Raw/…/Round9/RMPure/{Exits,Branch,Counted}`); with the 64 flat rules, which cannot fire there
(`RMAtom.pure_adminsMS`), the `Step_pure` obligation of `RMAtom.RestMSHCH` is discharged:
`restMSHCH_of_I`, `wholeStepValidRM_of_restDPI`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMPure

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round7.MemSimd (adminsToVD)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **Every rule of `RMAtom.structPure` holds backward at `adminsToVD`**, in every `simEnv B`,
at every code (memory SIMD instructions included) and with no typing hypothesis. -/
theorem pure_struct (B : Builtins) : ∀ i ∈ RMAtom.structPure, LeafD B P host i := by
  intro i hi
  simp only [RMAtom.structPure, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  exacts [bwdD_ifTrue B, bwdD_ifFalse B, bwdD_labelVals B, bwdD_brLabelZero B,
    bwdD_brLabelSucc B, bwdD_brHandler B, bwdD_frameVals B, bwdD_returnFrame B,
    bwdD_returnLabel B, bwdD_returnHandler B, bwdD_handlerVals B, bwdD_trapInstrs B,
    bwdD_trapLabel B, bwdD_trapHandler B, bwdD_trapFrame B]

variable {hn : H → String}

/-- **`RestMSHCI` gives `RMAtom.RestMSHCH`**: its `pure` field by `pure_struct`. -/
theorem restMSHCH_of_I (h : RestMSHCI hn P host) : RMAtom.RestMSHCH hn P host where
  pure := by
    intro i hi s f is w _ _ _ hf
    obtain ⟨is', hw, hs⟩ := pure_struct (Prims.builtins P hn host) i hi s f is w hf
    exact ⟨is', is', Bwd.CodeEq.refl is', hw, hs⟩
  read := h.read
  firesRead := h.firesRead

/-- **`OpenRMRestDPI` gives `RMAtom.OpenRMRestDPH`.** -/
theorem openRMRestDPH_of_I (O : OpenRMRestDPI hn P host) : RMAtom.OpenRMRestDPH hn P host :=
  ⟨O.forward, restMSHCH_of_I O.restMSHC, O.castsFwd, O.castsBwd⟩

/-- **`Round7.MemSimd.Task.wholeStepValidRM` from `OpenRMRestDPI`.** -/
theorem wholeStepValidRM_of_restDPI
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice),
          OpenRMRestDPI hn (Profile.spec nd r) host) :
    Round7.MemSimd.Task.wholeStepValidRM :=
  RMAtom.wholeStepValidRM_of_restDPH fun H hn hinj host hf hh nd r =>
    openRMRestDPH_of_I (h H hn hinj host hf hh nd r)

end Silmaril.Wasm.SpecTec.Sim.Round9.RMPure
