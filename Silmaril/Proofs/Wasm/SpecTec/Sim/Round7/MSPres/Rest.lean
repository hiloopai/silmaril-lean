module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSPres.Step

/-!
# Round 7, memory SIMD: `RestMS` for a host that adds no memory SIMD code

With `step_noMemSimd`, `NoMSDom`'s successor condition follows from `NoMemSimd` of the source
(`noMSDom_of_noMemSimd`). So for a host that adds no memory SIMD code:

* `restMS_iff_restMSC`: round 7's `RestMS` is `RestMSC`, the per-rule obligations at the
  `NoCastVM` configurations that themselves contain memory SIMD code (one direction,
  `restMSC_of_restMS`, holds for every host);
* `rest_of_restMSC`: `OpenRMRest.rest` (at `BM`) follows from `RestMSC`;
* `wholeStepValidRMNoMSH_backend`: round 7's memory-SIMD-free restriction of the target holds with
  the successor condition `NoMemSimd c₁` dropped.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSPres

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim
open Round6.MemSimd (NoMemSimd)
open Round7.MemSimd (NoCastVM BackwardUpToDRestS)
open Round7.VInv (NoMSDom RestMS backwardUpToDRestS_mono)
open Round7.MSPres (HostKeepsMS RestMSC WholeStepValidRMNoMSH)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **`NoMSDom` from `NoMemSimd`** for a host that adds no memory SIMD code. -/
theorem noMSDom_of_noMemSimd (hh : HostKeepsMS host) {c : Config H} (hv : NoCastVM c)
    (hm : NoMemSimd c) : NoMSDom P host c :=
  ⟨hv, hm, fun _ h => step_noMemSimd hh h hm⟩

/-- `RestMS` gives `RestMSC`, for every host: `RestMSC`'s domain is the smaller one. -/
theorem restMSC_of_restMS (h : RestMS hn P host) : RestMSC hn P host :=
  backwardUpToDRestS_mono (fun _ hc => ⟨hc.1, fun hd => hc.2 hd.2.1⟩) h

/-- `RestMSC` gives `RestMS` for a host that adds no memory SIMD code. -/
theorem restMS_of_restMSC (hh : HostKeepsMS host) (h : RestMSC hn P host) : RestMS hn P host :=
  backwardUpToDRestS_mono (fun _ hc => ⟨hc.1, fun hm => hc.2 (noMSDom_of_noMemSimd hh hc.1 hm)⟩) h

/-- **`RestMS` is `RestMSC`** for a host that adds no memory SIMD code. -/
theorem restMS_iff_restMSC (hh : HostKeepsMS host) : RestMS hn P host ↔ RestMSC hn P host :=
  ⟨restMSC_of_restMS, restMS_of_restMSC hh⟩

/-- **`OpenRMRest.rest` from `RestMSC`**, for an injective encoding, a finite host that adds no
memory SIMD code and a profile in which growth may both succeed and fail. -/
theorem rest_of_restMSC (hinj : Function.Injective hn) (hf : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    (hh : HostKeepsMS host) (h : RestMSC hn P host) :
    BackwardUpToDRestS NoCastVM (simEnv (Round7.MemSimd.BM P hn host)) hn P host :=
  Round7.VInv.rest_of_restMS hinj hf hPs hPf (restMS_of_restMSC hh h)

/-- **The memory-SIMD-free restriction without the successor condition**, from round 7's
`wholeStepValidRMNoMS_backend` and `step_noMemSimd`. -/
theorem wholeStepValidRMNoMSH_backend : WholeStepValidRMNoMSH :=
  fun H hn hinj host hf hok hh nd r =>
    (Round7.MemSimd.wholeStepValidRMNoMS_backend H hn hinj host hf hok nd r).imp fun _ hB =>
      ⟨fun c c' ts hc hb hm hsucc hs =>
          hB.1 c c' ts hc hb hm (fun c₁ h₁ => ⟨hsucc c₁ h₁, step_noMemSimd hh h₁ hm⟩) hs,
        fun c ts w hc hb hm hs => hB.2 c ts w hc hb hm (fun _ h₁ => step_noMemSimd hh h₁ hm) hs⟩

end Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSPres
