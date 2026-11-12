module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NullHost.Agree

/-!
# Round 7, memory SIMD: `RestMSH` at memory-SIMD-free sources, for every host

The per-rule backward obligations off memory SIMD and off `Step` 8 and 9 do not involve the
host: a rule other than 8 and 9 never calls `$hostcall` (`HAgree.relRulesUsers_step`), and round
6's primitives at two hosts agree off `$hostcall` (`agreeOff_host`). So they can be read at
`nullHost`, the host with no outcome:

* at `nullHost`, a Core step adds no memory SIMD code (`MSPres.step_noMemSimd`, the host
  condition holding vacuously), so a memory-SIMD-free configuration is in `VInv.NoMSDom`, where
  round 6's leaves give the obligations (`VInv.backwardUpToDRestS_noMSDom`);
* they move to the primitives at `host` off the host calls (`HAgree.backwardUpToDRestSH_agree`);
* a Core step at `nullHost` is a Core step at `host` (silmaril's `Step.of_noHost`).

`restSH_noMemSimd`: **the obligations hold at every `NoCastVM` configuration without memory SIMD
code, for every host**, with no successor condition. Hence `restMSH_of_restMSHC` and
`restMSH_iff_restMSHC`: `RMD.RestMSH` is `RestMSHC`, the obligations at configurations that
themselves hold memory SIMD code, with no host condition (round 7's `MSPres.restMS_iff_restMSC`
needed `HostKeepsMS`). `wholeStepValidRM_of_restDC` restates `RMD.wholeStepValidRM_of_restD` with
`OpenRMRestDC`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NullHost

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round6.MemSimd (NoMemSimd)
open Round7.MemSimd (NoCastVM)
open HAgree (BackwardUpToDRestSH)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

theorem nullHost_finite : HostFinite (nullHost (H := H)) :=
  fun _ _ _ => ⟨[], fun _ => by simp [nullHost]⟩

theorem nullHost_keepsMS : MSPres.HostKeepsMS (nullHost (H := H)) :=
  fun _ _ _ _ _ h => h.elim

/-- A smaller predicate keeps the obligations. -/
theorem restSH_mono {V W : Config H → Prop} {env : Env} (hVW : ∀ c, V c → W c)
    (h : BackwardUpToDRestSH W env hn P host) : BackwardUpToDRestSH V env hn P host where
  pure i s f is w hV hT hF := h.pure i s f is w (hVW _ hV) hT hF
  read i hi c w hV hT hF := h.read i hi c w (hVW _ hV) hT hF
  step i h6 hi h8 h9 c w hV hT hF := h.step i h6 hi h8 h9 c w (hVW _ hV) hT hF

/-- **Obligations with Core steps at `nullHost` give them at any host.** -/
theorem restSH_of_null {V : Config H → Prop} {env : Env}
    (h : BackwardUpToDRestSH V env hn P nullHost) : BackwardUpToDRestSH V env hn P host where
  pure i s f is w hV hT hF :=
    have ⟨is', js, hce, hw, hs⟩ := h.pure i s f is w hV hT hF
    ⟨is', js, hce, hw, Step.of_noHost host hs⟩
  read i hi c w hV hT hF :=
    have ⟨is', js, hce, hw, hs⟩ := h.read i hi c w hV hT hF
    ⟨is', js, hce, hw, Step.of_noHost host hs⟩
  step i h6 hi h8 h9 c w hV hT hF :=
    have ⟨c', d', hce, hw, hs⟩ := h.step i h6 hi h8 h9 c w hV hT hF
    ⟨c', d', hce, hw, Step.of_noHost host hs⟩

/-- A memory-SIMD-free configuration is in `NoMSDom` at `nullHost`. -/
theorem noMSDom_null {c : Config H} (hv : NoCastVM c) (hm : NoMemSimd c) :
    VInv.NoMSDom P nullHost c :=
  ⟨hv, hm, fun _ h => MSPres.step_noMemSimd nullHost_keepsMS h hm⟩

/-- **The obligations off memory SIMD and off the host calls hold at every memory-SIMD-free
`NoCastVM` configuration, for every host**, at round 6's primitives. -/
theorem restSH_noMemSimd (hinj : Function.Injective hn)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d) :
    BackwardUpToDRestSH (fun c => NoCastVM c ∧ NoMemSimd c) (simEnv (Prims.builtins P hn host))
      hn P host :=
  restSH_of_null <| restSH_mono (fun _ hc => noMSDom_null hc.1 hc.2) <|
    HAgree.backwardUpToDRestSH_agree (agreeOff_host P hn host nullHost) <|
      HAgree.restSH_of_restS <|
        VInv.backwardUpToDRestS_noMSDom hinj nullHost_finite hPs hPf

/-- **`RestMSH` from `RestMSHC`**, for every host. -/
theorem restMSH_of_restMSHC (hinj : Function.Injective hn)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    (h : RestMSHC hn P host) : RMD.RestMSH hn P host := by
  have N := restSH_noMemSimd (host := host) hinj hPs hPf
  refine ⟨fun i s f is w hV hT hF => ?_, fun i hi c w hV hT hF => ?_,
    fun i h6 hi h8 h9 c w hV hT hF => ?_⟩
  · by_cases hm : NoMemSimd ⟨s, f, is⟩
    · exact N.pure i s f is w ⟨hV.1, hm⟩ hT hF
    · exact h.pure i s f is w ⟨hV.1, hm⟩ hT hF
  · by_cases hm : NoMemSimd c
    · exact N.read i hi c w ⟨hV.1, hm⟩ hT hF
    · exact h.read i hi c w ⟨hV.1, hm⟩ hT hF
  · by_cases hm : NoMemSimd c
    · exact N.step i h6 hi h8 h9 c w ⟨hV.1, hm⟩ hT hF
    · exact h.step i h6 hi h8 h9 c w ⟨hV.1, hm⟩ hT hF

/-- `RestMSH` gives `RestMSHC`: a configuration with memory SIMD code is outside `NoMSDom`. -/
theorem restMSHC_of_restMSH (h : RMD.RestMSH hn P host) : RestMSHC hn P host :=
  restSH_mono (fun _ hc => ⟨hc.1, fun hd => hc.2 hd.2.1⟩) h

/-- **`RestMSH` is `RestMSHC`**, for every host. -/
theorem restMSH_iff_restMSHC (hinj : Function.Injective hn)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d) :
    RMD.RestMSH hn P host ↔ RestMSHC hn P host :=
  ⟨restMSHC_of_restMSH, restMSH_of_restMSHC hinj hPs hPf⟩

/-- Round 7's `MSPres.RestMSC` gives `RestMSHC`, with no host condition. -/
theorem restMSHC_of_restMSC (h : MSPres.RestMSC hn P host) : RestMSHC hn P host :=
  HAgree.restSH_of_restS h

/-- `OpenRMRestDC` gives `RMD.OpenRMRestD`. -/
theorem openRMRestD_of_DC (hinj : Function.Injective hn)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    (O : OpenRMRestDC hn P host) : RMD.OpenRMRestD hn P host :=
  ⟨O.forward, restMSH_of_restMSHC hinj hPs hPf O.restMSHC, O.castsFwd, O.castsBwd⟩

/-- **`Round7.Task.wholeStepValidRM` from `OpenRMRestDC`.** -/
theorem wholeStepValidRM_of_restDC
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), OpenRMRestDC hn (Profile.spec nd r) host) :
    Round7.MemSimd.Task.wholeStepValidRM :=
  RMD.wholeStepValidRM_of_restD fun H hn hinj host hfin hok nd r =>
    openRMRestD_of_DC hinj (Round5.BwdStep.growMaySucceed_spec nd r) (fun _ _ _ _ => trivial)
      (h H hn hinj host hfin hok nd r)

end Silmaril.Wasm.SpecTec.Sim.Round7.NullHost
