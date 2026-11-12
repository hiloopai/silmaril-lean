module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.RMD.MSD

/-!
# Round 7, `BD`: `Round7.Task.wholeStepValidRM` from `OpenRMRestD`

* `restD_of_restMSH`: the per-rule backward obligations off memory SIMD at `BD`
  (`MemSimd.BackwardUpToDRestS NoCastVM (simEnv BD)`, host calls included) follow from `RestMSH`:
  - on `VInv.NoMSDom`, round 6's leaves at `BI` (`VInv.backwardUpToDRestS_noMSDom`);
  - outside it, `RestMSH`;
  - both move from `BI` to `BD` off the host calls (`HAgree.backwardUpToDRestSH_agree`), and the
    host calls `Step` 8 and 9 are `HostRulesD.hostStepsD`.
* `fwdRMD_of_open`, `bwdRMD_of_open`: the two halves of the frozen target at `B := BD`.
* **`wholeStepValidRM_of_restD`**: `Round7.MemSimd.Task.wholeStepValidRM` from `OpenRMRestD` at
  every injective encoding, finite `HostOk` host and spec profile. It is a reduction: `forward`,
  `restMSH`, `castsFwd` and `castsBwd` are not proved here.
* `restMSH_of_restMS`, `restMSH_of_restMSC`: `RestMSH` is implied by round 7's `VInv.RestMS`, and
  by `MSPres.RestMSC` for a host that adds no memory SIMD code; so `OpenRMRestD` asks no more of
  the backward half than `VInv.OpenRMRestMS` does.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.RMD

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round7.MemSimd (NoCastVM BoundedSelM configVD BackwardUpToDRestS BwdUpToD stepMSRules
  noCastVM_closed noCastVM_entry typedD_of_configOk_selM transferD_backend)
open Round7.HostD (BD)
open Round6.Target (CastRedex)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## The backward obligations at `BD` -/

/-- `RestMSH` together with round 6's leaves on `NoMSDom`, at `BI`, off the host calls. -/
theorem restSH_bi (hinj : Function.Injective hn) (hf : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    (h : RestMSH hn P host) :
    HAgree.BackwardUpToDRestSH NoCastVM (simEnv (Prims.builtins P hn host)) hn P host := by
  have N := HAgree.restSH_of_restS (VInv.backwardUpToDRestS_noMSDom hinj hf hPs hPf)
  refine ⟨fun i s f is w hV hT hF => ?_, fun i hi c w hV hT hF => ?_,
    fun i h6 hi h8 h9 c w hV hT hF => ?_⟩
  · by_cases hW : VInv.NoMSDom P host ⟨s, f, is⟩
    · exact N.pure i s f is w hW hT hF
    · exact h.pure i s f is w ⟨hV, hW⟩ hT hF
  · by_cases hW : VInv.NoMSDom P host c
    · exact N.read i hi c w hW hT hF
    · exact h.read i hi c w ⟨hV, hW⟩ hT hF
  · by_cases hW : VInv.NoMSDom P host c
    · exact N.step i h6 hi h8 h9 c w hW hT hF
    · exact h.step i h6 hi h8 h9 c w ⟨hV, hW⟩ hT hF

/-- **The per-rule backward obligations off memory SIMD at `BD`, from `RestMSH`.** The host calls
(`Step` 8 and 9) are `HostRulesD.hostStepsD`; every other rule moves from `BI`. -/
theorem restD_of_restMSH (hinj : Function.Injective hn) (hf : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    (h : RestMSH hn P host) :
    BackwardUpToDRestS NoCastVM (simEnv (BD P hn host)) hn P host := by
  have S := HAgree.backwardUpToDRestSH_agree (HAgree.agreeOff_bd_bi P hn host)
    (restSH_bi hinj hf hPs hPf h)
  refine ⟨S.pure, S.read, fun i h6 hi c w hV hT hF => ?_⟩
  by_cases h89 : i = 8 ∨ i = 9
  · exact HostRulesD.hostStepsD hinj hf (by rcases h89 with rfl | rfl <;> decide) c w hT hF
  · exact S.step i h6 hi (fun h => h89 (.inl h)) (fun h => h89 (.inr h)) c w hV hT hF

/-! ## The two halves at `BD` -/

/-- **The forward half of the round-7 target at `BD`, from `OpenRMRestD`.** -/
theorem fwdRMD_of_open (O : OpenRMRestD hn P host) (c c' : Config H) (ts : List CValType)
    (hc : ConfigOk c ts) (hb : BoundedSelM c) (hsucc : ∀ c₁, Step P host c c₁ → BoundedSelM c₁)
    (hs : Step P host c c') :
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧
        Round6.Int.backend.step (BD P hn host) (configVD hn c) (configVD hn d') := by
  by_cases hx : CastRedex c.code
  · obtain ⟨d', hd', hst⟩ := O.castsFwd c c' ts hc hb hsucc hx hs
    exact ⟨c', hs, fun _ => rfl, d', hd', hst⟩
  · obtain ⟨c'', hs'', hu, d', hd', hst⟩ := O.forward c c' ts hc hb hsucc hx hs
    exact ⟨c'', hs'', hu, d', hd', (transferD_backend _ hn hx _).2 hst⟩

/-- **The backward half of the round-7 target at `BD`, from `OpenRMRestD`.** -/
theorem bwdRMD_of_open (O : OpenRMRestD hn P host) (hinj : Function.Injective hn)
    (hf : HostFinite host) (hPs : ∀ k a n d, P.growMaySucceed k a n d)
    (hPf : ∀ k a n d, P.growMayFail k a n d) (c : Config H) (ts : List CValType) (w : Value)
    (hc : ConfigOk c ts) (hb : BoundedSelM c)
    (hs : Round6.Int.backend.step (BD P hn host) (configVD hn c) w) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step P host c c' := by
  by_cases hx : CastRedex c.code
  · exact O.castsBwd c ts w hc hb hx hs
  · exact backward_upToD_restSD noCastVM_closed (restD_of_restMSH hinj hf hPs hPf O.restMSH) c w
      (noCastVM_entry c ts hc hb hx) (typedD_of_configOk_selM _ hn hc hb)
      ((transferD_backend _ hn hx w).1 hs)

/-- **`Round7.Task.wholeStepValidRM` from `OpenRMRestD`**: the frozen round-7 target holds, with
`B := BD`, as soon as the forward half and the cast leaf at `BD` and the obligations `RestMSH`
hold at every injective encoding, finite `HostOk` host and spec profile. -/
theorem wholeStepValidRM_of_restD
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), OpenRMRestD hn (Profile.spec nd r) host) :
    Round7.MemSimd.Task.wholeStepValidRM := fun H hn hinj host hfin hok nd r =>
  have O := h H hn hinj host hfin hok nd r
  ⟨BD (Profile.spec nd r) hn host,
    fun c c' ts hc hb hsucc hs => fwdRMD_of_open O c c' ts hc hb hsucc hs,
    fun c ts w hc hb hs => bwdRMD_of_open O hinj hfin (Round5.BwdStep.growMaySucceed_spec nd r)
      (fun _ _ _ _ => trivial) c ts w hc hb hs⟩

/-! ## `RestMSH` is weaker than round 7's `RestMS` -/

/-- **`RestMS` gives `RestMSH`.** -/
theorem restMSH_of_restMS (h : VInv.RestMS hn P host) : RestMSH hn P host :=
  HAgree.restSH_of_restS h

/-- **`RestMSC` gives `RestMSH`** for a host that adds no memory SIMD code. -/
theorem restMSH_of_restMSC (hh : MSPres.HostKeepsMS host) (h : MSPres.RestMSC hn P host) :
    RestMSH hn P host :=
  restMSH_of_restMS ((MSPres.restMS_iff_restMSC hh).2 h)

end Silmaril.Wasm.SpecTec.Sim.Round7.RMD
