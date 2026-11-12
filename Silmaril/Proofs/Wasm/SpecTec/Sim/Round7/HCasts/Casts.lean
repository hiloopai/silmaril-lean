module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.HCasts.StepB
public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Final.Thms

/-!
# Round 7, `BD`: the backend whole step between `BD` and `BI`, and the cast leaf at `BD` off
memory SIMD and `CALL_REF`

* `sstepB_bd_bi_iff`, `sstepB_bd_bm_iff`: on sources whose image has no memory SIMD atom and no
  `CALL_REF` (`VInv.NoAtoms hAtoms`), round 6's backend whole step reads alike at `BD` and round 6's
  `BI`, and at `BD` and `BM` (`sstepB_iff_h` with `HAgree.agreeOff_bd_bi`, `agreeOff_bd_bm`).
* `castsFwdD_noMS`, `castsBwdD_noMS`: **`RMD.OpenRMRestD.castsFwd` and `castsBwd` at
  memory-SIMD-free sources whose image has no `CALL_REF`**, when no Core successor has memory
  SIMD code, at every injective encoding, finite `HostOk` host and spec profile. Round 6's proved
  cast leaf at `BI` (`Round6.Int.openR_backend`, through `agreeTy_BI`) gives a backend step
  between `configV` images; they are `configVD` images, and the step moves to `BD`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HCasts

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round6.MemSimd (NoMemSimd)
open Round6.Target (CastRedex)
open Round6.Reading (SStepB)
open Round7.MemSimd (BoundedSelM configVD)
open Round7.HostD (BD)
open Round7.HStep (hAtoms)

variable {H : Type} {hn : H → String} {host : HostSemantics H}

/-- **The backend whole step reads alike at `BD` and round 6's `BI`** on sources without memory
SIMD atoms and `CALL_REF`. -/
theorem sstepB_bd_bi_iff {P : Profile} {c c' : Value} (hc : VInv.NoAtoms hAtoms c) :
    SStepB (simEnv (BD P hn host)) c c' ↔ SStepB (simEnv (Prims.builtins P hn host)) c c' :=
  sstepB_iff_h (HAgree.agreeOff_bd_bi P hn host) ⟨c, c', rfl, hc⟩

/-- **The backend whole step reads alike at `BD` and `BM`** on the same sources. -/
theorem sstepB_bd_bm_iff {P : Profile} {c c' : Value} (hc : VInv.NoAtoms hAtoms c) :
    SStepB (simEnv (BD P hn host)) c c' ↔ SStepB (simEnv (Round7.MemSimd.BM P hn host)) c c' :=
  sstepB_iff_h (HAgree.agreeOff_bd_bm P hn host) ⟨c, c', rfl, hc⟩

/-- **`castsFwd` at `BD`, at memory-SIMD-free sources whose image has no `CALL_REF`.** -/
theorem castsFwdD_noMS {nd : Bool} {r : RelaxedChoice} (hinj : Function.Injective hn)
    (hf : HostFinite host) (hh : HostOk host) {c c' : Config H} {ts : List CValType}
    (hc : ConfigOk c ts) (hb : BoundedSelM c)
    (hsucc : ∀ c₁, Step (Profile.spec nd r) host c c₁ → BoundedSelM c₁) (hx : CastRedex c.code)
    (hm : NoMemSimd c) (hms : ∀ c₁, Step (Profile.spec nd r) host c c₁ → NoMemSimd c₁)
    (hA : VInv.NoAtoms hAtoms (configV hn c)) (hs : Step (Profile.spec nd r) host c c') :
    ∃ d', Bwd.ConfigEq c' d' ∧
      Round6.Int.backend.step (BD (Profile.spec nd r) hn host) (configVD hn c) (configVD hn d') := by
  have O := Round6.Int.openR_backend (hn := hn) (host := host) (nd := nd) (r := r) hinj hf hh
  have hT := VInv.typed_of_typedD hm
    (Round7.MemSimd.typedD_of_configOk_selM (Prims.builtins (Profile.spec nd r) hn host) hn hc hb)
  obtain ⟨d', ⟨hd', -⟩, hst⟩ := O.casts.fwd c c c' ts hc
    (Round7.MemSimd.boundedSel_of_boundedSelM hb hm)
    (fun c₁ h₁ => Round7.MemSimd.boundedSel_of_boundedSelM (hsucc c₁ h₁) (hms c₁ h₁))
    ⟨Bwd.ConfigEq.refl c, hT⟩ hx hs
  refine ⟨d', hd', ?_⟩
  rw [Round7.MemSimd.configVD_eq_of_noMemSimd hn hm,
    Round7.MemSimd.configVD_eq_of_noMemSimd hn (VInv.noMemSimd_of_configEq hd' (hms _ hs))]
  exact (sstepB_bd_bi_iff hA).2 hst

/-- **`castsBwd` at `BD`, at memory-SIMD-free sources whose image has no `CALL_REF`.** -/
theorem castsBwdD_noMS {nd : Bool} {r : RelaxedChoice} (hinj : Function.Injective hn)
    (hf : HostFinite host) (hh : HostOk host) {c : Config H} {ts : List CValType} {w : Value}
    (hc : ConfigOk c ts) (hb : BoundedSelM c) (hx : CastRedex c.code) (hm : NoMemSimd c)
    (hms : ∀ c₁, Step (Profile.spec nd r) host c c₁ → NoMemSimd c₁)
    (hA : VInv.NoAtoms hAtoms (configV hn c))
    (hs : Round6.Int.backend.step (BD (Profile.spec nd r) hn host) (configVD hn c) w) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step (Profile.spec nd r) host c c' := by
  have O := Round6.Int.openR_backend (hn := hn) (host := host) (nd := nd) (r := r) hinj hf hh
  have hT := VInv.typed_of_typedD hm
    (Round7.MemSimd.typedD_of_configOk_selM (Prims.builtins (Profile.spec nd r) hn host) hn hc hb)
  rw [Round7.MemSimd.configVD_eq_of_noMemSimd hn hm] at hs
  have hs' : SStepB (simEnv (Prims.builtins (Profile.spec nd r) hn host)) (configV hn c) w :=
    (sstepB_bd_bi_iff hA).1 hs
  obtain ⟨c', d', hd', -, hw, hst⟩ := O.casts.bwd c c ts w hc
    (Round7.MemSimd.boundedSel_of_boundedSelM hb hm) ⟨Bwd.ConfigEq.refl c, hT⟩ hx hs'
  refine ⟨c', d', hd', ?_, hst⟩
  rw [hw, Round7.MemSimd.configVD_eq_of_noMemSimd hn (VInv.noMemSimd_of_configEq hd' (hms _ hst))]

end Silmaril.Wasm.SpecTec.Sim.Round7.HCasts
