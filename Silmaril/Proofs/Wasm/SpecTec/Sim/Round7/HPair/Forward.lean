module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HPair.Inv
public import Silmaril.Wasm.SpecTec.Sim.Round7.RMRed.Thms

/-!
# Round 7, `BD`: `forward` and the casts at sources with `CALL_REF`, and the narrowed reduction

* `sstep_bd_bi_iff_p`, `sstepB_bd_bi_iff_p`: on sources without memory SIMD atoms whose lists
  have no `REF.FUNC_ADDR` followed by `CALL_REF` (`NoPair`), the whole step (declarative and
  backend) reads alike at `BD` and round 6's `BI`.
* `forwardD_p`, `castsFwdD_p`, `castsBwdD_p`: **`forward` and the casts at `EasyP` sources**:
  `HStep.forwardD_noMS`, `HCasts.castsFwdD_noMS`, `castsBwdD_noMS` with `NoPair` for the absence of
  `CALL_REF`. The memory SIMD part of the old hypothesis comes from `MSAtoms.noAtoms_ms_configV`.
* `noPair_of_noAtoms`, `easyP_of_easy`: `EasyP` contains `RMRed.Easy`. `call_ref` code that is not
  right after a function reference (for example `local.get 0; call_ref`), and `call_ref` in
  function bodies and block bodies, are `EasyP` but not `Easy`.
* `openRMRestDR_of_P`, `wholeStepValidRM_of_restDP`: **`Round7.MemSimd.Task.wholeStepValidRM`
  from `OpenRMRestDP`**.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HPair

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
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
open VInv (NoAtoms NoAtomsL NoAtomsF msAtoms)

variable {H : Type} {hn : H → String} {host : HostSemantics H}

/-! ## `NoAtoms` with `CALL_REF` gives `NoPair` -/

theorem pairFree_of_noCall {A : List MixopS} (hA : "CALL_REF" ∈ A) :
    ∀ {vs : List Value}, NoAtomsL A vs → PairFreeL vs
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: vs, h => by
    refine ⟨?_, pairFree_of_noCall hA h.2⟩
    have hb : NoAtoms A b := h.2.1
    rcases a with _ | _ | _ | _ | ⟨x, _⟩ | _ | _ | _ <;> rcases b with _ | _ | _ | _ | ⟨y, _⟩ | _ | _ | _ <;>
      simp only [pairAt]
    have hy : y ∉ A := hb.1
    by_cases hyc : y = "CALL_REF"
    · exact absurd (hyc ▸ hA) hy
    · simp [hyc]

mutual
theorem noPair_of_noAtoms {A : List MixopS} (hA : "CALL_REF" ∈ A) :
    ∀ v : Value, NoAtoms A v → NoPair v
  | .bool _, _ => trivial
  | .num _, _ => trivial
  | .text _, _ => trivial
  | .tuple vs, h => noPairL_of_noAtoms hA vs h
  | .case _ w, h => noPair_of_noAtoms hA w h.2
  | .struct gs, h => noPairF_of_noAtoms hA gs h
  | .list vs, h => ⟨pairFree_of_noCall hA h, noPairL_of_noAtoms hA vs h⟩
  | .opt none, _ => trivial
  | .opt (some w), h => noPair_of_noAtoms hA w h

theorem noPairL_of_noAtoms {A : List MixopS} (hA : "CALL_REF" ∈ A) :
    ∀ vs : List Value, NoAtomsL A vs → NoPairL vs
  | [], _ => trivial
  | v :: vs, h => ⟨noPair_of_noAtoms hA v h.1, noPairL_of_noAtoms hA vs h.2⟩

theorem noPairF_of_noAtoms {A : List MixopS} (hA : "CALL_REF" ∈ A) :
    ∀ gs : List (AtomS × Value), NoAtomsF A gs → NoPairF gs
  | [], _ => trivial
  | (_, v) :: gs, h => ⟨noPair_of_noAtoms hA v h.1, noPairF_of_noAtoms hA gs h.2⟩
end

/-- **`EasyP` contains `RMRed.Easy`.** -/
theorem easyP_of_easy {P : Profile} {c : Config H} (h : RMRed.Easy hn P host c) :
    EasyP hn P host c :=
  ⟨h.1, h.2.1, noPair_of_noAtoms (by simp [HStep.hAtoms]) _ h.2.2⟩

/-! ## The transfers -/

theorem qp_of {c c' : Value} (hm : NoAtoms msAtoms c) (hp : NoPair c) : Qp (.tuple [c, c']) :=
  ⟨⟨c, c', rfl, hm⟩, ⟨c, c', rfl, hp⟩⟩

/-- **The whole step reads alike at `BD` and round 6's `BI`** on `Qp` sources. -/
theorem sstep_bd_bi_iff_p {P : Profile} {c c' : Value} (hm : NoAtoms msAtoms c) (hp : NoPair c) :
    SStep (simEnv (BD P hn host)) c c' ↔ SStep (simEnv (Prims.builtins P hn host)) c c' :=
  ⟨HStep.sstep_agree (HAgree.agreeOff_bd_bi P hn host) stepInvH_p (qp_of hm hp),
    HStep.sstep_agree (HAgree.agreeOff_symm (HAgree.agreeOff_bd_bi P hn host)) stepInvH_p
      (qp_of hm hp)⟩

/-- **The backend whole step reads alike at `BD` and round 6's `BI`** on `Qp` sources. -/
theorem sstepB_bd_bi_iff_p {P : Profile} {c c' : Value} (hm : NoAtoms msAtoms c)
    (hp : NoPair c) :
    SStepB (simEnv (BD P hn host)) c c' ↔ SStepB (simEnv (Prims.builtins P hn host)) c c' :=
  ⟨HCasts.sstepB_agree (HAgree.agreeOff_bd_bi P hn host) stepInvBH_p (qp_of hm hp),
    HCasts.sstepB_agree (HAgree.agreeOff_symm (HAgree.agreeOff_bd_bi P hn host)) stepInvBH_p
      (qp_of hm hp)⟩

/-! ## `forward` and the casts at `EasyP` sources -/

/-- **`forward` at `BD` at `EasyP` sources.** -/
theorem forwardD_p {P : Profile} (hinj : Function.Injective hn) (hf : HostFinite host)
    (hh : HostOk host) {c c' : Config H} {ts : List CValType} (hc : ConfigOk c ts)
    (hb : BoundedSelM c) (hsucc : ∀ c₁, Step P host c c₁ → BoundedSelM c₁) (hx : ¬ CastRedex c.code)
    (hE : EasyP hn P host c) (hs : Step P host c c') :
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧ SStep (simEnv (BD P hn host)) (configVD hn c) (configVD hn d') := by
  obtain ⟨hm, hms, hp⟩ := hE
  obtain ⟨c'', hs'', hu, hF⟩ := Round6.Target.forwardR' hinj hf hs
    (Round7.MemSimd.bounded_of_boundedM hb.1.1 hm) hx
  have hT := VInv.typed_of_typedD hm
    (Round7.MemSimd.typedD_of_configOk_selM (Prims.builtins P hn host) hn hc hb)
  have hc'' := (Step.preservation hh hc hs'').1
  have hT'' := VInv.typed_of_typedD (hms _ hs'')
    (Round7.MemSimd.typedD_of_configOk_selM (Prims.builtins P hn host) hn hc''
      (hsucc _ hs''))
  obtain ⟨d', hd', -, hst⟩ := hF hT hT''
  refine ⟨c'', hs'', hu, d', hd', ?_⟩
  rw [Round7.MemSimd.configVD_eq_of_noMemSimd hn hm,
    Round7.MemSimd.configVD_eq_of_noMemSimd hn (VInv.noMemSimd_of_configEq hd' (hms _ hs''))]
  exact (sstep_bd_bi_iff_p (MSAtoms.noAtoms_ms_configV hn hm) hp).2 hst

/-- **`castsFwd` at `BD` at `EasyP` sources.** -/
theorem castsFwdD_p {nd : Bool} {r : RelaxedChoice} (hinj : Function.Injective hn)
    (hf : HostFinite host) (hh : HostOk host) {c c' : Config H} {ts : List CValType}
    (hc : ConfigOk c ts) (hb : BoundedSelM c)
    (hsucc : ∀ c₁, Step (Profile.spec nd r) host c c₁ → BoundedSelM c₁) (hx : CastRedex c.code)
    (hE : EasyP hn (Profile.spec nd r) host c) (hs : Step (Profile.spec nd r) host c c') :
    ∃ d', Bwd.ConfigEq c' d' ∧
      Round6.Int.backend.step (BD (Profile.spec nd r) hn host) (configVD hn c) (configVD hn d') := by
  obtain ⟨hm, hms, hp⟩ := hE
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
  exact (sstepB_bd_bi_iff_p (MSAtoms.noAtoms_ms_configV hn hm) hp).2 hst

/-- **`castsBwd` at `BD` at `EasyP` sources.** -/
theorem castsBwdD_p {nd : Bool} {r : RelaxedChoice} (hinj : Function.Injective hn)
    (hf : HostFinite host) (hh : HostOk host) {c : Config H} {ts : List CValType} {w : Value}
    (hc : ConfigOk c ts) (hb : BoundedSelM c) (hx : CastRedex c.code)
    (hE : EasyP hn (Profile.spec nd r) host c)
    (hs : Round6.Int.backend.step (BD (Profile.spec nd r) hn host) (configVD hn c) w) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step (Profile.spec nd r) host c c' := by
  obtain ⟨hm, hms, hp⟩ := hE
  have O := Round6.Int.openR_backend (hn := hn) (host := host) (nd := nd) (r := r) hinj hf hh
  have hT := VInv.typed_of_typedD hm
    (Round7.MemSimd.typedD_of_configOk_selM (Prims.builtins (Profile.spec nd r) hn host) hn hc hb)
  rw [Round7.MemSimd.configVD_eq_of_noMemSimd hn hm] at hs
  have hs' : SStepB (simEnv (Prims.builtins (Profile.spec nd r) hn host)) (configV hn c) w :=
    (sstepB_bd_bi_iff_p (MSAtoms.noAtoms_ms_configV hn hm) hp).1 hs
  obtain ⟨c', d', hd', -, hw, hst⟩ := O.casts.bwd c c ts w hc
    (Round7.MemSimd.boundedSel_of_boundedSelM hb hm) ⟨Bwd.ConfigEq.refl c, hT⟩ hx hs'
  refine ⟨c', d', hd', ?_, hst⟩
  rw [hw, Round7.MemSimd.configVD_eq_of_noMemSimd hn (VInv.noMemSimd_of_configEq hd' (hms _ hst))]

/-! ## The narrowed reduction -/

/-- **`OpenRMRestDP` gives `RMRed.OpenRMRestDR`.** -/
theorem openRMRestDR_of_P {nd : Bool} {r : RelaxedChoice} (hinj : Function.Injective hn)
    (hf : HostFinite host) (hh : HostOk host) (O : OpenRMRestDP hn (Profile.spec nd r) host) :
    RMRed.OpenRMRestDR hn (Profile.spec nd r) host where
  forward c c' ts hc hb hsucc hx _ hs hH := by
    by_cases hE : EasyP hn (Profile.spec nd r) host c
    · exact forwardD_p hinj hf hh hc hb hsucc hx hE hs
    exact O.forward c c' ts hc hb hsucc hx hE hs hH
  restMSHC := O.restMSHC
  castsFwd c c' ts hc hb hsucc hx _ hs := by
    by_cases hE : EasyP hn (Profile.spec nd r) host c
    · exact castsFwdD_p hinj hf hh hc hb hsucc hx hE hs
    exact O.castsFwd c c' ts hc hb hsucc hx hE hs
  castsBwd c ts w hc hb hx _ hs := by
    by_cases hE : EasyP hn (Profile.spec nd r) host c
    · exact castsBwdD_p hinj hf hh hc hb hx hE hs
    exact O.castsBwd c ts w hc hb hx hE hs

/-- **`Round7.MemSimd.Task.wholeStepValidRM` from `OpenRMRestDP`.** -/
theorem wholeStepValidRM_of_restDP
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), OpenRMRestDP hn (Profile.spec nd r) host) :
    Round7.MemSimd.Task.wholeStepValidRM :=
  RMRed.wholeStepValidRM_of_restDR fun H hn hinj host hf hh nd r =>
    openRMRestDR_of_P hinj hf hh (h H hn hinj host hf hh nd r)

end Silmaril.Wasm.SpecTec.Sim.Round7.HPair
