module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Target.Generic
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round6.Target.BwdVec
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round6.Target.CastFires
public import Silmaril.Wasm.SpecTec.Sim.Round5.Target.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Read2.Thms

/-!
# Round 6: the backward simulation away from casts, from proved leaves only

The backward recursion `backward_upToVC` under `NoCastV` (`ReadValidS` and no cast redex), at
the concrete builtins, with every per-rule obligation a proved round-5 lemma:

* `Step_pure`: as `Round5.Target.backwardSel_pure`, the vector rules from
  `Round5.Convert.vecAgreeNC_builtins` and `Round5.Convert.vecConvertR_builtins`
  (`pure_vecDoneNC`; `Vec.VecAgree`'s `convert` is false under `Profile.spec`), the open rules
  64, 70–73 from `Round5.Simd.pureOpenVtestop`;
* `Step_read`: as `Round5.Target.backwardSel_read`, with the cast rules (`Round5.Read.readDoneK`)
  excluded by `castRedex_of_fires_readK` and the rest from `Round5.Read2.readRest`;
* `Step`: as `Round5.Target.backwardSel_step`, the rest from `Round5.BwdStep.remStep`;
* the host rules from `Round5.FwdRef.hostStepsV_of_T` and `Round5.FwdRef2.hostRespectsT_all`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Target

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4Read (BackwardUpToV)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **The vector rules of `Step_pure`, backward, at the concrete builtins**, from
`VecAgreeNC` and `VecConvertR` (both proved). -/
theorem pure_vecDoneNC (i : Nat) (hi : i ∈ Round5.BwdStep.pureVecDone) (s : Store H)
    (f : Frame) (is : List Admin) (w : Value)
    (hf : Fires (simEnv (BI P hn host)) "Step_pure" i (.tuple [.list (adminsToV is), w])) :
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧
      Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨is', hw, hs⟩ := bwd_vectorRulesNC (Vec.hasVectorRules_simEnv _)
    Round5.BwdStep.vecDecode Round5.Convert.vecAgreeNC_builtins
    Round5.Convert.vecConvertR_builtins i hi hf
  exact ⟨is', is', Bwd.CodeEq.refl _, hw, hs⟩

/-- **The open `Step_pure` rules, backward, at the concrete builtins** (`Round5.BwdStep`'s
`remPure_of_open` with `pure_vecDoneNC` and `Round5.Simd.pureOpenVtestop`). -/
theorem remPureNC :
    ∀ i, i ∉ Bwd.pureDone → i ∉ Integrate.floatDone → i ∉ BwdPureStep.pureDone →
      ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value), Round4Read.ReadValid ⟨s, f, is⟩ →
      Typed (simEnv (BI P hn host)) hn ⟨s, f, is⟩ →
      Fires (simEnv (BI P hn host)) "Step_pure" i (.tuple [.list (adminsToV is), w]) →
      ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧
        Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro i h₁ h₂ h₃ s f is w hv hc hf
  have hlt := Round5.BwdStep.pure_lt hf
  by_cases hd : i ∈ Round5.BwdStep.pureVecDone
  · exact pure_vecDoneNC i hd s f is w hf
  · refine Round5.Simd.pureOpenV_of_vtestop Round5.Simd.pureOpenVtestop i ?_ s f is w hv hc hf
    simp only [Bwd.pureDone, Integrate.floatDone, BwdPureStep.pureDone,
      Round5.BwdStep.pureVecDone, Round5.BwdStep.pureOpenR5, List.mem_append, List.mem_cons,
      List.mem_nil_iff, or_false] at h₁ h₂ h₃ hd ⊢
    omega

/-- The host-call rules (`Step` 8, 9), backward, at the concrete builtins
(`Round5.FwdRef.hostStepsV_of_T` with `Round5.FwdRef2.hostRespectsT_all`). -/
theorem hostStepsBI (hinj : Function.Injective hn) (hf : HostFinite host) :
    Round5.Bwd.HostStepsV (simEnv (BI P hn host)) hn P host :=
  Round5.FwdRef.hostStepsV_of_T hf (Round5.FwdRef2.hostRespectsT_all (BI P hn host) hinj host)

/-- **The per-rule backward obligations under `NoCastV`**, at the concrete builtins, for an
injective encoding, a finite host and a profile in which growth may both succeed and fail. -/
theorem backwardUpToNC (hinj : Function.Injective hn) (hf : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d) :
    BackwardUpToV NoCastV (simEnv (BI P hn host)) hn P host where
  pure i s f is w hv hc hfi := by
    by_cases h₀ : i ∈ Bwd.pureDone
    · exact (Round5.Bwd.famBwdV_of_hostSteps (hostStepsBI hinj hf)).pure
        i h₀ s f is w hv.1.r.read hc hfi
    by_cases h₁ : i ∈ Integrate.floatDone
    · exact Integrate.pure_floatDone (Prims.intB_builtins hn host)
        (Prims.floatB_builtins hn host) h₁ hfi
    by_cases h₂ : i ∈ BwdPureStep.pureDone
    · exact Bwd.pure_upTo (BwdPureStep.pure_done _ (BwdPureStep.bwdB_builtins hn host) i h₂ hfi)
    · exact remPureNC i h₀ h₁ h₂ s f is w hv.1.r.read hc hfi
  read i c w hv hc hfi := by
    by_cases h₀ : i ∈ Bwd.readDoneUpTo
    · exact (Round5.Bwd.famBwdV_of_hostSteps (hostStepsBI hinj hf)).read
        i h₀ c w hv.1.r.read hc hfi
    by_cases h₁ : i ∈ BwdRead.readDone
    · exact Bwd.read_upTo (BwdRead.read_done _ (BwdRead.noAcc_builtins P hn host) i h₁ c w hc hfi)
    by_cases h₂ : i ∈ Round4Read.readDoneV
    · exact Bwd.read_upTo (Round4Read.read_doneV _ (BwdRead.noAcc_builtins P hn host) i h₂ c w
      hv.1.r.read hc hfi)
    by_cases h₃ : i ∈ Round5.Bwd.readDoneR
    · exact Bwd.read_upTo (Round5.Bwd.read_doneR i h₃ c w hv.1.r hc hfi)
    by_cases h₄ : i ∈ Round5.Read.readDoneS
    · exact Bwd.read_upTo (Round5.Read.read_doneS i h₄ c w hv.1 hc hfi)
    by_cases h₅ : i ∈ Round5.Read.readDoneK
    · exact absurd (castRedex_of_fires_readK h₅ hfi) hv.2
    · exact Round5.Read2.readRest i (Round5.Read.lt_of_fires_read hfi) h₀ h₁ h₂ h₃ h₄ h₅ c w
        hv.1 hc hfi
  step i h6 c w hv hc hfi := by
    by_cases h₀ : i ∈ Bwd.stepDone
    · exact (Round5.Bwd.famBwdV_of_hostSteps (hostStepsBI hinj hf)).step
        i h₀ c w hv.1.r.read hc hfi
    by_cases h₁ : i ∈ BwdPureStep.stepDone
    · exact Bwd.step_upTo (BwdPureStep.step_done _ (BwdPureStep.bwdB_builtins hn host) i h₁ hfi)
    · exact Round5.BwdStep.remStep hPs hPf i h6 h₀ h₁ c w hv.1.r.read hc hfi

/-- **The backward simulation from typed `NoCastV` sources**, at the concrete builtins, with no
hypothesis beyond an injective encoding, a finite host and a profile in which growth may both
succeed and fail. -/
theorem backwardNC (hinj : Function.Injective hn) (hf : HostFinite host)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (hPf : ∀ k a n d, P.growMayFail k a n d)
    (c : Config H) (w : Value) (hv : NoCastV c) (hc : Typed (simEnv (BI P hn host)) hn c)
    (hs : SStep (simEnv (BI P hn host)) (configV hn c) w) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step P host c c' :=
  backward_upToVC noCastV_closed (backwardUpToNC hinj hf hPs hPf)
    (Bwd.structDecode_of_ctrl (Typing.ctrlDecode_simEnv _)) (Typing.typingFacts_simEnv _ hn)
    (hasStepRules_simEnv _) (Bwd.findRel_of_ruleAt (simEnv_execRules _).unreachable)
    (Bwd.findRel_of_ruleAt (simEnv_readRules _).call) c w hv hc hs

end Silmaril.Wasm.SpecTec.Sim.Round6.Target
