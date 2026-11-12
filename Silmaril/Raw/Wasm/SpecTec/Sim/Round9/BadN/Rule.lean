module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.BadN.Iter

/-!
# Round 9, RE: the rule case at rules passing `goodRuleN` (unrefined)

`ruleFwdN`: where a rule of `Step`/`Step_read` passing `goodRuleN` fires under SpecTec's
`otherwise`, its erased instance fires on the erased side. This is the rule case of round 8's
`NxStep.stepFwd` without `Step` premises, with indexed iterations handled by `iterN_fwd`.
`badFwdE_of_N`: `BadFwdE` from `BadFwdN` (seven rules).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.BadN

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
open Silmaril.Wasm.SpecTec.Sim.Round7.NxRule (qScope ctx0 premAuxR)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxErase (QT premX)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV eraseA)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (BIErase grE gdE xExp xPrem eraseP)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round8.NxDer (PCtx)
open Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
open Round6.Reading (DDerivesB DPremB conclAlts otherwiseB)

variable {B : Builtins}

theorem iterN_inv {pr : Prem} (h : iterN pr = true) :
    ∃ pr' eₙ ido ds, pr = .iterPr pr' (.mk (.listN eₙ ido) ds) ∧
      Round8.NxDer.listIter pr' = true ∧ Round8.NxElse.elseIn pr' = false := by
  unfold iterN at h
  split at h
  · rename_i pr' eₙ ido ds
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨pr', eₙ, ido, ds, rfl, h.1, h.2⟩
  · cases h

section Rule

set_option linter.unusedSectionVars false

variable (hB : NxSound.BuiltinsVT sigX tsigFixed (utf8Env B)) (H : BIErase QT gdE (utf8Env B))
include hB H

/-- **The rule case at a rule passing `goodRuleN`.** -/
theorem ruleFwdN {x : IL.Id} {op : MixopS} {args : List ArgV} {i : Nat} {v : Value}
    {ps : List Param} {t : Typ} {rules : List Rule} {nm : IL.Id} {qs : List Param} {e e' : Exp}
    {prems : List Prem} {ρ₀ : VarEnv} {σ : List (IL.Id × Value)}
    (hx : Round8.NxStep.stepRel x = true)
    (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e prems))
    (hg : goodRuleN (.ruleD nm qs op e prems) = true) (halt : e' ∈ conclAlts e)
    (hps : bindParams VarEnv.empty ps args = some ρ₀)
    (hq : QuantsOk (utf8Env B) (ρ₀.bindVals σ) qs)
    (he : EvalExp (utf8Env B) (ρ₀.bindVals σ) e' v)
    (hp : ∀ pr ∈ prems, DPremB (utf8Env B) (otherwiseB (utf8Env B))
      (otherwiseB (utf8Env B) x args i v) (ρ₀.bindVals σ) pr) :
    DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op (args.map eraseA) (eraseV v) := by
  simp only [goodRuleN, Bool.and_eq_true, List.all_eq_true] at hg
  have hr : reach 0 x = true := Round8.NxStep.reach_stepRel hx
  have hF := NxRule.rFacts hr hrel hrule
  obtain ⟨hargs, hρ⟩ := EraseDer.bindParams_nil_args (hF.params ▸ hps)
  have hq' : QuantsOk (utf8Env B) (VarEnv.empty.bindVals σ) qs := hρ ▸ hq
  have heq : ρ₀.bindVals (σ.map eraseP) = eraseScope (ρ₀.bindVals σ) := by
    rw [hρ, Round8.NxDer.eraseScope_inst]
  have hD := NxFlow.flowSound B hB
  have hCE : ∀ k, NxErase.CallE gdE sigX tsigFixed ctx0 (utf8Env B)
      (qScope qs (VarEnv.empty.bindVals σ)) k :=
    fun k => NxClause.clauseErase B hB H _ k rfl rfl
  have hC : PCtx B (quantsΓ qs) (qScope qs (ρ₀.bindVals σ)) := by
    rw [hρ]
    exact ⟨NxRule.scopeVT_qScope (NxRule.typsNx_inst σ) hq' hF.wild,
      fun n => ⟨NxRule.callH_nil hD rfl rfl n, hCE n, fun p hp => by
        simp [qScope, VarEnv.bindVals, VarEnv.empty, Map.empty] at hp⟩⟩
  have hX := NxErase.ruleX_at hr hrel (List.mem_of_getElem? hrule)
  simp only [NxErase.ruleX, Bool.and_eq_true, List.all_eq_true] at hX
  have hps' : bindParams VarEnv.empty ps (args.map eraseA) = some ρ₀ := by
    rw [hargs]; rw [hargs] at hps; exact hps
  refine .rule (σ := σ.map eraseP) hrel hrule halt hps' ?_ ?_ fun pr hpr => ?_
  · rw [hρ, ← Round8.NxDer.eraseScope_inst]
    exact Round8.NxTyp.typFwdN_utf8Env hr hrel hrule hq'
  · obtain ⟨n, hn⟩ := he
    refine ⟨n, ?_⟩
    rw [hρ] at hn
    rw [hρ, ← Round8.NxDer.eraseScope_inst,
      NxErase.erase_alt hD H hr hrel hrule hq' hCE halt (hg.1 _ halt) n, hn]
    rfl
  · rw [heq]
    obtain ⟨hpt, hpa, hpc⟩ := hF.premsOk pr hpr
    have hN := hg.2 pr hpr
    by_cases hif : ∃ c, pr = .ifPr c
    · obtain ⟨c, rfl⟩ := hif
      have hxc : xExp grE gdE c = true := by
        simp only [premN, Round8.NxStep.premS, xPrem, iterN, stepPremB, Bool.and_eq_true,
          Bool.or_eq_true, Bool.false_and] at hN
        rcases hN with h | h
        · exact h.1.1.1
        · cases h
      cases hp _ hpr with
      | ifPr h =>
        rw [hρ] at h ⊢
        exact .ifPr (NxClause.ifPr_fwd hD H hr hrel hrule hq' hCE hpr hxc h)
    · have hbs : bindSite sigX (quantsΓ qs) pr = false := by
        cases pr with
        | ifPr c => exact absurd ⟨c, rfl⟩ hif
        | _ => rfl
      have hb := NxRule.badPr_zero hr hrel hrule hpr hbs
      simp only [premN, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hN
      rcases hN with ⟨hS, hns⟩ | ⟨hin, hxp⟩
      · have hS' := Round8.NxStep.premS_other hS fun y args' op' e₁ h => by
          subst h; simpa [stepPremB] using hns
        have hfire := Round8.NxElse.dpremB_fire (els' := otherwiseB (utf8Env B) x
          (args.map eraseA) i (eraseV v)) hS'.1 (fun h => by rw [hS'.2.2] at h; cases h)
          (hp pr hpr)
        exact Round8.NxDer.dpremB_fwd hB H (Round8.NxElse.hO_else hB H) hC
          (NxRule.agreeOn_qScope hpc) hpt hpa (hX.2 pr hpr) hb hS'.1 hS'.2.1 id hfire
      · obtain ⟨pr', eₙ, ido, ds, rfl, hl, hne⟩ := iterN_inv hin
        have hfire := Round8.NxElse.dpremB_fire (els' := otherwiseB (utf8Env B) x
          (args.map eraseA) i (eraseV v)) hxp
          (fun h => by simp only [Round8.NxElse.elseIn, hne] at h; cases h) (hp _ hpr)
        exact iterN_fwd hB H (Round8.NxElse.hO_else hB H) hC (NxRule.agreeOn_qScope hpc) hpt hpa
          (hX.2 _ hpr) hb hxp hl id hfire

/-- **`BadFwdE` from the seven rules of `BadFwdN`.** -/
theorem badFwdE_of_N (hN : BadFwdN (utf8Env B)) : BadFwdE (utf8Env B) := by
  intro x op args i v hx ⟨ps, t, rules, nm, qs, e, e', prems, ρ₀, σ, hrel, hrule, hg, hgE, halt,
    hps, hq, he, hp⟩
  cases hgN : goodRuleN (.ruleD nm qs op e prems) with
  | false =>
    exact hN hx ⟨ps, t, rules, nm, qs, e, e', prems, ρ₀, σ, hrel, hrule, hg, hgE, hgN, halt, hps,
      hq, he, hp⟩
  | true => exact ruleFwdN hB H hx hrel hrule hgN halt hps hq he hp

end Rule

end Silmaril.Wasm.SpecTec.Sim.Round9.BadN
