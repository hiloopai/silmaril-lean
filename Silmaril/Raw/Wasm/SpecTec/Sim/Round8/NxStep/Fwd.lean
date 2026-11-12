module

public import Silmaril.Wasm.SpecTec.Sim.Round8.NxStep.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round8.NxElse.Thms

/-!
# Round 8, `Step` and `Step_read` across erasure, rule by rule (unrefined)

`stepFwd`: a derivation of `Step` or `Step_read` under SpecTec's `otherwise` gives one of the erased
value from the erased arguments, given `BadFwd` at the rules that fail `goodRule`. The proof is
the rule case of round 8's `NxDer.dderivesB_fwd`, by structural recursion on the derivation:

* the conclusion goes across by `NxErase.erase_alt` and the quantifiers by `NxTyp.typFwdN_utf8Env`;
* a top-level `if` premise goes across by `NxClause.ifPr_fwd`;
* a relation premise of `Step` or `Step_read` goes across by the recursion, its arguments and
  expression by `NxDer.args_fwd` and `NxDer.exp_fwd`;
* every other premise has no failing site and reads only `grE` relations, so it goes across by
  `NxDer.dpremB_fwd`, with its relation premises read through `NxElse.elseF` and `otherwise`
  discharged by `NxElse.hO_else`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.NxStep

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
open Round6.Reading (DDerivesB DPremB conclAlts otherwiseB)

variable {B : Builtins}

theorem reach_stepRel {x : IL.Id} (h : stepRel x = true) : reach 0 x = true := by
  simp only [stepRel, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl <;> decide

theorem premS_rule {y : IL.Id} {args : List Arg} {op : MixopS} {e : Exp}
    (h : premS (.rulePr y args op e) = true) (hy : stepRel y = true) :
    EraseAll.xArgs grE gdE args = true ∧ xExp grE gdE e = true := by
  simpa [premS, hy] using h

theorem premS_other {pr : Prem} (h : premS pr = true)
    (hpr : ∀ y args op e, pr = .rulePr y args op e → stepRel y = false) :
    xPrem grE gdE pr = true ∧ NxDer.listIter pr = true ∧ NxElse.elseIn pr = false := by
  cases pr with
  | rulePr y args op e =>
    have hy := hpr y args op e rfl
    simp only [premS, hy] at h
    exact ⟨by simpa using h, rfl, rfl⟩
  | _ =>
    simp only [premS, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨h.1.1, h.1.2, h.2⟩

section Fwd

set_option linter.unusedSectionVars false

variable (hB : NxSound.BuiltinsVT sigX tsigFixed (utf8Env B)) (H : BIErase QT gdE (utf8Env B))
  (hBad : BadFwd (utf8Env B))
include hB H hBad

set_option maxRecDepth 20000

mutual
/-- **A derivation of `Step` or `Step_read` goes to the erased side**, given `BadFwd`. -/
theorem stepFwd :
    ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}, stepRel x = true →
      DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op args v →
      DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op (args.map eraseA) (eraseV v)
  | x, op, args, v, hx, .rule (σ := σ) (ρ₀ := ρ₀) (qs := qs) (ps := ps) (prems := prems) (i := i)
      (e := e) (nm := nm) (e' := e') (t := t) (rules := rules) hrel hrule halt hps hq he hp => by
    cases hg : goodRule (.ruleD nm qs op e prems) with
    | false =>
      exact hBad hx ⟨ps, t, rules, nm, qs, e, e', prems, ρ₀, σ, hrel, hrule, hg, halt, hps, hq, he,
        hp⟩
    | true =>
    simp only [goodRule, Bool.and_eq_true, List.all_eq_true] at hg
    have hr : reach 0 x = true := reach_stepRel hx
    have hF := NxRule.rFacts hr hrel hrule
    obtain ⟨hargs, hρ⟩ := EraseDer.bindParams_nil_args (hF.params ▸ hps)
    have hq' : QuantsOk (utf8Env B) (VarEnv.empty.bindVals σ) qs := hρ ▸ hq
    have heq : ρ₀.bindVals (σ.map eraseP) = eraseScope (ρ₀.bindVals σ) := by
      rw [hρ, NxDer.eraseScope_inst]
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
    · rw [hρ, ← NxDer.eraseScope_inst]
      exact NxTyp.typFwdN_utf8Env hr hrel hrule hq'
    · obtain ⟨n, hn⟩ := he
      refine ⟨n, ?_⟩
      rw [hρ] at hn
      rw [hρ, ← NxDer.eraseScope_inst,
        NxErase.erase_alt hD H hr hrel hrule hq' hCE halt (hg.1 _ halt) n, hn]
      rfl
    · rw [heq]
      obtain ⟨hpt, hpa, hpc⟩ := hF.premsOk pr hpr
      have hS := hg.2 pr hpr
      by_cases hif : ∃ c, pr = .ifPr c
      · obtain ⟨c, rfl⟩ := hif
        have hxc : xExp grE gdE c = true := by
          simp only [premS, xPrem, Bool.and_eq_true] at hS
          exact hS.1.1
        cases hp _ hpr with
        | ifPr h =>
          rw [hρ] at h ⊢
          exact .ifPr (NxClause.ifPr_fwd hD H hr hrel hrule hq' hCE hpr hxc h)
      · have hbs : bindSite sigX (quantsΓ qs) pr = false := by
          cases pr with
          | ifPr c => exact absurd ⟨c, rfl⟩ hif
          | _ => rfl
        have hb := NxRule.badPr_zero hr hrel hrule hpr hbs
        by_cases hst : ∃ y args' op' e₁, pr = .rulePr y args' op' e₁ ∧ stepRel y = true
        · obtain ⟨y, args', op', e₁, rfl, hy⟩ := hst
          obtain ⟨hxa, hxe⟩ := premS_rule hS hy
          exact stepPrem hC (NxRule.agreeOn_qScope hpc) hpt hpa (hX.2 _ hpr) hb
            ⟨y, args', op', e₁, rfl, hxa, hxe, hy⟩ (hp _ hpr)
        · have hS' := premS_other hS fun y args' op' e₁ h => by
            cases hy : stepRel y
            · rfl
            · exact absurd ⟨y, args', op', e₁, h, hy⟩ hst
          have hfire := NxElse.dpremB_fire (els' := otherwiseB (utf8Env B) x
            (args.map eraseA) i (eraseV v)) hS'.1 (fun h => by rw [hS'.2.2] at h; cases h)
            (hp pr hpr)
          exact NxDer.dpremB_fwd hB H (NxElse.hO_else hB H) hC (NxRule.agreeOn_qScope hpc) hpt
            hpa (hX.2 pr hpr) hb hS'.1 hS'.2.1 id hfire
termination_by structural _ _ _ _ _ hd => hd

/-- **A relation premise of `Step` or `Step_read` goes to the erased side.** -/
theorem stepPrem :
    ∀ {els els' : Prop} {Γ : List (String × AT)} {ρq ρ : VarEnv} {pr : Prem}, PCtx B Γ ρq →
      VarEnv.AgreeOn (freePrem pr) ρ ρq → premTy sigX tsigFixed Γ pr = true →
      premAuxR pr = true → premX ctx0 pr = true → badPr sigX Γ pr = 0 →
      (∃ y args op e, pr = .rulePr y args op e ∧ EraseAll.xArgs grE gdE args = true ∧
        xExp grE gdE e = true ∧ stepRel y = true) →
      DPremB (utf8Env B) (otherwiseB (utf8Env B)) els ρ pr →
      DPremB (utf8Env B) (otherwiseB (utf8Env B)) els' (eraseScope ρ) pr
  | _, _, _, _, _, _, hc, hag, ht, ha, hX, hb, hS, .rulePr hav hev hd => by
    obtain ⟨y, args, op, e, heq, hxa, hxe, hy⟩ := hS
    cases heq
    simp only [premTy, ckRulePr, Bool.and_eq_true] at ht
    simp only [premAuxR, Bool.and_eq_true] at ha
    simp only [premX, Bool.and_eq_true] at hX
    simp only [badPr] at hb
    exact .rulePr
      (NxDer.args_fwd H hc (hag.mono (EraseDer.sub_rule_args _ _ _ _)) ht.1.1 ha.1.2 hX.1
        (by omega) hxa hav)
      (NxDer.exp_fwd H hc (hag.mono (EraseDer.sub_rule_exp _ _ _ _)) ht.1.2 ha.2 hX.2
        (by omega) hxe hev)
      (stepFwd hy hd)
  | _, _, _, _, _, _, _, _, _, _, _, _, hS, .ifPr _ => by
    obtain ⟨_, _, _, _, h, _⟩ := hS; cases h
  | _, _, _, _, _, _, _, _, _, _, _, _, hS, .elsePr _ => by
    obtain ⟨_, _, _, _, h, _⟩ := hS; cases h
  | _, _, _, _, _, _, _, _, _, _, _, _, hS, .letPr _ _ => by
    obtain ⟨_, _, _, _, h, _⟩ := hS; cases h
  | _, _, _, _, _, _, _, _, _, _, _, _, hS, .iterOptNone _ _ _ => by
    obtain ⟨_, _, _, _, h, _⟩ := hS; cases h
  | _, _, _, _, _, _, _, _, _, _, _, _, hS, .iterOptSome _ _ _ _ => by
    obtain ⟨_, _, _, _, h, _⟩ := hS; cases h
  | _, _, _, _, _, _, _, _, _, _, _, _, hS, .iterList _ _ _ _ _ _ => by
    obtain ⟨_, _, _, _, h, _⟩ := hS; cases h
  | _, _, _, _, _, _, _, _, _, _, _, _, hS, .iterListN _ _ _ _ _ _ => by
    obtain ⟨_, _, _, _, h, _⟩ := hS; cases h
termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ hd => hd
end

end Fwd

end Silmaril.Wasm.SpecTec.Sim.Round8.NxStep
