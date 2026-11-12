module

public import Silmaril.Wasm.SpecTec.Sim.Round8.NxStep.Thms
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.ElseBwd.Else
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.ElseBwd.Check

/-!
# Round 9, RE: the `otherwise` rules of `BadFwd` (unrefined)

* `elsePairs_mem`: the kernel check `elsePairs_fixed`, read at a pair of rules.
* `otherwiseB_eraseV`: at an `otherwise` rule of `Step` or `Step_read` that fired, SpecTec's
  `otherwise` goes to the erased side, given `ElseBwdB` (`ElseBwd.otherwiseAtB_map` at `eraseV`).
* `ruleFwdE`: a rule that passes `goodRuleE` goes to the erased side. This is the rule case of
  round 8's `NxStep.stepFwd` with its `otherwise` premise handled by `otherwiseB_eraseV`; the rule
  has no `Step`/`Step_read` premise, so there is no recursion.
* `badFwd_of_else`: `NxStep.BadFwd` from `BadFwdE` (the eight rules that fail `goodRuleE`) and
  `ElseBwdB`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd

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
open Silmaril.Wasm.SpecTec.Sim.Round8.NxStep (stepRel goodRule BadFwd RuleAt)
open Round6.Reading (DDerivesB DPremB conclAlts otherwiseB otherwiseAtB)

variable {B : Builtins}

/-- The pairs of `elsePairsOf` are the pairs of rules with an `otherwise` rule, an earlier rule,
and heads not known to differ. -/
theorem mem_elsePairsOf {rules : List Rule} {i j : Nat} {ri rj : Rule} (hi : rules[i]? = some ri)
    (hel : hasElse ri = true) (hj : j < i) (hrj : rules[j]? = some rj)
    (hd : headsDiffer ri rj = false) : (i, j) ∈ elsePairsOf rules := by
  have hil : i < rules.length := by
    rcases Nat.lt_or_ge i rules.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hi; cases hi
  simp only [elsePairsOf, List.mem_flatMap, List.mem_range]
  refine ⟨i, hil, ?_⟩
  rw [hi]
  simp only [hel, ite_true, List.mem_filterMap, List.mem_range]
  refine ⟨j, hj, ?_⟩
  rw [hrj]
  simp [hd]

/-- **The kernel check `elsePairs_fixed`, read at a pair of `Step_read` rules** of `simEnv B`. -/
theorem elsePairs_mem_sim {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {i j : Nat} {ri rj : Rule} (hrel : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules))
    (hi : rules[i]? = some ri) (hel : hasElse ri = true) (hj : j < i)
    (hrj : rules[j]? = some rj) (hd : headsDiffer ri rj = false) : (i, j) ∈ elsePairs := by
  have hm := List.all_eq_true.1 elsePairs_fixed _ (EraseAll.mem_rels_of_findRel' hrel)
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hm
  rw [← hm.1]
  exact mem_elsePairsOf hi hel hj hrj hd

/-- `elsePairs_mem_sim` in `utf8Env B`. -/
theorem elsePairs_mem {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i j : Nat}
    {ri rj : Rule} (hrel : (utf8Env B).findRel? "Step_read" = some (ps, op, t, rules))
    (hi : rules[i]? = some ri) (hel : hasElse ri = true) (hj : j < i)
    (hrj : rules[j]? = some rj) (hd : headsDiffer ri rj = false) : (i, j) ∈ elsePairs :=
  elsePairs_mem_sim (by rw [← findRel?_utf8Env]; exact hrel) hi hel hj hrj hd

/-- No rule of `Step` has an `otherwise` premise (the kernel check `elsePairs_fixed`). -/
theorem step_noElse {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i : Nat}
    {ri : Rule} (hrel : (utf8Env B).findRel? "Step" = some (ps, op, t, rules))
    (hi : rules[i]? = some ri) : hasElse ri = false := by
  rw [findRel?_utf8Env] at hrel
  have hm := List.all_eq_true.1 elsePairs_fixed _ (EraseAll.mem_rels_of_findRel' hrel)
  have hne : ("Step" != "Step_read") = true := by decide
  simp only [hne, Bool.true_or, bne_self_eq_false, Bool.false_or, Bool.true_and,
    Bool.not_eq_true', List.any_eq_false] at hm
  cases h : hasElse ri
  · rfl
  · exact absurd h (hm ri (List.mem_of_getElem? hi))

theorem hasElse_of_mem {nm : IL.Id} {qs : List Param} {op : MixopS} {e : Exp}
    {prems : List Prem} (h : Prem.elsePr ∈ prems) : hasElse (.ruleD nm qs op e prems) = true := by
  simp only [hasElse, List.any_eq_true]
  exact ⟨_, h, rfl⟩

theorem elseIn_of_mem {prems : List Prem} (h : Prem.elsePr ∈ prems) :
    prems.any Round8.NxElse.elseIn = true := by
  simp only [List.any_eq_true]
  exact ⟨_, h, rfl⟩

/-- **SpecTec's `otherwise` goes to the erased side** at a fired `otherwise` rule of `Step` or
`Step_read`, given `ElseBwdB`. -/
theorem otherwiseB_eraseV (hP : ElseBwdB (utf8Env B)) {x : IL.Id} {ps : List Param}
    {op : MixopS} {t : Typ} {rules : List Rule} {i : Nat} {nm : IL.Id} {qs : List Param}
    {e : Exp} {prems : List Prem} {args : List ArgV} {v : Value} (hx : stepRel x = true)
    (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e prems)) (hel : Prem.elsePr ∈ prems)
    (hargs : args = []) (hF : Round8.NxElse.Fired (utf8Env B) x args i v)
    (h : otherwiseB (utf8Env B) x args i v) :
    otherwiseB (utf8Env B) x (args.map eraseA) i (eraseV v) := by
  subst hargs
  simp only [stepRel, Bool.or_eq_true, beq_iff_eq] at hx
  rcases hx with rfl | rfl
  · have h₀ := step_noElse hrel hrule
    rw [hasElse_of_mem hel] at h₀
    cases h₀
  · unfold otherwiseB at h ⊢
    refine otherwiseAtB_map (fun _ _ _ => eraseV_pair) vHead_eraseV hF ?_ h
    intro j hj ps' op' t' rules' ri rj hrel' hi hrj hd
    rw [hrel] at hrel'
    cases hrel'
    rw [hrule] at hi
    cases hi
    exact hP (i, j) (elsePairs_mem hrel hrule (hasElse_of_mem hel) hj hrj hd)

theorem premSE_cases {pr : Prem} (h : premSE pr = true) :
    pr = .elsePr ∨ (Round8.NxStep.premS pr = true ∧ stepPremB pr = false) := by
  cases pr with
  | elsePr => exact .inl rfl
  | _ =>
    right
    simp only [premSE, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h

section Fwd

set_option linter.unusedSectionVars false

variable (hB : NxSound.BuiltinsVT sigX tsigFixed (utf8Env B)) (H : BIErase QT gdE (utf8Env B))
  (hP : ElseBwdB (utf8Env B))
include hB H hP

set_option maxRecDepth 20000 in
/-- **A rule that passes the check up to `otherwise` goes to the erased side**, given
`ElseBwdB`. -/
theorem ruleFwdE {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value} {ps : List Param}
    {t : Typ} {rules : List Rule} {i : Nat} {nm : IL.Id} {qs : List Param} {e e' : Exp}
    {prems : List Prem} {ρ₀ : VarEnv} {σ : List (IL.Id × Value)} (hx : stepRel x = true)
    (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e prems)) (halt : e' ∈ conclAlts e)
    (hps : bindParams VarEnv.empty ps args = some ρ₀)
    (hq : QuantsOk (utf8Env B) (ρ₀.bindVals σ) qs) (he : EvalExp (utf8Env B) (ρ₀.bindVals σ) e' v)
    (hp : ∀ pr ∈ prems, DPremB (utf8Env B) (otherwiseB (utf8Env B))
      (otherwiseB (utf8Env B) x args i v) (ρ₀.bindVals σ) pr)
    (hg : goodRuleE (.ruleD nm qs op e prems) = true) :
    DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op (args.map eraseA) (eraseV v) := by
  simp only [goodRuleE, Bool.and_eq_true, List.all_eq_true] at hg
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
    rcases premSE_cases (hg.2 pr hpr) with rfl | ⟨hS, hns⟩
    · cases hp _ hpr with
      | elsePr h =>
        exact .elsePr (otherwiseB_eraseV hP hx hrel hrule hpr hargs
          ⟨ps, op, t, rules, nm, qs, e, prems, e', ρ₀, σ, hrel, hrule, elseIn_of_mem hpr, halt,
            hps, hq, he⟩ h)
    obtain ⟨hpt, hpa, hpc⟩ := hF.premsOk pr hpr
    by_cases hif : ∃ c, pr = .ifPr c
    · obtain ⟨c, rfl⟩ := hif
      have hxc : xExp grE gdE c = true := by
        simp only [Round8.NxStep.premS, xPrem, Bool.and_eq_true] at hS
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
      have hS' := Round8.NxStep.premS_other hS fun y args' op' e₁ h => by
        subst h; simpa [stepPremB] using hns
      have hfire := Round8.NxElse.dpremB_fire (els' := otherwiseB (utf8Env B) x
        (args.map eraseA) i (eraseV v)) hS'.1 (fun h => by rw [hS'.2.2] at h; cases h)
        (hp pr hpr)
      exact Round8.NxDer.dpremB_fwd hB H (Round8.NxElse.hO_else hB H) hC
        (NxRule.agreeOn_qScope hpc) hpt hpa (hX.2 pr hpr) hb hS'.1 hS'.2.1 id hfire

/-- **`NxStep.BadFwd` from the eight rules that fail `goodRuleE` and the pairs left.** -/
theorem badFwd_of_else (hE : BadFwdE (utf8Env B)) : BadFwd (utf8Env B) := by
  intro x op args i v hx ⟨ps, t, rules, nm, qs, e, e', prems, ρ₀, σ, hrel, hrule, hg, halt, hps,
    hq, he, hp⟩
  cases hgE : goodRuleE (.ruleD nm qs op e prems) with
  | false =>
    exact hE hx ⟨ps, t, rules, nm, qs, e, e', prems, ρ₀, σ, hrel, hrule, hg, hgE, halt, hps, hq,
      he, hp⟩
  | true => exact ruleFwdE hB H hP hx hrel hrule halt hps hq he hp hgE

end Fwd

/-- **The declarative `otherwise` goes along code erasure** at a fired `otherwise` rule of
`Step_read` in `simEnv B`, given `ElseBwdD` (RM). -/
theorem otherwise_eraseC (hP : ElseBwdD (simEnv B)) {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {i : Nat} {ri : Rule} {v : Value}
    (hrel : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules))
    (hi : rules[i]? = some ri) (hel : hasElse ri = true)
    (hF : FiredD (simEnv B) "Step_read" [] i v) (h : Sim.otherwiseAt (simEnv B) "Step_read" [] i v) :
    Sim.otherwiseAt (simEnv B) "Step_read" [] i (Round8.CodeErase.Swap.eraseC v) := by
  refine otherwiseAt_map (fun _ _ _ => eraseC_pair) vHead_eraseC hF ?_ h
  intro j hj ps' op' t' rules' ri' rj hrel' hi' hrj hd
  rw [hrel] at hrel'
  cases hrel'
  rw [hi] at hi'
  cases hi'
  exact hP (i, j) (elsePairs_mem_sim hrel hi hel hj hrj hd)

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
