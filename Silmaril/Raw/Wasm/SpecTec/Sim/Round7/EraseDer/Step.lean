module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseDer.QCB
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseDer.CheckStep

/-!
# Round 7, moving derivations across erasure: the relation `Step` (unrefined)

`stepFwd`, `stepBwd`: SpecTec's `Step` commutes with erasure on the swap set, given that the four
rules using an excluded name (`excNames`) do (`RuleFwd`, `RuleBwd`).

`Step` is not in the checked part, so the generic transfer (`dderivesB_fwd`) does not apply to it
as a whole. Its rules are handled one instance at a time, by structural recursion on the
derivation:

* the mode analysis (`Round7.EraseAll.aiOn_ruleK`) does not read relation names, so it runs on
  the premises with `Step` renamed to `Step_read` (`rnS`, `ruleK_rnS`), where the evaluator-level
  hypotheses at `grB` apply; a `Step` premise's fact (its value is in the swap set when its input
  is) comes from the recursion;
* a `Step` premise goes across by the recursion; every other premise is checked at `grB`
  (`xStepOk_fixed`) and goes across by the generic transfers at `grB` (`dpremB_AIG`,
  `dpremB_fwd`/`dpremB_bwd`), with `otherwise` read by `otherwiseAtB_erase_iff` at `grB`;
* `Step` has no `otherwise` premise, so its own `otherwise` reading never matters
  (`dpremB_noElse`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (DDerivesBQ DPremBQ QuantsP Hyps xPrem xExp xArgs
  eraseP grB gdB InAI AIOn DefsG PremFactQ defsG_empty defsG_bindVals ai_eval_on aiOn_ruleK)
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (tyA TypsOk typsOk_empty typsOk_of_typs)
open Silmaril.Wasm.SpecTec.Sim.Round7.Transfer (bindParams_nil)
open Silmaril.Wasm.SpecTec.Sim.Round7.Determ (premDetOk fvIn detFacts premDetOk_rulePr quantNames
  premStep modeK ruleK)
open Round6.Reading (DDerivesB DPremB conclAlts otherwiseB)

variable {Q : Value → Prop} {B : Builtins}

/-! ## The mode check does not read relation names -/

/-- Rename a `Step` premise to a `Step_read` premise. -/
def rnS : Prem → Prem
  | .rulePr x args op e => .rulePr (if x == "Step" then "Step_read" else x) args op e
  | pr => pr

theorem premStep_rnS (K : List IL.Id) (pr : Prem) : premStep K (rnS pr) = premStep K pr := by
  cases pr with
  | rulePr x args op e =>
    simp only [rnS]
    split
    all_goals cases e <;> try simp [premStep]
    all_goals (rename_i es; cases es <;> rfl)
  | _ => rfl

theorem modeK_rnS (prems : List Prem) : ∀ (n : Nat) (K : List IL.Id),
    modeK (prems.map rnS) n K = modeK prems n K
  | 0, _ => rfl
  | n + 1, K => by
    simp only [modeK, List.flatMap_map, premStep_rnS]
    exact modeK_rnS prems n _

theorem ruleK_rnS (qs : List Param) (e : Exp) (prems : List Prem) :
    ruleK qs e (prems.map rnS) = ruleK qs e prems :=
  modeK_rnS prems 3 _

theorem premFactQ_rnS (env : Env) (ρ : VarEnv) (pr : Prem) :
    PremFactQ Q env ρ (rnS pr) = PremFactQ Q env ρ pr := by
  cases pr <;> rfl

theorem xPrem_rnS {pr : Prem} (h : xPremS pr = true) : xPrem grB gdB (rnS pr) = true := by
  cases pr with
  | rulePr x args op e =>
    by_cases hx : x = "Step"
    · subst hx
      simp only [xPremS, beq_self_eq_true, ite_true, Bool.and_eq_true] at h
      simp [rnS, xPrem, h.1, h.2, grB]
    · have hx' : (x == "Step") = false := by simpa using hx
      simp only [xPremS, hx', Bool.false_eq_true, ite_false] at h
      simpa [rnS, hx'] using h
  | _ => simp only [xPremS, Bool.and_eq_true] at h; exact h.1

/-! ## Premises without `otherwise` -/

theorem dpremB_noElse {env : Env} {O : ElseI} {els els' : Prop} :
    ∀ {ρ : VarEnv} {pr : Prem}, noElseP pr = true → DPremB env O els ρ pr → DPremB env O els' ρ pr
  | _, _, _, .ifPr h => .ifPr h
  | _, _, hn, .elsePr _ => by simp [noElseP] at hn
  | _, _, _, .letPr h₂ h₁ => .letPr h₂ h₁
  | _, _, _, .rulePr ha he hd => .rulePr ha he hd
  | _, _, _, .iterOptNone hd hne hall => .iterOptNone hd hne hall
  | _, .iterPr _ _, hn, .iterOptSome hd hne hs hp => .iterOptSome hd hne hs (dpremB_noElse hn hp)
  | _, .iterPr _ _, hn, .iterList hit hd hne hl hk hp =>
    .iterList hit hd hne hl hk fun r hr => dpremB_noElse hn (hp r hr)
  | _, .iterPr _ _, hn, .iterListN hd he hk hl hlen hp =>
    .iterListN hd he hk hl hlen fun r hr => dpremB_noElse hn (hp r hr)
termination_by _ pr => pr

/-! ## The facts about a rule of `Step` -/

/-- What the kernel checks say about a rule of `Step` outside `excNames`. -/
structure SFacts (ps qs : List Param) (e : Exp) (prems : List Prem) : Prop where
  params : ps = []
  prems : ∀ pr ∈ prems, xPremS pr = true ∧ varsIn (quantNames qs) (freePrem pr) = true
  alts : ∀ e' ∈ conclAlts e, xExp grB gdB e' = true ∧ varsIn (quantNames qs) (freeExp e') = true
  quants : ∀ y t, Param.expP y t ∈ qs →
    xTy TypAgree.tyB t = true ∧ varsIn (quantNames qs) (freeTyp t) = true

theorem step_reach : (0, "Step") ∈ Script.stepReach := by decide

theorem sFacts {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i : Nat}
    {nm : IL.Id} {qs : List Param} {e : Exp} {prems : List Prem}
    (hrel : (utf8Env B).findRel? "Step" = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e prems)) (hnm : nm ∉ excNames) :
    SFacts ps qs e prems := by
  have hr : Rule.ruleD nm qs op e prems ∈ rules := List.mem_of_getElem? hrule
  have hrel' := hrel
  rw [findRel?_utf8Env] at hrel'
  have hF := detFacts step_reach hrel' hrule
  have hm := EraseAll.mem_rels_of_findRel' hrel'
  obtain ⟨d', hd', hm'⟩ := EraseAll.mem_relsOfDefs hm
  have hS := List.all_eq_true.1 (List.all_eq_true.1 xStepOk_fixed d' hd') _ hm'
  simp only [bne_self_eq_false, Bool.false_or, List.all_eq_true] at hS
  have hS' := hS _ hr
  have hnm' : excNames.contains nm = false := by simpa using hnm
  simp only [xStepRule, hnm', Bool.false_or, Bool.and_eq_true, List.all_eq_true] at hS'
  have hreach' : Script.stepReach.contains (0, "Step") = true := List.contains_iff_mem.2 step_reach
  have hc := List.all_eq_true.1 closedRels_fixed _ hm
  simp only [hreach', Bool.not_true, Bool.false_or] at hc
  have hcl := List.all_eq_true.1 hc _ hr
  simp only [ruleClosed, Bool.and_eq_true, List.all_eq_true] at hcl
  have hq := List.all_eq_true.1 xRelQuants_fixed _ hm
  simp only [hreach', Bool.not_true, Bool.false_or, List.all_eq_true] at hq
  have hq' := hq _ hr
  simp only [List.all_eq_true] at hq'
  refine ⟨hF.params, fun pr hpr => ⟨hS'.2 pr hpr, hcl.1.2 pr hpr⟩,
    fun e' he' => ⟨hS'.1 e' he', hcl.1.1 e' he'⟩, fun y ty hy => ⟨?_, ?_⟩⟩
  · simpa using hq' _ hy
  · simpa using hcl.2 _ hy

/-! ## Inputs of `Step` premises -/

theorem inAI_of_stepPrem {gr gd : String → Bool} {P : Value → Prop} {env : Env}
    (H : Hyps P gr gd env) {ρ : VarEnv} {K : List IL.Id} {x : IL.Id} {args : List Arg}
    {op : MixopS} {e : Exp} {w : Value} (hD : DefsG gd ρ) (hxe : xExp gr gd e = true)
    (hK : AIOn P ρ K) (hok : premDetOk K (.rulePr x args op e) = true) (he : EvalExp env ρ e w) :
    InAI P w := by
  obtain ⟨a, rest, rfl, hfv⟩ := premDetOk_rulePr hok
  have hxa : xExp gr gd a = true := by
    simp only [xExp, EraseAll.xExps, Bool.and_eq_true] at hxe
    exact hxe.1
  obtain ⟨va, vs, rfl, ha⟩ := Determ.evalExp_tupE_cons he
  have hva : AllIn P va := ai_eval_on H hD hxa hK hfv ha
  intro a' r' heq
  cases heq
  exact hva

theorem xPremS_step {args : List Arg} {op : MixopS} {e : Exp}
    (h : xPremS (.rulePr "Step" args op e) = true) :
    xArgs grB gdB args = true ∧ xExp grB gdB e = true := by
  simpa [xPremS] using h

theorem xPremS_other {x : IL.Id} {args : List Arg} {op : MixopS} {e : Exp} (hx : x ≠ "Step")
    (h : xPremS (.rulePr x args op e) = true) : xPrem grB gdB (.rulePr x args op e) = true := by
  have hx' : (x == "Step") = false := by simpa using hx
  simpa [xPremS, hx'] using h

theorem xPremS_gen {pr : Prem} (hpr : ∀ x args op e, pr ≠ .rulePr x args op e)
    (h : xPremS pr = true) : xPrem grB gdB pr = true ∧ noElseP pr = true := by
  cases pr with
  | rulePr x args op e => exact absurd rfl (hpr x args op e)
  | _ => simpa [xPremS] using h

/-! ## The forward direction -/

section Fwd

set_option linter.unusedSectionVars false

variable (H : Hyps Q grB gdB (utf8Env B)) (H' : Hyps (EImg Q) grB gdB (utf8Env B))
  (hT : TypFwd Q gdB (utf8Env B)) (hTb : TypBwd Q gdB (utf8Env B)) (hQA : ∀ r, Q r → AllIn Q r)
include H H' hT hTb hQA

/-- **A checked premise without `otherwise` goes to the erased side**, through the transfers at
`grB`. -/
theorem premFwdGen {els : Prop} {ρ : VarEnv} {pr : Prem} (hX : xPrem grB gdB pr = true)
    (hne : noElseP pr = true) (h : DPremB (utf8Env B) (otherwiseB (utf8Env B)) els ρ pr) :
    PremFactQ Q (utf8Env B) ρ pr ∧ ∀ {K : List IL.Id} {ρ' : VarEnv} {els' : Prop},
      premDetOk K pr = true → AIOn Q ρ K → DefsG gdB ρ → ErRel Q gdB (freePrem pr) ρ ρ' →
      DPremB (utf8Env B) (otherwiseB (utf8Env B)) els' ρ' pr := by
  refine ⟨dpremB_factQG gFacts_B H hX h, fun hok hK hD hR => ?_⟩
  have h₀ : DPremB (utf8Env B) (otherwiseB (utf8Env B)) False ρ pr := dpremB_noElse hne h
  have hQ := dpremB_AIG gFacts_B H hok hK hD hX id h₀
  refine dpremB_fwd H gFacts_B.rf hT (O₁ := ElseAIg grB Q (otherwiseB (utf8Env B)))
    (fun x args i v hO => ?_) hX hR False.elim hQ
  exact (otherwiseAtB_erase_iff gFacts_B H H' hT hTb hQA hO.2.2 i v hO.2.1 args).1 hO.1

variable (hX : ∀ nm ∈ excNames, RuleFwd Q (utf8Env B) nm)
include hX

mutual
/-- **`Step` goes to the erased side** on the swap set. -/
theorem stepFwd : ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}, x = "Step" →
    InAI Q v → DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op args v →
    DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op (args.map eraseA) (eraseV v) ∧
      AllIn Q v
  | x, _, args, v, hxs, hin, .rule (σ := σ) (ρ₀ := ρ₀) (qs := qs) (ps := ps) (nm := nm)
      (prems := prems) (i := i) hrel hrule halt hps hq he hp => by
    have hrelS : (utf8Env B).findRel? "Step" = some _ := hxs ▸ hrel
    have hrel' := hrelS
    rw [findRel?_utf8Env] at hrel'
    have hFd := detFacts step_reach hrel' hrule
    have hargs : args = [] := (bindParams_nil_args (hFd.params ▸ hps)).1
    have hρ : ρ₀ = VarEnv.empty := (bindParams_nil_args (hFd.params ▸ hps)).2
    have hpar : bindParams VarEnv.empty ps (args.map eraseA) = some ρ₀ := by
      rw [hargs]; rw [hargs] at hps; exact hps
    by_cases hnm : nm ∈ excNames
    · obtain ⟨hv, σ', hq', he', hp'⟩ := hX nm hnm hrelS hrule halt (hρ ▸ hq) (hρ ▸ he)
        (by subst hρ hxs hargs; exact hp) hin
      refine ⟨.rule (σ := σ') hrel hrule halt hpar (hρ ▸ hq') (hρ ▸ he') ?_, hv⟩
      subst hρ hxs hargs
      exact hp'
    have hS := sFacts hrelS hrule hnm
    have hD : DefsG gdB (ρ₀.bindVals σ) := hρ ▸ defsG_bindVals defsG_empty σ
    have hT0 : TypsOk tyA (ρ₀.bindVals σ) := hρ ▸ typsOk_of_typs (typsOk_empty tyA) rfl
    obtain ⟨-, hqK, hfvK, hpK⟩ := hFd.concl _ halt
    have hK₀ := aiOn_ruleK H hD hT0 hq he hin (prems := prems.map rnS)
      (fun pr hpr => by
        obtain ⟨p, hp', rfl⟩ := List.mem_map.1 hpr
        exact xPrem_rnS (hS.prems p hp').1)
      (fun pr hpr => by
        obtain ⟨p, hp', rfl⟩ := List.mem_map.1 hpr
        rw [premFactQ_rnS]
        exact (premFwdS (hS.prems p hp').1 (hp p hp')).1)
    rw [ruleK_rnS] at hK₀
    have hxq : QuantsP (AllIn Q) (ρ₀.bindVals σ) qs := fun y _ w hy hw =>
      hK₀ y (List.contains_iff_mem.1 (List.all_eq_true.1 hqK y (List.mem_filterMap.2 ⟨_, hy, rfl⟩)))
        w hw
    have hR : ∀ S : Sets, varsIn (quantNames qs) S = true →
        ErRel Q gdB S (ρ₀.bindVals σ) (ρ₀.bindVals (σ.map eraseP)) := by
      intro S hS'
      subst hρ
      exact erRel_inst (ai_of_varsIn hxq hS')
    obtain ⟨hxe, hfe⟩ := hS.alts _ halt
    refine ⟨.rule (σ := σ.map eraseP) hrel hrule halt hpar (fun y ty hy => ?_)
      (evalExp_fwd H (hR _ hfe) hxe he).1 fun pr hpr => ?_,
      ai_eval_on H hD hxe hK₀ hfvK he⟩
    · obtain ⟨w, hw, hty⟩ := hq y ty hy
      obtain ⟨ht, hft⟩ := hS.quants y ty hy
      refine ⟨eraseV w, ?_, hT _ _ _ _ (hR _ hft) rfl (by subst hρ; rfl) (by subst hρ; rfl) rfl rfl
        ht (hxq y ty w hy hw) hty⟩
      have h₁ := hρ ▸ findVal?_inst σ y
      rw [h₁, hw]; rfl
    · exact (premFwdS (hS.prems pr hpr).1 (hp pr hpr)).2 (hpK pr hpr) hK₀ hD
        (hR _ (hS.prems pr hpr).2)
termination_by structural _ _ _ _ _ _ hd => hd

/-- **A premise of `Step` goes to the erased side**, with its fact for the mode analysis. -/
theorem premFwdS : ∀ {els : Prop} {ρ : VarEnv} {pr : Prem}, xPremS pr = true →
    DPremB (utf8Env B) (otherwiseB (utf8Env B)) els ρ pr →
    PremFactQ Q (utf8Env B) ρ pr ∧ ∀ {K : List IL.Id} {ρ' : VarEnv} {els' : Prop},
      premDetOk K pr = true → AIOn Q ρ K → DefsG gdB ρ → ErRel Q gdB (freePrem pr) ρ ρ' →
      DPremB (utf8Env B) (otherwiseB (utf8Env B)) els' ρ' pr
  | els, _, .rulePr x args op e, hXp, .rulePr (avs := avs) (w := w) ha he hd => by
    by_cases hx : x = "Step"
    · obtain ⟨hxa, hxe⟩ := xPremS_step (hx ▸ hXp)
      refine ⟨⟨w, he, fun hin => (stepFwd hx hin hd).2⟩, fun hok hK hD hR => ?_⟩
      have hin := inAI_of_stepPrem H hD hxe hK hok he
      exact .rulePr (evalArgs_fwd H (hR.mono (sub_rule_args _ args op e)) hxa ha).1
        (evalExp_fwd H (hR.mono (sub_rule_exp _ args op e)) hxe he).1 (stepFwd hx hin hd).1
    · exact premFwdGen H H' hT hTb hQA (xPremS_other hx hXp) rfl (.rulePr (els := els) ha he hd)
  | _, _, .ifPr _, hXp, h@(.ifPr _) => by
    obtain ⟨h₁, h₂⟩ := xPremS_gen (by intros; simp) hXp
    exact premFwdGen H H' hT hTb hQA h₁ h₂ h
  | _, _, .elsePr, hXp, .elsePr _ => by simp [xPremS, xPrem, noElseP] at hXp
  | _, _, .letPr _ _, hXp, h@(.letPr _ _) => by
    obtain ⟨h₁, h₂⟩ := xPremS_gen (by intros; simp) hXp
    exact premFwdGen H H' hT hTb hQA h₁ h₂ h
  | _, _, .iterPr _ _, hXp, h@(.iterOptNone _ _ _) => by
    obtain ⟨h₁, h₂⟩ := xPremS_gen (by intros; simp) hXp
    exact premFwdGen H H' hT hTb hQA h₁ h₂ h
  | _, _, .iterPr _ _, hXp, h@(.iterOptSome _ _ _ _) => by
    obtain ⟨h₁, h₂⟩ := xPremS_gen (by intros; simp) hXp
    exact premFwdGen H H' hT hTb hQA h₁ h₂ h
  | _, _, .iterPr _ _, hXp, h@(.iterList _ _ _ _ _ _) => by
    obtain ⟨h₁, h₂⟩ := xPremS_gen (by intros; simp) hXp
    exact premFwdGen H H' hT hTb hQA h₁ h₂ h
  | _, _, .iterPr _ _, hXp, h@(.iterListN _ _ _ _ _ _) => by
    obtain ⟨h₁, h₂⟩ := xPremS_gen (by intros; simp) hXp
    exact premFwdGen H H' hT hTb hQA h₁ h₂ h
termination_by structural _ _ _ _ hd => hd
end

end Fwd

/-! ## The backward direction -/

section Bwd

set_option linter.unusedSectionVars false

variable (H : Hyps Q grB gdB (utf8Env B)) (H' : Hyps (EImg Q) grB gdB (utf8Env B))
  (hT : TypFwd Q gdB (utf8Env B)) (hTb : TypBwd Q gdB (utf8Env B)) (hQA : ∀ r, Q r → AllIn Q r)
include H H' hT hTb hQA

/-- **A checked premise without `otherwise` comes back from the erased side**, through the
transfers at `grB`. -/
theorem premBwdGen {els' : Prop} {ρ' : VarEnv} {pr : Prem} (hX : xPrem grB gdB pr = true)
    (hne : noElseP pr = true) (h : DPremB (utf8Env B) (otherwiseB (utf8Env B)) els' ρ' pr) :
    PremFactQ (EImg Q) (utf8Env B) ρ' pr ∧ ∀ {K : List IL.Id} {ρ : VarEnv} {els : Prop},
      premDetOk K pr = true → AIOn (EImg Q) ρ' K → DefsG gdB ρ' → ErRel Q gdB (freePrem pr) ρ ρ' →
      DPremB (utf8Env B) (otherwiseB (utf8Env B)) els ρ pr := by
  refine ⟨dpremB_factQG gFacts_B H' hX h, fun hok hK hD hR => ?_⟩
  have h₀ : DPremB (utf8Env B) (otherwiseB (utf8Env B)) False ρ' pr := dpremB_noElse hne h
  have hQ := dpremB_AIG gFacts_B H' hok hK hD hX id h₀
  refine dpremB_bwd H gFacts_B.rf hTb hQA (O₂ := ElseAIg grB (EImg Q) (otherwiseB (utf8Env B)))
    (fun y as₀ i u hO has hu => ?_) hX hR False.elim hQ
  subst has
  obtain ⟨hu₁, hu₂⟩ := unerase_eImg hQA u hu
  refine (otherwiseAtB_erase_iff gFacts_B H H' hT hTb hQA hO.2.2 i _ (inAI_of_allIn hu₁) []).2 ?_
  rw [hu₂]; exact hO.1

variable (hX : ∀ nm ∈ excNames, RuleBwd Q (utf8Env B) nm)
include hX

mutual
/-- **`Step` comes back from the erased side** on the erased swap set. -/
theorem stepBwd : ∀ {x : IL.Id} {op : MixopS} {args' : List ArgV} {v' : Value}, x = "Step" →
    InAI (EImg Q) v' → DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op args' v' →
    args' = [] ∧ DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op [] (unerase Q v') ∧
      AllIn (EImg Q) v'
  | x, _, args', v', hxs, hin, .rule (σ := σ') (ρ₀ := ρ₀) (qs := qs) (ps := ps) (nm := nm)
      (prems := prems) (i := i) hrel hrule halt hps hq he hp => by
    have hrelS : (utf8Env B).findRel? "Step" = some _ := hxs ▸ hrel
    have hrel' := hrelS
    rw [findRel?_utf8Env] at hrel'
    have hFd := detFacts step_reach hrel' hrule
    have hargs : args' = [] := (bindParams_nil_args (hFd.params ▸ hps)).1
    have hρ : ρ₀ = VarEnv.empty := (bindParams_nil_args (hFd.params ▸ hps)).2
    have hpar : bindParams VarEnv.empty ps [] = some ρ₀ := by
      rw [hargs] at hps; exact hps
    by_cases hnm : nm ∈ excNames
    · obtain ⟨hv, σ, hq', he', hp'⟩ := hX nm hnm hrelS hrule halt (hρ ▸ hq) (hρ ▸ he)
        (by subst hρ hxs hargs; exact hp) hin
      refine ⟨hargs, .rule (σ := σ) hrel hrule halt hpar (hρ ▸ hq') (hρ ▸ he') ?_, hv⟩
      subst hρ hxs hargs
      exact hp'
    have hS := sFacts hrelS hrule hnm
    have hD : DefsG gdB (ρ₀.bindVals σ') := hρ ▸ defsG_bindVals defsG_empty σ'
    have hT0 : TypsOk tyA (ρ₀.bindVals σ') := hρ ▸ typsOk_of_typs (typsOk_empty tyA) rfl
    obtain ⟨-, hqK, hfvK, hpK⟩ := hFd.concl _ halt
    have hK₀ := aiOn_ruleK H' hD hT0 hq he hin (prems := prems.map rnS)
      (fun pr hpr => by
        obtain ⟨p, hp', rfl⟩ := List.mem_map.1 hpr
        exact xPrem_rnS (hS.prems p hp').1)
      (fun pr hpr => by
        obtain ⟨p, hp', rfl⟩ := List.mem_map.1 hpr
        rw [premFactQ_rnS]
        exact (premBwdS (hS.prems p hp').1 (hp p hp')).1)
    rw [ruleK_rnS] at hK₀
    have hxq : QuantsP (AllIn (EImg Q)) (ρ₀.bindVals σ') qs := fun y _ w hy hw =>
      hK₀ y (List.contains_iff_mem.1 (List.all_eq_true.1 hqK y (List.mem_filterMap.2 ⟨_, hy, rfl⟩)))
        w hw
    have hR : ∀ S : Sets, varsIn (quantNames qs) S = true →
        ErRel Q gdB S (ρ₀.bindVals (σ'.map (uneraseP Q))) (ρ₀.bindVals σ') := by
      intro S hS'
      subst hρ
      exact erRel_unerase hQA (ai_of_varsIn hxq hS')
    obtain ⟨hxe, hfe⟩ := hS.alts _ halt
    obtain ⟨v, hv, hve, hva⟩ := evalExp_bwd H (hR _ hfe) hxe he
    have hvu : unerase Q v' = v := hve ▸ unerase_eraseV H.inj v hva
    refine ⟨hargs, .rule (σ := σ'.map (uneraseP Q)) hrel hrule halt hpar (fun y ty hy => ?_)
      (hvu ▸ hv) fun pr hpr => ?_, ai_eval_on H' hD hxe hK₀ hfvK he⟩
    · obtain ⟨w', hw', hty⟩ := hq y ty hy
      obtain ⟨ht, hft⟩ := hS.quants y ty hy
      obtain ⟨hu₁, hu₂⟩ := unerase_eImg hQA w' (hxq y ty w' hy hw')
      refine ⟨unerase Q w', ?_, hTb _ _ _ _ (hR _ hft) rfl (by subst hρ; rfl) (by subst hρ; rfl)
        rfl rfl ht hu₁ (by rw [hu₂]; exact hty)⟩
      have h₁ := findVal?_uninst (Q := Q) σ' y
      rw [← hρ] at h₁
      rw [h₁, hw']; rfl
    · exact (premBwdS (hS.prems pr hpr).1 (hp pr hpr)).2 (hpK pr hpr) hK₀ hD
        (hR _ (hS.prems pr hpr).2)
termination_by structural _ _ _ _ _ _ hd => hd

/-- **A premise of `Step` comes back from the erased side**, with its fact for the mode
analysis. -/
theorem premBwdS : ∀ {els' : Prop} {ρ' : VarEnv} {pr : Prem}, xPremS pr = true →
    DPremB (utf8Env B) (otherwiseB (utf8Env B)) els' ρ' pr →
    PremFactQ (EImg Q) (utf8Env B) ρ' pr ∧ ∀ {K : List IL.Id} {ρ : VarEnv} {els : Prop},
      premDetOk K pr = true → AIOn (EImg Q) ρ' K → DefsG gdB ρ' → ErRel Q gdB (freePrem pr) ρ ρ' →
      DPremB (utf8Env B) (otherwiseB (utf8Env B)) els ρ pr
  | els', _, .rulePr x args op e, hXp, .rulePr (avs := avs') (w := w') ha he hd => by
    by_cases hx : x = "Step"
    · obtain ⟨hxa, hxe⟩ := xPremS_step (hx ▸ hXp)
      refine ⟨⟨w', he, fun hin => (stepBwd hx hin hd).2.2⟩, fun hok hK hD hR => ?_⟩
      have hin := inAI_of_stepPrem H' hD hxe hK hok he
      obtain ⟨hnil, hd', -⟩ := stepBwd hx hin hd
      obtain ⟨avs, havs, havse, -⟩ := evalArgs_bwd H (hR.mono (sub_rule_args _ args op e)) hxa ha
      obtain ⟨w, hw, hwe, hwa⟩ := evalExp_bwd H (hR.mono (sub_rule_exp _ args op e)) hxe he
      have havs' : avs = [] := by
        rw [hnil] at havse; exact List.map_eq_nil_iff.1 havse
      have hwu : unerase Q w' = w := hwe ▸ unerase_eraseV H.inj w hwa
      exact .rulePr (havs' ▸ havs) (hwu ▸ hw) hd'
    · exact premBwdGen H H' hT hTb hQA (xPremS_other hx hXp) rfl (.rulePr (els := els') ha he hd)
  | _, _, .ifPr _, hXp, h@(.ifPr _) => by
    obtain ⟨h₁, h₂⟩ := xPremS_gen (by intros; simp) hXp
    exact premBwdGen H H' hT hTb hQA h₁ h₂ h
  | _, _, .elsePr, hXp, .elsePr _ => by simp [xPremS, xPrem, noElseP] at hXp
  | _, _, .letPr _ _, hXp, h@(.letPr _ _) => by
    obtain ⟨h₁, h₂⟩ := xPremS_gen (by intros; simp) hXp
    exact premBwdGen H H' hT hTb hQA h₁ h₂ h
  | _, _, .iterPr _ _, hXp, h@(.iterOptNone _ _ _) => by
    obtain ⟨h₁, h₂⟩ := xPremS_gen (by intros; simp) hXp
    exact premBwdGen H H' hT hTb hQA h₁ h₂ h
  | _, _, .iterPr _ _, hXp, h@(.iterOptSome _ _ _ _) => by
    obtain ⟨h₁, h₂⟩ := xPremS_gen (by intros; simp) hXp
    exact premBwdGen H H' hT hTb hQA h₁ h₂ h
  | _, _, .iterPr _ _, hXp, h@(.iterList _ _ _ _ _ _) => by
    obtain ⟨h₁, h₂⟩ := xPremS_gen (by intros; simp) hXp
    exact premBwdGen H H' hT hTb hQA h₁ h₂ h
  | _, _, .iterPr _ _, hXp, h@(.iterListN _ _ _ _ _ _) => by
    obtain ⟨h₁, h₂⟩ := xPremS_gen (by intros; simp) hXp
    exact premBwdGen H H' hT hTb hQA h₁ h₂ h
termination_by structural _ _ _ _ hd => hd
end

end Bwd

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
