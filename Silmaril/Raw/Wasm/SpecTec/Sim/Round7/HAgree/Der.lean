module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HAgree.TypEq

/-!
# Round 7, memory SIMD: derivations of `GoodRel` relations move from `simEnv B₁` to `simEnv B₂` (unrefined)

For builtins that agree off `$vbytes_`:

* `premW_agree`: a premise read through `PremW` holds at `B₂` if it holds at `B₁`, when its syntax
  is `GoodEvs`, its relations are read alike on `GoodRel` (`hD`) and its `otherwise` reading is
  carried over where the premise has one (`elseFree`);
* `dderives_agree`, `dderivesB_agree`: a `DDerives` (`DDerivesB`) derivation of a `GoodRel`
  relation at `B₁` is one at `B₂`, given `otherwise` readings related on `GoodRel` relations
  (`hO`). The proof is by structural recursion on the derivation. At a rule instance the scope is
  `VarEnv.empty.bindVals σ` (the relations `Step` reaches have no parameters, `relFacts_of_find`);
  the quantifier types and conclusion alternatives are `RG` (`quant_rg`, `alt_rg`), so typing
  transfers by `quantsOk_iff` and the conclusion by `HAgree.evalExp_iff`; the premises are
  `GoodEvs` by `HAgree.goodRules`.
* `ruleBody_agree`, `ruleBodyB_agree`: one rule body, with relations read through any `D₁`, `D₂`
  related on `GoodRel`.

The template is `Raw/…/Round7/EraseDer/Fwd.lean`, which moves derivations across erasure; here the
values do not change, only the builtins.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Round7.VDecl (elseFree)
open Round7.Script (evRefs evTyp evExp evArg evArgs evPrem evPrems evParams evRule evIter
  evIterExp evDoms stepReach le_antisymm')
open Round7.VAgree (GoodRel)
open Round6.Reading (DDerivesB DPremB conclAlts RuleBodyB)

variable {B₁ B₂ : Builtins}

/-! ## Small facts -/

theorem evalDoms_iff (hB : AgreeOff B₁ B₂) {ρ : VarEnv} {ds : List Dom}
    {xvs : List (IL.Id × Value)} (hD : DefsOk ρ) (hG : GoodEvs (evDoms ds)) :
    EvalDoms (simEnv B₁) ρ ds xvs ↔ EvalDoms (simEnv B₂) ρ ds xvs := by
  have h : ∀ n, evalDoms n (simEnv B₁) ρ ds = evalDoms n (simEnv B₂) ρ ds := fun n =>
    le_antisymm' ((agreeAt B₁ B₂ hB n).doms ρ ds hD hG)
      ((agreeAt B₂ B₁ (agreeOff_symm hB) n).doms ρ ds hD hG)
  simp only [EvalDoms, h]

theorem bindParams_nil {ρ ρ' : VarEnv} {args : List ArgV} (h : bindParams ρ [] args = some ρ') :
    args = [] ∧ ρ' = ρ := by
  cases args with
  | nil => exact ⟨rfl, (Option.some.inj h).symm⟩
  | cons _ _ => simp [bindParams] at h

theorem scope_ok (σ : List (IL.Id × Value)) :
    DefsOk (VarEnv.empty.bindVals σ) ∧ TypsG (VarEnv.empty.bindVals σ) :=
  ⟨defsOk_bindVals defsOk_empty σ, typsG_bindVals typsG_empty σ⟩

/-- The parts of a `GoodEvs` rule premise. -/
theorem goodEvs_rulePr {x : IL.Id} {args : List Arg} {op : MixopS} {e : Exp}
    (h : GoodEvs (evPrem (.rulePr x args op e))) :
    GoodRel x ∧ GoodEvs (evArgs args) ∧ GoodEvs (evExp e) := by
  simpa only [evPrem, goodEvs_cons, goodEv_ref0, goodEvs_append] using h

/-- The parts of a `GoodEvs` iterated premise. -/
theorem goodEvs_iterPr {pr : Prem} {it : Iter} {ds : List Dom}
    (h : GoodEvs (evPrem (.iterPr pr (.mk it ds)))) :
    GoodEvs (evPrem pr) ∧ GoodEvs (evIter it) ∧ GoodEvs (evDoms ds) := by
  simpa only [evPrem, evIterExp, goodEvs_append] using h

theorem elseFree_iter {pr : Prem} {ie : IterExp} : elseFree (.iterPr pr ie) = elseFree pr := rfl

/-! ## One premise, through an interpretation -/

/-- **A `PremW` premise moves from `B₁` to `B₂`.** -/
theorem premW_agree (hB : AgreeOff B₁ B₂) {D₁ D₂ : Interp}
    (hD : ∀ x op args v, GoodRel x → (∀ w ∈ args, ArgOk w) → D₁ x op args v → D₂ x op args v) :
    ∀ {els₁ els₂ : Prop} {ρ : VarEnv} {pr : Prem}, DefsOk ρ → GoodEvs (evPrem pr) →
      (elseFree pr = false → els₁ → els₂) →
      PremW (simEnv B₁) D₁ els₁ ρ pr → PremW (simEnv B₂) D₂ els₂ ρ pr := by
  intro els₁ els₂ ρ pr hρ hG hels h
  induction h generalizing els₂ with
  | ifPr he => exact .ifPr ((evalExp_iff hB hρ hG).1 he)
  | elsePr h => exact .elsePr (hels rfl h)
  | letPr h₂ h₁ =>
    simp only [evPrem, goodEvs_append] at hG
    exact .letPr ((evalExp_iff hB hρ hG.2).1 h₂) ((evalExp_iff hB hρ hG.1).1 h₁)
  | rulePr ha he hd =>
    obtain ⟨hx, hga, hge⟩ := goodEvs_rulePr hG
    obtain ⟨n, hn⟩ := ha
    exact .rulePr ((evalArgs_iff hB hρ hga).1 ⟨n, hn⟩) ((evalExp_iff hB hρ hge).1 he)
      (hD _ _ _ _ hx (evalArgs_argOk hρ hga hn) hd)
  | iterOptNone hd hne hall =>
    obtain ⟨-, -, hgd⟩ := goodEvs_iterPr hG
    exact .iterOptNone ((evalDoms_iff hB hρ hgd).1 hd) hne hall
  | iterOptSome hd hne hs _ ih =>
    obtain ⟨hgp, -, hgd⟩ := goodEvs_iterPr hG
    exact .iterOptSome ((evalDoms_iff hB hρ hgd).1 hd) hne hs
      (ih (defsOk_bindVals hρ _) hgp hels)
  | iterList hit hd hne hl hlen _ ih =>
    obtain ⟨hgp, -, hgd⟩ := goodEvs_iterPr hG
    exact .iterList hit ((evalDoms_iff hB hρ hgd).1 hd) hne hl hlen
      fun r hr => ih r hr (defsOk_bindVals hρ _) hgp hels
  | iterListN hd he hk hl hlen _ ih =>
    obtain ⟨hgp, hgi, hgd⟩ := goodEvs_iterPr hG
    exact .iterListN ((evalDoms_iff hB hρ hgd).1 hd)
      ((evalExp_iff hB hρ (by simpa only [evIter] using hgi)).1 he) hk hl hlen
      fun r hr => ih r hr (defsOk_bindVals hρ _) hgp hels

/-- **One rule body moves from `B₁` to `B₂`**, for a parameter-free relation, when the rule's
quantifier types and conclusion are `RG` and its premises `GoodEvs`. -/
theorem ruleBody_agree (hB : AgreeOff B₁ B₂) {D₁ D₂ : Interp}
    (hD : ∀ x op args v, GoodRel x → (∀ w ∈ args, ArgOk w) → D₁ x op args v → D₂ x op args v)
    {els₁ els₂ : Prop} {args : List ArgV} {op : MixopS} {nm : IL.Id} {qs : List Param}
    {op' : MixopS} {e : Exp} {prems : List Prem} {v : Value}
    (hq : ∀ x t, Param.expP x t ∈ qs → RG (evTyp t)) (he : RG (evExp e))
    (hG : GoodEvs (evPrems prems)) (hels : prems.all elseFree = false → els₁ → els₂)
    (h : RuleBody (simEnv B₁) D₁ els₁ [] args op (.ruleD nm qs op' e prems) v) :
    RuleBody (simEnv B₂) D₂ els₂ [] args op (.ruleD nm qs op' e prems) v := by
  obtain ⟨hop, ρ₀, σ, hps, hQ, hE, hP⟩ := h
  have hρ : ρ₀ = VarEnv.empty := (bindParams_nil hps).2
  subst hρ
  have hs := scope_ok σ
  refine ⟨hop, VarEnv.empty, σ, hps, (quantsOk_iff hB hs.1 hs.2 hq).1 hQ,
    (evalExp_iff hB hs.1 (goodEvs_of_rg he)).1 hE, fun pr hpr => ?_⟩
  refine premW_agree hB hD hs.1 (goodEvs_prems hG pr hpr) (fun hf h₁ => hels ?_ h₁) (hP pr hpr)
  exact List.all_eq_false.2 ⟨pr, hpr, by simp [hf]⟩

/-- `ruleBody_agree` for `RuleBodyB`: every conclusion alternative is `RG`. -/
theorem ruleBodyB_agree (hB : AgreeOff B₁ B₂) {D₁ D₂ : Interp}
    (hD : ∀ x op args v, GoodRel x → (∀ w ∈ args, ArgOk w) → D₁ x op args v → D₂ x op args v)
    {els₁ els₂ : Prop} {args : List ArgV} {op : MixopS} {nm : IL.Id} {qs : List Param}
    {op' : MixopS} {e : Exp} {prems : List Prem} {v : Value}
    (hq : ∀ x t, Param.expP x t ∈ qs → RG (evTyp t)) (he : ∀ e' ∈ conclAlts e, RG (evExp e'))
    (hG : GoodEvs (evPrems prems)) (hels : prems.all elseFree = false → els₁ → els₂)
    (h : RuleBodyB (simEnv B₁) D₁ els₁ [] args op (.ruleD nm qs op' e prems) v) :
    RuleBodyB (simEnv B₂) D₂ els₂ [] args op (.ruleD nm qs op' e prems) v := by
  obtain ⟨e', he', hb⟩ := h
  exact ⟨e', he', ruleBody_agree hB hD hq (he e' he') hG hels hb⟩

/-! ## Derivations -/

section Der

set_option linter.unusedSectionVars false

variable (hB : AgreeOff B₁ B₂) {O₁ O₂ : ElseI}
  (hO : ∀ x args i v, GoodRel x → O₁ x args i v → O₂ x args i v)
include hB hO

mutual
/-- **A `DDerives` derivation of a `GoodRel` relation moves from `B₁` to `B₂`.** -/
theorem dderives_agree :
    ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}, GoodRel x →
      DDerives (simEnv B₁) O₁ x op args v → DDerives (simEnv B₂) O₂ x op args v
  | x, _, args, v, hx, .rule (σ := σ) (ρ₀ := ρ₀) (i := i) (qs := qs) (e := e) (prems := prems)
      (rules := rules) (ps := ps) hrel hrule hps hq he hp => by
    have hrel₂ := (findRel?_simEnv B₂ B₁ x).trans hrel
    have hF := relFacts_of_find hrel hx.1
    have hr : Rule.ruleD _ qs _ e prems ∈ rules := List.mem_of_getElem? hrule
    have hRF := hF.2 _ hr
    have hps0 : ps = [] := hF.1
    have hps' := hps
    rw [hps0] at hps'
    have hρ : ρ₀ = VarEnv.empty := (bindParams_nil hps').2
    have hs : DefsOk (ρ₀.bindVals σ) ∧ TypsG (ρ₀.bindVals σ) := hρ ▸ scope_ok σ
    have hGr : GoodEvs (evRule (.ruleD _ qs _ e prems)) := goodRules B₁ hx hrel _ hr
    have hGp : GoodEvs (evPrems prems) := by
      simp only [evRule, goodEvs_append] at hGr; exact hGr.2
    refine .rule hrel₂ hrule hps ((quantsOk_iff hB hs.1 hs.2 (quant_rg hRF)).1 hq)
      ((evalExp_iff hB hs.1 (goodEvs_of_rg (alt_rg hRF e List.mem_cons_self))).1
        he) fun pr hpr => ?_
    exact dprem_agree hs.1 (goodEvs_prems hGp pr hpr) (fun _ => hO _ _ _ _ hx) (hp pr hpr)
termination_by structural _ _ _ _ _ hd => hd

/-- **A `DPrem` premise moves from `B₁` to `B₂`.** -/
theorem dprem_agree :
    ∀ {els₁ els₂ : Prop} {ρ : VarEnv} {pr : Prem}, DefsOk ρ → GoodEvs (evPrem pr) →
      (elseFree pr = false → els₁ → els₂) →
      DPrem (simEnv B₁) O₁ els₁ ρ pr → DPrem (simEnv B₂) O₂ els₂ ρ pr
  | _, _, _, _, hρ, hG, _, .ifPr he => .ifPr ((evalExp_iff hB hρ hG).1 he)
  | _, _, _, _, _, _, hels, .elsePr h => .elsePr (hels rfl h)
  | _, _, _, .letPr e₁ e₂, hρ, hG, _, .letPr h₂ h₁ => by
    simp only [evPrem, goodEvs_append] at hG
    exact .letPr ((evalExp_iff hB hρ hG.2).1 h₂) ((evalExp_iff hB hρ hG.1).1 h₁)
  | _, _, _, .rulePr x args op e, hρ, hG, _, .rulePr ha he hd => by
    obtain ⟨hx, hga, hge⟩ := goodEvs_rulePr hG
    exact .rulePr ((evalArgs_iff hB hρ hga).1 ha) ((evalExp_iff hB hρ hge).1 he)
      (dderives_agree hx hd)
  | _, _, _, .iterPr pr (.mk _ ds), hρ, hG, _, .iterOptNone hd hne hall => by
    obtain ⟨-, -, hgd⟩ := goodEvs_iterPr hG
    exact .iterOptNone ((evalDoms_iff hB hρ hgd).1 hd) hne hall
  | _, _, _, .iterPr pr (.mk _ ds), hρ, hG, hels, .iterOptSome hd hne hs hp => by
    obtain ⟨hgp, -, hgd⟩ := goodEvs_iterPr hG
    exact .iterOptSome ((evalDoms_iff hB hρ hgd).1 hd) hne hs
      (dprem_agree (defsOk_bindVals hρ _) hgp hels hp)
  | _, _, _, .iterPr pr (.mk it ds), hρ, hG, hels, .iterList hit hd hne hl hlen hp => by
    obtain ⟨hgp, -, hgd⟩ := goodEvs_iterPr hG
    exact .iterList hit ((evalDoms_iff hB hρ hgd).1 hd) hne hl hlen
      fun r hr => dprem_agree (defsOk_bindVals hρ _) hgp hels (hp r hr)
  | _, _, _, .iterPr pr (.mk (.listN eₙ ido) ds), hρ, hG, hels,
      .iterListN hd he hk hl hlen hp => by
    obtain ⟨hgp, hgi, hgd⟩ := goodEvs_iterPr hG
    exact .iterListN ((evalDoms_iff hB hρ hgd).1 hd)
      ((evalExp_iff hB hρ (by simpa only [evIter] using hgi)).1 he) hk hl hlen
      fun r hr => dprem_agree (defsOk_bindVals hρ _) hgp hels (hp r hr)
termination_by structural _ _ _ _ _ _ _ hd => hd
end

mutual
/-- **A `DDerivesB` derivation of a `GoodRel` relation moves from `B₁` to `B₂`.** -/
theorem dderivesB_agree :
    ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}, GoodRel x →
      DDerivesB (simEnv B₁) O₁ x op args v → DDerivesB (simEnv B₂) O₂ x op args v
  | x, _, args, v, hx, .rule (σ := σ) (ρ₀ := ρ₀) (i := i) (qs := qs) (e := e) (e' := e')
      (prems := prems) (rules := rules) (ps := ps) hrel hrule halt hps hq he hp => by
    have hrel₂ := (findRel?_simEnv B₂ B₁ x).trans hrel
    have hF := relFacts_of_find hrel hx.1
    have hr : Rule.ruleD _ qs _ e prems ∈ rules := List.mem_of_getElem? hrule
    have hRF := hF.2 _ hr
    have hps0 : ps = [] := hF.1
    have hps' := hps
    rw [hps0] at hps'
    have hρ : ρ₀ = VarEnv.empty := (bindParams_nil hps').2
    have hs : DefsOk (ρ₀.bindVals σ) ∧ TypsG (ρ₀.bindVals σ) := hρ ▸ scope_ok σ
    have hGr : GoodEvs (evRule (.ruleD _ qs _ e prems)) := goodRules B₁ hx hrel _ hr
    have hGp : GoodEvs (evPrems prems) := by
      simp only [evRule, goodEvs_append] at hGr; exact hGr.2
    refine .rule hrel₂ hrule halt hps ((quantsOk_iff hB hs.1 hs.2 (quant_rg hRF)).1 hq)
      ((evalExp_iff hB hs.1 (goodEvs_of_rg (alt_rg hRF e' halt))).1 he) fun pr hpr => ?_
    exact dpremB_agree hs.1 (goodEvs_prems hGp pr hpr) (fun _ => hO _ _ _ _ hx) (hp pr hpr)
termination_by structural _ _ _ _ _ hd => hd

/-- **A `DPremB` premise moves from `B₁` to `B₂`.** -/
theorem dpremB_agree :
    ∀ {els₁ els₂ : Prop} {ρ : VarEnv} {pr : Prem}, DefsOk ρ → GoodEvs (evPrem pr) →
      (elseFree pr = false → els₁ → els₂) →
      DPremB (simEnv B₁) O₁ els₁ ρ pr → DPremB (simEnv B₂) O₂ els₂ ρ pr
  | _, _, _, _, hρ, hG, _, .ifPr he => .ifPr ((evalExp_iff hB hρ hG).1 he)
  | _, _, _, _, _, _, hels, .elsePr h => .elsePr (hels rfl h)
  | _, _, _, .letPr e₁ e₂, hρ, hG, _, .letPr h₂ h₁ => by
    simp only [evPrem, goodEvs_append] at hG
    exact .letPr ((evalExp_iff hB hρ hG.2).1 h₂) ((evalExp_iff hB hρ hG.1).1 h₁)
  | _, _, _, .rulePr x args op e, hρ, hG, _, .rulePr ha he hd => by
    obtain ⟨hx, hga, hge⟩ := goodEvs_rulePr hG
    exact .rulePr ((evalArgs_iff hB hρ hga).1 ha) ((evalExp_iff hB hρ hge).1 he)
      (dderivesB_agree hx hd)
  | _, _, _, .iterPr pr (.mk _ ds), hρ, hG, _, .iterOptNone hd hne hall => by
    obtain ⟨-, -, hgd⟩ := goodEvs_iterPr hG
    exact .iterOptNone ((evalDoms_iff hB hρ hgd).1 hd) hne hall
  | _, _, _, .iterPr pr (.mk _ ds), hρ, hG, hels, .iterOptSome hd hne hs hp => by
    obtain ⟨hgp, -, hgd⟩ := goodEvs_iterPr hG
    exact .iterOptSome ((evalDoms_iff hB hρ hgd).1 hd) hne hs
      (dpremB_agree (defsOk_bindVals hρ _) hgp hels hp)
  | _, _, _, .iterPr pr (.mk it ds), hρ, hG, hels, .iterList hit hd hne hl hlen hp => by
    obtain ⟨hgp, -, hgd⟩ := goodEvs_iterPr hG
    exact .iterList hit ((evalDoms_iff hB hρ hgd).1 hd) hne hl hlen
      fun r hr => dpremB_agree (defsOk_bindVals hρ _) hgp hels (hp r hr)
  | _, _, _, .iterPr pr (.mk (.listN eₙ ido) ds), hρ, hG, hels,
      .iterListN hd he hk hl hlen hp => by
    obtain ⟨hgp, hgi, hgd⟩ := goodEvs_iterPr hG
    exact .iterListN ((evalDoms_iff hB hρ hgd).1 hd)
      ((evalExp_iff hB hρ (by simpa only [evIter] using hgi)).1 he) hk hl hlen
      fun r hr => dpremB_agree (defsOk_bindVals hρ _) hgp hels (hp r hr)
termination_by structural _ _ _ _ _ _ _ hd => hd
end

end Der

end Silmaril.Wasm.SpecTec.Sim.Round7.HAgree
