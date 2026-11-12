module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HStep.Ctx

/-!
# Round 7, `BD`: the whole step moves across `HAgree.AgreeOff` under a `StepInvH` (unrefined)

A copy of `Raw/…/Round7/VDecl/Step.lean` (`VDecl.dderivesQ`) for builtins that agree off
`$vbytes_` and `$hostcall`, with `HAgree`'s lemmas for `VAgree`'s and `VDecl`'s. The changes:
`ctxPremOkH` for `ctxPremOk`; `HAgree.goodRule_step` (rules outside `HAgree.stepBad`) and
`HAgree.goodRule_read`; and two more excluded cases in the `Step` dispatch, rules 8 and 9, kept
silent by `StepInvH.step8`/`step9`. Kept unrefined, like the original.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HStep

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Round7.Script (evRefs evExp evArgs evPrem evPrems evRule stepReach)
open Round7.VAgree (GoodRel)
open Round7.VDecl (elseFree)
open HAgree (GoodEvs GoodRule DefsOk TypsG ArgOk AgreeOff agreeOff_symm defsOk_bindVals goodEvs_append
  goodEvs_prems evalExp_iff evalArgs_iff findRel?_simEnv rg_of_rgB rg_append goodEvs_of_rg
  goodEvs_rulePr relFacts_of_find scope_ok quantsOk_iff quant_rg alt_rg dprem_agree
  dderives_otherwise otherwiseAt_goodRel otherwiseAt_read read_mem_stepReach
  goodEvs_prems_of_rule bindParams_nil)

variable {B₁ B₂ : Builtins}

/-- The derivations `dderivesQ` covers: a `GoodRel` relation, or `Step`/`Step_read` at a `Q`
value. -/
def Cov (Q : Value → Prop) (x : IL.Id) (v : Value) : Prop :=
  GoodRel x ∨ ((x = "Step" ∨ x = "Step_read") ∧ Q v)

theorem ctxPrem_split {y : IL.Id} {args : List Arg} {op : MixopS} {e : Exp}
    (h : ctxPremOkH (.rulePr y args op e) = true) :
    ((y = "Step" ∨ y = "Step_read") ∧ GoodEvs (evArgs args) ∧ GoodEvs (evExp e)) ∨
      GoodEvs (evPrem (.rulePr y args op e)) := by
  simp only [ctxPremOkH, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨hy, hg⟩ | hg
  · have hg' := rg_append.1 (rg_of_rgB hg)
    exact .inl ⟨hy, goodEvs_of_rg hg'.1, goodEvs_of_rg hg'.2⟩
  · exact .inr (goodEvs_of_rg (rg_of_rgB hg))

theorem goodEvs_of_ctxPremOk {pr : Prem} (h : ctxPremOkH pr = true)
    (hn : ∀ y args op e, pr ≠ .rulePr y args op e) : GoodEvs (evPrem pr) := by
  cases pr with
  | rulePr y args op e => exact absurd rfl (hn y args op e)
  | _ => exact goodEvs_of_rg (rg_of_rgB h)

section Step

set_option linter.unusedSectionVars false

variable (hB : AgreeOff B₁ B₂) {Q : Value → Prop} (hQ : StepInvH Q)
include hB hQ

/-- The `otherwise` reading of `GoodRel` relations, as `dprem_agree` takes it. -/
theorem hO_goodRel : ∀ x args i v, GoodRel x →
    otherwise (simEnv B₁) x args i v → otherwise (simEnv B₂) x args i v :=
  fun _ args i w hy => otherwiseAt_goodRel hB hy args i w

/- The equation compiler needs more than the default recursion depth for `dpremQ`'s match. -/
set_option maxRecDepth 4000 in
mutual
/-- **A covered derivation moves from `B₁` to `B₂`.** -/
theorem dderivesQ :
    ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}, Cov Q x v →
      DDerives (simEnv B₁) (otherwise (simEnv B₁)) x op args v →
      DDerives (simEnv B₂) (otherwise (simEnv B₂)) x op args v
  | x, op, args, v, hx, .rule (σ := σ) (ρ₀ := ρ₀) (i := i) (qs := qs) (e := e) (prems := prems)
      (rules := rules) (ps := ps) (nm := nm) (t := t) hrel hrule hps hq he hp => by
    rcases hx with hg | ⟨hxs, hv⟩
    · exact dderives_otherwise hB hg (.rule hrel hrule hps hq he hp)
    have hreach : (0, x) ∈ stepReach := by
      rcases hxs with h | h
      · rw [h]; exact Round7.Script.step_mem_stepReach
      · rw [h]; exact read_mem_stepReach
    have hF := relFacts_of_find hrel hreach
    have hr : Rule.ruleD nm qs op e prems ∈ rules := List.mem_of_getElem? hrule
    have hRF := hF.2 _ hr
    have hps0 : ps = [] := hF.1
    have hps' := hps
    rw [hps0] at hps'
    have hρ : ρ₀ = VarEnv.empty := (bindParams_nil hps').2
    have hs : DefsOk (ρ₀.bindVals σ) ∧ TypsG (ρ₀.bindVals σ) := hρ ▸ scope_ok σ
    have hrel₂ := (findRel?_simEnv B₂ B₁ x).trans hrel
    have hq₂ := (quantsOk_iff hB hs.1 hs.2 (quant_rg hRF)).1 hq
    have he₂ := (evalExp_iff hB hs.1 (goodEvs_of_rg (alt_rg hRF e List.mem_cons_self))).1 he
    have hbody : RuleBody (simEnv B₁) (DDerives (simEnv B₁) (otherwise (simEnv B₁)))
        (otherwise (simEnv B₁) x args i v) ps args op (.ruleD nm qs op e prems) v :=
      ⟨rfl, ρ₀, σ, hps, hq, he, fun pr hpr => dprem_toPremW (hp pr hpr)⟩
    rcases hxs with hx | hx
    · -- `Step`
      have hrelS : (simEnv B₁).findRel? "Step" = some (ps, op, t, rules) := hx ▸ hrel
      have hnoElse := VDecl.step_elseFree hrelS hrule
      have hels : ∀ pr ∈ prems, elseFree pr = false →
          otherwise (simEnv B₁) x args i v → otherwise (simEnv B₂) x args i v :=
        fun pr hpr hf => absurd (List.all_eq_true.1 hnoElse pr hpr) (by simp [hf])
      by_cases h23 : i = 23
      · exact absurd hbody (hQ.inv.step23 B₁ _ _ ps op t rules _ args op v hv hrelS (h23 ▸ hrule))
      by_cases h8 : i = 8
      · exact absurd hbody (hQ.step8 B₁ _ _ ps op t rules _ args op v hv hrelS (h8 ▸ hrule))
      by_cases h9 : i = 9
      · exact absurd hbody (hQ.step9 B₁ _ _ ps op t rules _ args op v hv hrelS (h9 ▸ hrule))
      by_cases hctx : i ∈ [1, 2, 3, 4, 5]
      · refine .rule hrel₂ hrule hps hq₂ he₂ fun pr hpr => ?_
        exact dpremQ hs.1 (ctxPremOkH_of hrelS hctx hrule pr hpr)
          (fun y ags op'' e' w hpe hy hw => hQ.inv.ctx B₁ ps op t rules i nm qs op e prems _ v y ags
            op'' e' w hrelS hctx hrule he hv (hpe ▸ hpr) hy hw)
          (hels pr hpr) (hp pr hpr)
      · have hi : i ∉ HAgree.stepBad := by
          intro hm
          simp only [HAgree.stepBad, List.mem_cons, List.not_mem_nil, or_false] at hm hctx
          omega
        have hG : GoodEvs (evRule _) := HAgree.goodRule_step hi B₁ _ _ hrelS hrule
        refine .rule hrel₂ hrule hps hq₂ he₂ fun pr hpr => ?_
        exact dprem_agree hB (hO_goodRel hB hQ) hs.1
          (goodEvs_prems (goodEvs_prems_of_rule hG) pr hpr) (hels pr hpr) (hp pr hpr)
    · -- `Step_read`
      have hrelR : (simEnv B₁).findRel? "Step_read" = some (ps, op, t, rules) := hx ▸ hrel
      have h43 : i ≠ 43 := fun h =>
        hQ.inv.read43 B₁ _ _ ps op t rules _ args op v hv hrelR (h ▸ hrule) hbody
      have hG : GoodEvs (evRule _) := HAgree.goodRule_read h43 B₁ _ _ hrelR hrule
      have hels : ∀ pr ∈ prems, elseFree pr = false →
          otherwise (simEnv B₁) x args i v → otherwise (simEnv B₂) x args i v := by
        intro pr hpr hf h₁
        have hf' : prems.all elseFree = false :=
          List.all_eq_false.2 ⟨pr, hpr, by simp [hf]⟩
        subst hx
        exact otherwiseAt_read hB args (VDecl.readP_of_else hrelR hrule hf' he) h₁
      refine .rule hrel₂ hrule hps hq₂ he₂ fun pr hpr => ?_
      exact dprem_agree hB (hO_goodRel hB hQ) hs.1
        (goodEvs_prems (goodEvs_prems_of_rule hG) pr hpr) (hels pr hpr) (hp pr hpr)
termination_by structural _ _ _ _ _ hd => hd

/-- **A premise of a context rule moves from `B₁` to `B₂`**, its `Step` and `Step_read` calls at
`Q` values. -/
theorem dpremQ :
    ∀ {els₁ els₂ : Prop} {ρ : VarEnv} {pr : Prem}, DefsOk ρ → ctxPremOkH pr = true →
      (∀ y args op e' w, pr = .rulePr y args op e' → (y = "Step" ∨ y = "Step_read") →
        EvalExp (simEnv B₁) ρ e' w → Q w) →
      (elseFree pr = false → els₁ → els₂) →
      DPrem (simEnv B₁) (otherwise (simEnv B₁)) els₁ ρ pr →
      DPrem (simEnv B₂) (otherwise (simEnv B₂)) els₂ ρ pr
  | _, _, _, .rulePr y args op e', hρ, hok, hQw, _, .rulePr ha he hd => by
    rcases ctxPrem_split hok with ⟨hy, hga, hge⟩ | hg
    · exact .rulePr ((evalArgs_iff hB hρ hga).1 ha) ((evalExp_iff hB hρ hge).1 he)
        (dderivesQ (.inr ⟨hy, hQw y args op e' _ rfl hy he⟩) hd)
    · obtain ⟨hx, hga, hge⟩ := goodEvs_rulePr hg
      exact .rulePr ((evalArgs_iff hB hρ hga).1 ha) ((evalExp_iff hB hρ hge).1 he)
        (dderivesQ (.inl hx) hd)
  | _, _, _, _, hρ, hok, _, hels, .ifPr h =>
    dprem_agree hB (hO_goodRel hB hQ) hρ (goodEvs_of_ctxPremOk hok (by intros; simp)) hels
      (.ifPr h)
  | _, _, _, _, hρ, hok, _, hels, .elsePr h =>
    dprem_agree hB (hO_goodRel hB hQ) hρ (goodEvs_of_ctxPremOk hok (by intros; simp)) hels
      (.elsePr h)
  | _, _, _, _, hρ, hok, _, hels, .letPr h₂ h₁ =>
    dprem_agree hB (hO_goodRel hB hQ) hρ (goodEvs_of_ctxPremOk hok (by intros; simp)) hels
      (.letPr h₂ h₁)
  | _, _, _, _, hρ, hok, _, hels, .iterOptNone hd hne hall =>
    dprem_agree hB (hO_goodRel hB hQ) hρ (goodEvs_of_ctxPremOk hok (by intros; simp)) hels
      (.iterOptNone hd hne hall)
  | _, _, _, _, hρ, hok, _, hels, .iterOptSome hd hne hs hp =>
    dprem_agree hB (hO_goodRel hB hQ) hρ (goodEvs_of_ctxPremOk hok (by intros; simp)) hels
      (.iterOptSome hd hne hs hp)
  | _, _, _, _, hρ, hok, _, hels, .iterList hit hd hne hl hlen hp =>
    dprem_agree hB (hO_goodRel hB hQ) hρ (goodEvs_of_ctxPremOk hok (by intros; simp)) hels
      (.iterList hit hd hne hl hlen hp)
  | _, _, _, _, hρ, hok, _, hels, .iterListN hd he hk hl hlen hp =>
    dprem_agree hB (hO_goodRel hB hQ) hρ (goodEvs_of_ctxPremOk hok (by intros; simp)) hels
      (.iterListN hd he hk hl hlen hp)
termination_by structural _ _ _ _ _ _ _ _ hd => hd
end

/-- **The whole step moves from `B₁` to `B₂` at a `Q` value.** -/
theorem sstep_agree {c c' : Value} (hq : Q (.tuple [c, c'])) (h : SStep (simEnv B₁) c c') :
    SStep (simEnv B₂) c c' :=
  dderivesQ hB hQ (.inr ⟨.inl rfl, hq⟩) h

/-- **`Step_read` moves from `B₁` to `B₂` at a `Q` value.** -/
theorem sread_agree {c : Value} {js : List Value} (hq : Q (.tuple [c, .list js]))
    (h : SRead (simEnv B₁) c js) : SRead (simEnv B₂) c js :=
  dderivesQ hB hQ (.inr ⟨.inr rfl, hq⟩) h

end Step

/-- **On `LhsNoAtoms hAtoms` values, the whole step reads alike at builtins agreeing off
`$vbytes_` and `$hostcall`.** -/
theorem sstep_iff_h (hB : AgreeOff B₁ B₂) {c c' : Value}
    (hq : VInv.LhsNoAtoms hAtoms (.tuple [c, c'])) :
    SStep (simEnv B₁) c c' ↔ SStep (simEnv B₂) c c' :=
  ⟨sstep_agree hB stepInvH_h hq, sstep_agree (agreeOff_symm hB) stepInvH_h hq⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.HStep
