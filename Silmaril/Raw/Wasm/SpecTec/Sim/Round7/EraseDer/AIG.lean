module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseDer.Bwd
public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.Sites.Thms

/-!
# Round 7, moving derivations across erasure: the mode analysis at any checked part (unrefined)

`Round7.EraseAll.dderivesB_AI` is stated at the checked part `grE`. Its proof uses three facts
about `grE` only: its relations are reached from `Step` (so the mode check `detFacts` applies),
every rule of each of them passes the evaluator-level check, and so do the conclusion
alternatives. `GFacts gr gd B` packages these for a set of relations `gr` (with `AllRFacts`, which
also carries the closure check), and `dderivesB_AIg` is the same proof at any such `gr`.

* `gFacts_E`: the facts at `grE`, `gdE`;
* `gFacts_B`: the facts at `grB`, `gdB` (`grE` with `Step_read`, `gdE` with `$blocktype_`), from
  the kernel check `xBNamedOk_fixed` of `Step_read`'s rules and conclusion alternatives.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (DDerivesBQ DPremBQ QuantsP Hyps xPrem xExp xDoms
  grE gdE grB gdB InAI AIOn DefsG PremFactQ defsG_empty defsG_bindVals aiOn_bindVals ai_evalDoms
  ai_domSomes ai_rows ai_eval_on aiOn_ruleK)
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (tyA TypsOk typsOk_empty typsOk_of_typs)
open Silmaril.Wasm.SpecTec.Sim.Round7.Transfer (bindParams_nil)
open Silmaril.Wasm.SpecTec.Sim.Round7.Determ (premDetOk fvIn detFacts premDetOk_rulePr
  premDetOk_iterPr quantNames)
open Round6.Reading (DDerivesB DPremB conclAlts)

variable {Q : Value → Prop} {B : Builtins}

/-! ## The facts about a checked part -/

/-- **What the derivation transfer needs of a set of relations `gr`**: each is reached from `Step`,
and each of its rules passes the checks at `gr`, `gd`. -/
structure GFacts (gr gd : String → Bool) (B : Builtins) : Prop where
  reach : ∀ x, gr x = true → (0, x) ∈ Script.stepReach
  rf : AllRFacts gr gd (utf8Env B)

/-- **`otherwise` read only at swap-set inputs** of the relations `gr`. -/
def ElseAIg (gr : String → Bool) (Q : Value → Prop) (O : ElseI) : ElseI := fun x args i v =>
  O x args i v ∧ InAI Q v ∧ gr x = true

theorem gFacts_E : GFacts grE gdE B :=
  ⟨fun _ hx => EraseAll.reach_of_grE hx, allRFacts_E⟩

theorem stepRead_reach : (0, "Step_read") ∈ Script.stepReach := by decide

theorem reach_of_grB {x : String} (h : grB x = true) : (0, x) ∈ Script.stepReach := by
  simp only [grB, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | rfl
  · exact EraseAll.reach_of_grE h
  · exact stepRead_reach

/-- The conclusion alternatives of `Step_read`'s rules pass the check at `grB`, `gdB`. -/
theorem altsB {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {nm : IL.Id} {qs : List Param} {e : Exp} {prems : List Prem} (hx : grB x = true)
    (hrel' : (simEnv B).findRel? x = some (ps, op, t, rules))
    (hr : Rule.ruleD nm qs op e prems ∈ rules) :
    ∀ e' ∈ (if Round6.Reading.hasOptNil e then Round6.Reading.optAlts e else []),
      xExp grB gdB e' = true := by
  by_cases hE : grE x = true
  · have h := List.all_eq_true.1 EraseAll.xAltsOk_fixed _ (EraseAll.mem_rels_of_findRel' hrel')
    simp only [hE, Bool.not_true, Bool.false_or, List.all_eq_true] at h
    have h₂ := h _ hr
    simp only [List.all_eq_true] at h₂
    exact fun e' he' => EraseAll.xExp_mono EraseAll.grE_grB EraseAll.gdE_gdB e' (h₂ e' he')
  · have hsr : x = "Step_read" := by simpa [grB, hE] using hx
    subst hsr
    obtain ⟨d', hd', hm⟩ := EraseAll.mem_relsOfDefs (EraseAll.mem_rels_of_findRel' hrel')
    have hn : EraseAll.xBNamed d' = true := by
      simp only [EraseAll.xBNamed, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
      exact Or.inr ⟨_, hm, rfl⟩
    have h := EraseAll.xDefOk_B hd' hn
    simp only [EraseAll.xDefOk, Bool.and_eq_true] at h
    have h' := List.all_eq_true.1 h.2 _ hm
    have hg : grB "Step_read" = true := by simp [grB]
    simp only [hg, Bool.not_true, Bool.false_or, List.all_eq_true] at h'
    have h₂ := h' _ hr
    simp only [List.all_eq_true] at h₂
    exact h₂

theorem rFactsB {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {i : Nat} {nm : IL.Id} {qs : List Param} {e : Exp} {prems : List Prem} (hx : grB x = true)
    (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e prems)) : RFacts grB gdB ps qs e prems := by
  have hr : Rule.ruleD nm qs op e prems ∈ rules := List.mem_of_getElem? hrule
  have hx₁ := EraseAll.rels_B B x _ hx hrel _ hr
  simp only [EraseAll.xRule, Bool.and_eq_true] at hx₁
  have hrel' := hrel
  rw [findRel?_utf8Env] at hrel'
  have hreach := reach_of_grB hx
  have hF := detFacts hreach hrel' hrule
  have hc := List.all_eq_true.1 closedRels_fixed _ (EraseAll.mem_rels_of_findRel' hrel')
  have hreach' : Script.stepReach.contains (0, x) = true := List.contains_iff_mem.2 hreach
  simp only [hreach', Bool.not_true, Bool.false_or] at hc
  have hcl := List.all_eq_true.1 hc _ hr
  simp only [ruleClosed, Bool.and_eq_true, List.all_eq_true] at hcl
  have hq := List.all_eq_true.1 xRelQuants_fixed _ (EraseAll.mem_rels_of_findRel' hrel')
  simp only [hreach', Bool.not_true, Bool.false_or, List.all_eq_true] at hq
  have hq' := hq _ hr
  simp only [List.all_eq_true] at hq'
  have hA := altsB hx hrel' hr
  refine ⟨hF.params, fun pr hpr => ⟨EraseAll.xPrems_mem hx₁.2 pr hpr, hcl.1.2 pr hpr⟩,
    fun e' he' => ⟨?_, hcl.1.1 e' he'⟩, fun y ty hy => ⟨?_, ?_⟩⟩
  · rcases List.mem_cons.1 he' with rfl | he'
    · exact hx₁.1
    · exact hA e' he'
  · simpa using hq' _ hy
  · simpa using hcl.2 _ hy

theorem gFacts_B : GFacts grB gdB B :=
  ⟨fun _ hx => reach_of_grB hx, fun hx hrel hrule => rFactsB hx hrel hrule⟩

/-! ## The mode analysis at `gr` -/

section AI

set_option linter.unusedSectionVars false

variable {gr gd : String → Bool}

theorem xPrem_rulePrG {x : IL.Id} {args : List Arg} {op : MixopS} {e : Exp}
    (h : xPrem gr gd (.rulePr x args op e) = true) : gr x = true := by
  simp only [xPrem, Bool.and_eq_true] at h
  exact h.1.1

theorem xPrem_iterPrG {pr : Prem} {it : Iter} {ds : List Dom}
    (h : xPrem gr gd (.iterPr pr (.mk it ds)) = true) :
    xPrem gr gd pr = true ∧ xDoms gr gd ds = true := by
  simp only [xPrem, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.2⟩

theorem inAI_of_premDetOkG (H : Hyps Q gr gd (utf8Env B)) {ρ : VarEnv} {K : List IL.Id}
    {x : IL.Id} {args : List Arg} {op : MixopS} {e : Exp} {w : Value} (hD : DefsG gd ρ)
    (hX : xPrem gr gd (.rulePr x args op e) = true) (hK : AIOn Q ρ K)
    (hok : premDetOk K (.rulePr x args op e) = true) (he : EvalExp (utf8Env B) ρ e w) :
    InAI Q w := by
  obtain ⟨a, rest, rfl, hfv⟩ := premDetOk_rulePr hok
  have hxa : xExp gr gd a = true := by
    simp only [xPrem, xExp, EraseAll.xExps, Bool.and_eq_true] at hX
    exact hX.2.1
  obtain ⟨va, vs, rfl, ha⟩ := Determ.evalExp_tupE_cons he
  have hva : AllIn Q va := ai_eval_on H hD hxa hK hfv ha
  intro a' r' heq
  cases heq
  exact hva

variable (G : GFacts gr gd B) (H : Hyps Q gr gd (utf8Env B))
include G H

mutual
/-- **Rule quantifiers in the swap set**, at any checked part. -/
theorem dderivesB_AIg {O : ElseI} :
    ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}, gr x = true → InAI Q v →
      DDerivesB (utf8Env B) O x op args v →
      DDerivesBQ (AllIn Q) (utf8Env B) (ElseAIg gr Q O) x op args v ∧ AllIn Q v
  | _, _, _, _, hx, hin, .rule (σ := σ) (ρ₀ := ρ₀) hrel hrule halt hps hq he hp => by
    have hrel' := hrel
    rw [findRel?_utf8Env] at hrel'
    have hF := detFacts (G.reach _ hx) hrel' hrule
    have hX := G.rf hx hrel hrule
    have hρ : ρ₀ = VarEnv.empty := bindParams_nil (hF.params ▸ hps)
    have hD : DefsG gd (ρ₀.bindVals σ) := hρ ▸ defsG_bindVals defsG_empty σ
    have hT : TypsOk tyA (ρ₀.bindVals σ) := hρ ▸ typsOk_of_typs (typsOk_empty tyA) rfl
    obtain ⟨-, hqK, hfvK, hpK⟩ := hF.concl _ halt
    have hxp : ∀ pr ∈ _, xPrem gr gd pr = true := fun pr hpr => (hX.prems pr hpr).1
    have hfact : ∀ pr ∈ _, PremFactQ Q (utf8Env B) (ρ₀.bindVals σ) pr := fun pr hpr =>
      dpremB_factQG (hxp pr hpr) (hp pr hpr)
    have hK := aiOn_ruleK H hD hT hq he hin hxp hfact
    have hxf : QuantsP (AllIn Q) (ρ₀.bindVals σ) _ := fun y t w hy hw =>
      hK y (List.contains_iff_mem.1 (List.all_eq_true.1 hqK y (List.mem_filterMap.2 ⟨_, hy, rfl⟩)))
        w hw
    refine ⟨.rule (σ := σ) hrel hrule halt hps hq hxf he fun pr hpr => ?_,
      ai_eval_on H hD (hX.alts _ halt).1 hK hfvK he⟩
    exact dpremB_AIG (hpK pr hpr) hK hD (hxp pr hpr) (fun h => ⟨h, hin, hx⟩) (hp pr hpr)
termination_by structural _ _ _ _ _ _ hd => hd

/-- **A premise that holds gives its `PremFactQ`.** -/
theorem dpremB_factQG {O : ElseI} {els : Prop} :
    ∀ {ρ : VarEnv} {pr : Prem}, xPrem gr gd pr = true → DPremB (utf8Env B) O els ρ pr →
      PremFactQ Q (utf8Env B) ρ pr
  | _, _, _, .ifPr h => h
  | _, _, _, .elsePr _ => trivial
  | _, _, _, .letPr h₂ h₁ => ⟨_, h₂, h₁⟩
  | _, _, hX, .rulePr _ he hd =>
    ⟨_, he, fun hin => (dderivesB_AIg (xPrem_rulePrG hX) hin hd).2⟩
  | _, _, _, .iterOptNone _ _ _ => trivial
  | _, _, _, .iterOptSome _ _ _ _ => trivial
  | _, _, _, .iterList _ _ _ _ _ _ => trivial
  | _, _, _, .iterListN _ _ _ _ _ _ => trivial
termination_by structural _ _ _ hd => hd

/-- **A premise over known variables is a `DPremBQ (AllIn Q)` premise.** -/
theorem dpremB_AIG {O : ElseI} {els els' : Prop} {K : List IL.Id} :
    ∀ {ρ : VarEnv} {pr : Prem}, premDetOk K pr = true → AIOn Q ρ K → DefsG gd ρ →
      xPrem gr gd pr = true → (els → els') → DPremB (utf8Env B) O els ρ pr →
      DPremBQ (AllIn Q) (utf8Env B) (ElseAIg gr Q O) els' ρ pr
  | _, _, _, _, _, _, _, .ifPr h => .ifPr h
  | _, _, _, _, _, _, hels, .elsePr h => .elsePr (hels h)
  | _, _, _, _, _, _, _, .letPr h₂ h₁ => .letPr h₂ h₁
  | _, .rulePr _ _ _ e, hok, hK, hD, hX, _, .rulePr ha he hd =>
    .rulePr ha he (dderivesB_AIg (xPrem_rulePrG hX) (inAI_of_premDetOkG H hD hX hK hok he) hd).1
  | _, _, _, _, _, _, _, .iterOptNone hd hne hall => .iterOptNone hd hne hall
  | _, _, hok, hK, hD, hX, hels, .iterOptSome (row := row) hd hne hs hp => by
    have hok' := premDetOk_iterPr hok
    have hX' := xPrem_iterPrG hX
    have hrow := ai_domSomes (ai_evalDoms H hD hX'.2 hK hok'.1 hd) hs
    exact .iterOptSome hd hne hs
      (dpremB_AIG hok'.2 (aiOn_bindVals hK hrow) (defsG_bindVals hD row) hX'.1 hels hp)
  | _, _, hok, hK, hD, hX, hels, .iterList hit hd hne hl hk hp => by
    have hok' := premDetOk_iterPr hok
    have hX' := xPrem_iterPrG hX
    have hx := ai_evalDoms H hD hX'.2 hK hok'.1 hd
    exact .iterList hit hd hne hl hk fun r hr =>
      dpremB_AIG hok'.2 (aiOn_bindVals hK (ai_rows hx hl none _ r hr)) (defsG_bindVals hD r)
        hX'.1 hels (hp r hr)
  | _, _, hok, hK, hD, hX, hels, .iterListN hd he hk hl hlen hp => by
    have hok' := premDetOk_iterPr hok
    have hX' := xPrem_iterPrG hX
    have hx := ai_evalDoms H hD hX'.2 hK hok'.1 hd
    exact .iterListN hd he hk hl hlen fun r hr =>
      dpremB_AIG hok'.2 (aiOn_bindVals hK (ai_rows hx hl _ _ r hr)) (defsG_bindVals hD r)
        hX'.1 hels (hp r hr)
termination_by structural _ _ _ _ _ _ _ hd => hd
end

end AI

/-! ## Typing does not depend on `gd` -/

theorem typFwd_gd {gd gd' : String → Bool} {env : Env} (h : TypFwd Q gd env) : TypFwd Q gd' env :=
  fun ρ ρ' t w hR ht hρ hdn hd hg hxt hw hty =>
    h ρ ρ' t w ⟨hR.ai, hR.er, fun p hp => by rw [hdn] at hp; cases hp⟩ ht hρ hdn hd hg hxt hw hty

theorem typBwd_gd {gd gd' : String → Bool} {env : Env} (h : TypBwd Q gd env) : TypBwd Q gd' env :=
  fun ρ ρ' t w hR ht hρ hdn hd hg hxt hw hty =>
    h ρ ρ' t w ⟨hR.ai, hR.er, fun p hp => by rw [hdn] at hp; cases hp⟩ ht hρ hdn hd hg hxt hw hty

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
