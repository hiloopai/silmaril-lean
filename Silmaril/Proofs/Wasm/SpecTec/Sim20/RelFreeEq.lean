module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.RelFree.Typ
public import Silmaril.Wasm.SpecTec.Sim.Defs

/-!
# Relation-free syntax: the agreements as statements about derivations

From the fuel-indexed agreements `RelFree.agreeAt` and `RelFree.tAgreeAt` (unrefined, in
`Raw/…/Sim20/RelFree/`):

* `evalExp_withRels`, `evalArgs_withRels`, `evalDoms_withRels`, `hasTyp_withRels`: relation-free
  syntax evaluates and types in `withRels env R` exactly as in `env` (both directions, since
  `withRels (withRels env R) env.rels = env`);
* `quantsOk_withRels`, `premW_withRels`, `ruleBody_withRels`: a rule body whose rule passes
  `ruleOkB bad` holds in `withRels env R`, with any relation and `otherwise` readings, if it holds in
  `env`. The rule has no `rulePr` and no `otherwise` premise, so the readings never matter.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.RelFree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (PremW QuantsOk RuleBody EvalDoms Interp)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evExp evArgs evDoms evTyp evPrem evPrems evParams
  evParam evRule evIter evIterExp)

variable {bad : List String} {env : Env} {R : Map RelDef}

/-! ## Environments -/

/-- Replacing the relation table twice, putting the old one back, gives the environment back. -/
theorem withRels_withRels (env : Env) (R : Map RelDef) : withRels (withRels env R) env.rels = env := by
  cases env; rfl

theorem defsGood_withRels (h : DefsGood bad env) : DefsGood bad (withRels env R) := h

theorem typsGood_withRels (h : TypsGood bad env) : TypsGood bad (withRels env R) := h

theorem goodEvs_of_all {l : List Silmaril.Wasm.SpecTec.Sim.Round7.Script.Ev}
    (h : l.all (rfEvB bad) = true) : GoodEvs bad l :=
  fun e he => List.all_eq_true.1 h e he

/-! ## Evaluation and typing -/

theorem evalExp_withRels (hDG : DefsGood bad env) {ρ : VarEnv} {e : Exp} {v : Value}
    (hD : DefsOk bad ρ) (hG : GoodEvs bad (evExp e)) (h : EvalExp env ρ e v) :
    EvalExp (withRels env R) ρ e v := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, ((agreeAt bad env R hDG n).exp ρ e hD hG).ok hn⟩

theorem evalArgs_withRels (hDG : DefsGood bad env) {ρ : VarEnv} {ags : List Arg} {ws : List ArgV}
    (hD : DefsOk bad ρ) (hG : GoodEvs bad (evArgs ags)) (h : EvalArgs env ρ ags ws) :
    EvalArgs (withRels env R) ρ ags ws := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, ((agreeAt bad env R hDG n).args ρ ags hD hG).ok hn⟩

theorem evalDoms_withRels (hDG : DefsGood bad env) {ρ : VarEnv} {ds : List Dom}
    {xvs : List (IL.Id × Value)} (hD : DefsOk bad ρ) (hG : GoodEvs bad (evDoms ds))
    (h : EvalDoms env ρ ds xvs) : EvalDoms (withRels env R) ρ ds xvs := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, ((agreeAt bad env R hDG n).doms ρ ds hD hG).ok hn⟩

theorem hasTyp_withRels (hDG : DefsGood bad env) (hTG : TypsGood bad env) {ρ : VarEnv} {t : Typ}
    {v : Value} (hD : DefsOk bad ρ) (hT : TypsOk bad ρ) (hG : GoodEvs bad (evTyp t))
    (h : HasTyp env ρ t v) : HasTyp (withRels env R) ρ t v := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, ((tAgreeAt bad env R hDG hTG n).typ ρ t v hD hT hG).ok hn⟩

/-- **Harmless types type alike under any relation table.** -/
theorem hasTyp_withRels_iff (hDG : DefsGood bad env) (hTG : TypsGood bad env) {ρ : VarEnv}
    {t : Typ} {v : Value} (hD : DefsOk bad ρ) (hT : TypsOk bad ρ) (hG : GoodEvs bad (evTyp t)) :
    HasTyp (withRels env R) ρ t v ↔ HasTyp env ρ t v := by
  refine ⟨fun h => ?_, hasTyp_withRels hDG hTG hD hT hG⟩
  have h' := hasTyp_withRels (R := env.rels) (defsGood_withRels (R := R) hDG)
    (typsGood_withRels (R := R) hTG) hD hT hG h
  rwa [withRels_withRels] at h'

/-- **Relation-free expressions evaluate alike under any relation table.** -/
theorem evalExp_withRels_iff (hDG : DefsGood bad env) {ρ : VarEnv} {e : Exp} {v : Value}
    (hD : DefsOk bad ρ) (hG : GoodEvs bad (evExp e)) :
    EvalExp (withRels env R) ρ e v ↔ EvalExp env ρ e v := by
  refine ⟨fun h => ?_, evalExp_withRels hDG hD hG⟩
  have h' := evalExp_withRels (R := env.rels) (defsGood_withRels (R := R) hDG) hD hG h
  rwa [withRels_withRels] at h'

/-! ## Rule bodies -/

theorem goodEvs_param_typ : ∀ {qs : List Param}, GoodEvs bad (evParams qs) →
    ∀ x t, Param.expP x t ∈ qs → GoodEvs bad (evTyp t) :=
  goodEvs_params

theorem quantsOk_withRels (hDG : DefsGood bad env) (hTG : TypsGood bad env) {ρ : VarEnv}
    {qs : List Param} (hD : DefsOk bad ρ) (hT : TypsOk bad ρ) (hG : GoodEvs bad (evParams qs))
    (h : QuantsOk env ρ qs) : QuantsOk (withRels env R) ρ qs := by
  intro x t hx
  obtain ⟨w, hw, ht⟩ := h x t hx
  exact ⟨w, hw, hasTyp_withRels hDG hTG hD hT (goodEvs_params hG x t hx) ht⟩

theorem goodEvs_letPr {e₁ e₂ : Exp} (h : GoodEvs bad (evPrem (.letPr e₁ e₂))) :
    GoodEvs bad (evExp e₁) ∧ GoodEvs bad (evExp e₂) := by
  simpa only [evPrem, goodEvs_append] using h

theorem goodEvs_iterPr {pr : Prem} {it : Iter} {ds : List Dom}
    (h : GoodEvs bad (evPrem (.iterPr pr (.mk it ds)))) :
    GoodEvs bad (evPrem pr) ∧ GoodEvs bad (evIter it) ∧ GoodEvs bad (evDoms ds) := by
  simpa only [evPrem, evIterExp, goodEvs_append, and_assoc] using h

theorem not_goodEvs_rulePr {x : IL.Id} {args : List Arg} {op : MixopS} {e : Exp} :
    ¬ GoodEvs bad (evPrem (.rulePr x args op e)) := fun h =>
  absurd (h (.ref 0 x) List.mem_cons_self) (by simp [rfEvB])

/-- **A relation-free premise holds under any relation table**, with any relation reading, if it
has no `otherwise` premise or the `otherwise` readings are related (`els → els'`). -/
theorem premW_withRels_gen (hDG : DefsGood bad env) {D D' : Interp} {els els' : Prop}
    {ρ : VarEnv} {pr : Prem} (h : PremW env D els ρ pr) :
    DefsOk bad ρ → GoodEvs bad (evPrem pr) → (noElseB pr = true ∨ (els → els')) →
      PremW (withRels env R) D' els' ρ pr := by
  induction h with
  | ifPr he => exact fun hD hG _ => .ifPr (evalExp_withRels hDG hD hG he)
  | elsePr hel => exact fun _ _ hE => .elsePr (hE.elim (fun h => absurd h (by decide)) (· hel))
  | letPr h₂ h₁ =>
    exact fun hD hG _ => .letPr (evalExp_withRels hDG hD (goodEvs_letPr hG).2 h₂)
      (evalExp_withRels hDG hD (goodEvs_letPr hG).1 h₁)
  | rulePr _ _ _ => exact fun _ hG _ => absurd hG not_goodEvs_rulePr
  | iterOptNone hds hne hall =>
    exact fun hD hG _ => .iterOptNone (evalDoms_withRels hDG hD (goodEvs_iterPr hG).2.2 hds) hne hall
  | iterOptSome hds hne hrow _ ih =>
    exact fun hD hG hE => .iterOptSome (evalDoms_withRels hDG hD (goodEvs_iterPr hG).2.2 hds) hne
      hrow (ih (defsOk_bindVals hD _) (goodEvs_iterPr hG).1 hE)
  | iterList hit hds hne hdl hlen _ ih =>
    exact fun hD hG hE => .iterList hit (evalDoms_withRels hDG hD (goodEvs_iterPr hG).2.2 hds) hne
      hdl hlen fun r hr => ih r hr (defsOk_bindVals hD _) (goodEvs_iterPr hG).1 hE
  | iterListN hds hk hkv hdl hlen _ ih =>
    exact fun hD hG hE => .iterListN (evalDoms_withRels hDG hD (goodEvs_iterPr hG).2.2 hds)
      (evalExp_withRels hDG hD (by simpa only [evIter] using (goodEvs_iterPr hG).2.1) hk) hkv
      hdl hlen fun r hr => ih r hr (defsOk_bindVals hD _) (goodEvs_iterPr hG).1 hE

/-- **A relation-free premise without `otherwise` holds under any relation table**, with any
relation and `otherwise` readings. -/
theorem premW_withRels (hDG : DefsGood bad env) {D D' : Interp} {els els' : Prop} {ρ : VarEnv}
    {pr : Prem} (h : PremW env D els ρ pr) (hD : DefsOk bad ρ) (hG : GoodEvs bad (evPrem pr))
    (hE : noElseB pr = true) : PremW (withRels env R) D' els' ρ pr :=
  premW_withRels_gen hDG h hD hG (.inl hE)

/-- The premises of a rule have no `otherwise`. -/
def rulePremsNoElse : Rule → Bool
  | .ruleD _ _ _ _ prems => prems.all noElseB

/-- **A rule body of a relation-free rule holds under any relation table**, with any relation
reading, if the rule has no `otherwise` premise or the `otherwise` readings are related. -/
theorem ruleBody_withRels_gen (hDG : DefsGood bad env) (hTG : TypsGood bad env) {D D' : Interp}
    {els els' : Prop} {op : MixopS} {r : Rule} {v : Value}
    (hr : (evRule r).all (rfEvB bad) = true) (hE : rulePremsNoElse r = true ∨ (els → els'))
    (h : RuleBody env D els [] [] op r v) : RuleBody (withRels env R) D' els' [] [] op r v := by
  obtain ⟨nm, qs, op', e, prems⟩ := r
  obtain ⟨hop, ρ₀, σ, hb, hq, he, hp⟩ := h
  have hG : GoodEvs bad (evRule (.ruleD nm qs op' e prems)) := goodEvs_of_all hr
  have hG' : (GoodEvs bad (evParams qs) ∧ GoodEvs bad (evExp e)) ∧ GoodEvs bad (evPrems prems) := by
    simpa only [evRule, goodEvs_append] using hG
  obtain rfl : ρ₀ = VarEnv.empty := by simpa [bindParams] using hb.symm
  have hD : DefsOk bad (VarEnv.empty.bindVals σ) := defsOk_bindVals defsOk_empty σ
  have hT : TypsOk bad (VarEnv.empty.bindVals σ) := typsOk_empty
  refine ⟨hop, VarEnv.empty, σ, hb, quantsOk_withRels hDG hTG hD hT hG'.1.1 hq,
    evalExp_withRels hDG hD hG'.1.2 he, fun pr hpr => ?_⟩
  have hE' : noElseB pr = true ∨ (els → els') :=
    hE.imp_left fun h => List.all_eq_true.1 h pr hpr
  exact premW_withRels_gen hDG (hp pr hpr) hD (goodEvs_prems hG'.2 pr hpr) hE'

/-- **A rule body of a `ruleOkB` rule holds under any relation table**, with any relation and
`otherwise` readings. -/
theorem ruleBody_withRels (hDG : DefsGood bad env) (hTG : TypsGood bad env) {D D' : Interp}
    {els els' : Prop} {op : MixopS} {r : Rule} {v : Value} (hr : ruleOkB bad r = true)
    (h : RuleBody env D els [] [] op r v) : RuleBody (withRels env R) D' els' [] [] op r v := by
  have hr' : (evRule r).all (rfEvB bad) = true ∧ rulePremsNoElse r = true := by
    obtain ⟨_, _, _, _, _⟩ := r
    simpa only [ruleOkB, rulePremsNoElse, Bool.and_eq_true] using hr
  exact ruleBody_withRels_gen hDG hTG hr'.1 (.inl hr'.2) h

/-- `ruleBody_withRels_gen`, back from `withRels env R` to `env`. -/
theorem ruleBody_of_withRels (hDG : DefsGood bad env) (hTG : TypsGood bad env) {D D' : Interp}
    {els els' : Prop} {op : MixopS} {r : Rule} {v : Value}
    (hr : (evRule r).all (rfEvB bad) = true) (hE : rulePremsNoElse r = true ∨ (els' → els))
    (h : RuleBody (withRels env R) D' els' [] [] op r v) : RuleBody env D els [] [] op r v := by
  have h' := ruleBody_withRels_gen (R := env.rels) (D' := D) (defsGood_withRels (R := R) hDG)
    (typsGood_withRels (R := R) hTG) hr hE h
  rwa [withRels_withRels] at h'

/-! ## `otherwise` and firings -/

/-- A rule body never holds with relation parameters but no arguments. -/
theorem not_ruleBody_cons {e : Env} {D : Interp} {els : Prop} {p : Param} {ps : List Param}
    {op : MixopS} {r : Rule} {w : Value} : ¬ RuleBody e D els (p :: ps) [] op r w := by
  obtain ⟨_, _, _, _, _⟩ := r
  rintro ⟨_, _, _, hb, _⟩
  simp [bindParams] at hb

/-- A relation-free rule body holds alike under any relation table, given related `otherwise`
readings. -/
theorem ruleBody_withRels_iff (hDG : DefsGood bad env) (hTG : TypsGood bad env) {D D' : Interp}
    {els els' : Prop} {ps : List Param} {op : MixopS} {r : Rule} {w : Value}
    (hr : (evRule r).all (rfEvB bad) = true) (hE : els' ↔ els) :
    RuleBody (withRels env R) D' els' ps [] op r w ↔ RuleBody env D els ps [] op r w := by
  cases ps with
  | nil => exact ⟨ruleBody_of_withRels hDG hTG hr (.inr hE.1), ruleBody_withRels_gen hDG hTG hr (.inr hE.2)⟩
  | cons p ps => exact iff_of_false not_ruleBody_cons not_ruleBody_cons

/-- **`otherwise` agrees under any relation table** on a relation that both tables give the same
relation-free rules. -/
theorem otherwiseAt_withRels_iff (hDG : DefsGood bad env) (hTG : TypsGood bad env) {x : IL.Id}
    (hx : (withRels env R).findRel? x = env.findRel? x)
    (hrules : ∀ ps op t rules, env.findRel? x = some (ps, op, t, rules) →
      ∀ r ∈ rules, (evRule r).all (rfEvB bad) = true) :
    ∀ i v, Sim.otherwiseAt (withRels env R) x [] i v ↔ Sim.otherwiseAt env x [] i v := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro v
    rw [Sim.otherwiseAt, Sim.otherwiseAt, hx]
    exact forall_congr' fun j => forall_congr' fun hj => forall_congr' fun ps =>
      forall_congr' fun op => forall_congr' fun t => forall_congr' fun rules =>
        forall_congr' fun r => forall_congr' fun hrel => forall_congr' fun hr =>
          forall_congr' fun w => forall_congr' fun _ => not_congr
            (ruleBody_withRels_iff hDG hTG (hrules ps op t rules hrel r (List.mem_of_getElem? hr))
              (ih j hj w))

/-- **Firings of a relation with relation-free rules agree under any relation table** (when both
tables give the relation the same rules). -/
theorem fires_withRels_iff (hDG : DefsGood bad env) (hTG : TypsGood bad env) {x : IL.Id}
    (hx : (withRels env R).findRel? x = env.findRel? x)
    (hrules : ∀ ps op t rules, env.findRel? x = some (ps, op, t, rules) →
      ∀ r ∈ rules, (evRule r).all (rfEvB bad) = true) (i : Nat) (v : Value) :
    Sim.Fires (withRels env R) x i v ↔ Sim.Fires env x i v := by
  have hO := otherwiseAt_withRels_iff hDG hTG hx hrules i v
  constructor
  · rintro ⟨t, rules, r, hrel, hr, hb⟩
    rw [hx] at hrel
    have hok := hrules _ _ _ _ hrel r (List.mem_of_getElem? hr)
    exact ⟨t, rules, r, hrel, hr, ruleBody_of_withRels hDG hTG hok (.inr hO.1) hb⟩
  · rintro ⟨t, rules, r, hrel, hr, hb⟩
    have hok := hrules _ _ _ _ hrel r (List.mem_of_getElem? hr)
    exact ⟨t, rules, r, hx ▸ hrel, hr, ruleBody_withRels_gen hDG hTG hok (.inr hO.2) hb⟩

end Silmaril.Wasm.SpecTec.Sim20.RelFree
