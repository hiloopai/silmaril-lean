module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Determ.Scope

/-!
# Round 7, determination: derivations from `ExpFree` inputs bind `ExpFree` quantifiers

`dderivesB_E`: in `utf8Env B`, with primitives that preserve `ExpFree`, every `DDerivesB`
derivation of a relation `Step` reaches, at a value whose input (first tuple component) is
`ExpFree`, is a `Round7.Transfer.DDerivesBE` derivation, and its value is `ExpFree`. Its
`otherwise` premises are read at `ExpFree` inputs only (`ElseEF O`).

The proof is by structural recursion on the derivation. At a rule instance:

1. each premise gives its `PremFact`, a relation premise through the recursion (`dpremB_fact`);
2. the mode check is sound (`Round7.Determ.efOn_ruleK`), so every quantifier is `ExpFree` and,
   by the forward lemma, so is the conclusion's value;
3. every premise is then rebuilt as a `DPremBE` premise (`dpremB_E`): a relation premise has an
   `ExpFree` input by the check `premDetOk`, so the recursion applies to it, also inside
   iterations, whose rows are `ExpFree`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Determ

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (ExpFree tyA TypsOk typsOk_empty typsOk_of_typs)
open Silmaril.Wasm.SpecTec.Sim.Round7.Transfer (DDerivesBE DPremBE QuantsExpFree bindParams_nil)
open Round6.Reading (DDerivesB DPremB conclAlts)

/-- **`otherwise` read only at `ExpFree` inputs**, of relations `Step` reaches. -/
def ElseEF (O : ElseI) : ElseI := fun x args i v => O x args i v ∧ InEF v ∧ (0, x) ∈ stepReach

variable {B : Builtins}

theorem inEF_of_tupE {ρ : VarEnv} {K : List IL.Id} {a : Exp} {rest : List Exp} {w : Value}
    (hB : BuiltinsEF B) (hD : DefsOk ρ) (hGa : GoodXs (evExp a)) (hK : EFOn ρ K)
    (hfv : fvIn K a = true) (he : EvalExp (utf8Env B) ρ (.tupE (a :: rest)) w) : InEF w := by
  obtain ⟨va, vs, rfl, ha⟩ := evalExp_tupE_cons he
  have hva : ExpFree va := ef_eval_on hB hD hGa hK hfv ha
  intro a' r' heq
  cases heq
  exact hva

theorem premDetOk_rulePr {K : List IL.Id} {x : IL.Id} {args : List Arg} {op : MixopS} {e : Exp}
    (h : premDetOk K (.rulePr x args op e) = true) :
    ∃ a rest, e = .tupE (a :: rest) ∧ fvIn K a = true := by
  unfold premDetOk at h
  split at h
  · rename_i a rest heq
    cases heq
    exact ⟨a, rest, rfl, h⟩
  · cases h
  · rename_i heq; cases heq
  · rename_i _ _ hne _; exact (hne x args op e rfl).elim

theorem goodXs_rulePr {x : IL.Id} {args : List Arg} {op : MixopS} {e : Exp}
    (h : GoodXs (evPrem (.rulePr x args op e))) : (0, x) ∈ stepReach ∧ GoodXs (evExp e) := by
  simp only [evPrem, goodXs_cons, goodXs_append, goodX_ref0] at h
  exact ⟨h.1, h.2.2⟩

theorem goodXs_iterPr {pr : Prem} {it : Iter} {ds : List Dom}
    (h : GoodXs (evPrem (.iterPr pr (.mk it ds)))) : GoodXs (evPrem pr) ∧ GoodXs (evDoms ds) := by
  simp only [evPrem, evIterExp, goodXs_append] at h
  exact ⟨h.1, h.2.2⟩

theorem inEF_of_premDetOk {ρ : VarEnv} {K : List IL.Id} {x : IL.Id} {args : List Arg}
    {op : MixopS} {e : Exp} {w : Value} (hB : BuiltinsEF B) (hD : DefsOk ρ)
    (hG : GoodXs (evPrem (.rulePr x args op e))) (hK : EFOn ρ K)
    (hok : premDetOk K (.rulePr x args op e) = true) (he : EvalExp (utf8Env B) ρ e w) :
    InEF w := by
  obtain ⟨a, rest, rfl, hfv⟩ := premDetOk_rulePr hok
  have hGa : GoodXs (evExp a) := by
    have h := (goodXs_rulePr hG).2
    simp only [evExp, evExps, goodXs_append] at h
    exact h.1
  exact inEF_of_tupE hB hD hGa hK hfv he

theorem premDetOk_iterPr {K : List IL.Id} {pr : Prem} {it : Iter} {ds : List Dom}
    (h : premDetOk K (.iterPr pr (.mk it ds)) = true) :
    (∀ d ∈ ds, fvIn K (domSrc d) = true) ∧ premDetOk K pr = true := by
  simp only [premDetOk, Bool.and_eq_true, List.all_eq_true] at h
  exact h

mutual
/-- **Determination.** -/
theorem dderivesB_E (hB : BuiltinsEF B) {O : ElseI} :
    ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}, (0, x) ∈ stepReach → InEF v →
      DDerivesB (utf8Env B) O x op args v →
      DDerivesBE (utf8Env B) (ElseEF O) x op args v ∧ ExpFree v
  | _, _, _, _, hx, hin, .rule (σ := σ) (ρ₀ := ρ₀) hrel hrule halt hps hq he hp => by
    have hrel' := hrel
    rw [Round7.findRel?_utf8Env] at hrel'
    have hF := detFacts hx hrel' hrule
    have hρ : ρ₀ = VarEnv.empty := bindParams_nil (hF.params ▸ hps)
    have hD : DefsOk (ρ₀.bindVals σ) := hρ ▸ defsOk_bindVals defsOk_empty σ
    have hT : TypsOk tyA (ρ₀.bindVals σ) := hρ ▸ typsOk_of_typs (typsOk_empty tyA) rfl
    obtain ⟨hGe, hqK, hfvK, hpK⟩ := hF.concl _ halt
    have hfact : ∀ pr ∈ _, PremFact B (ρ₀.bindVals σ) pr := fun pr hpr =>
      dpremB_fact hB (hF.goodPrems pr hpr) (hp pr hpr)
    have hK := efOn_ruleK hB hD hT hq he hin hF.goodPrems hfact
    have hxf : QuantsExpFree (ρ₀.bindVals σ) _ := fun y t w hy hw =>
      hK y (List.contains_iff_mem.1 (List.all_eq_true.1 hqK y (List.mem_filterMap.2 ⟨_, hy, rfl⟩)))
        w hw
    refine ⟨.rule (σ := σ) hrel hrule halt hps hq hxf he fun pr hpr => ?_,
      ef_eval_on hB hD hGe hK hfvK he⟩
    exact dpremB_E hB (hpK pr hpr) hK hD (hF.goodPrems pr hpr) (fun h => ⟨h, hin, hx⟩) (hp pr hpr)
termination_by structural _ _ _ _ _ _ hd => hd

/-- **A premise that holds gives its `PremFact`.** -/
theorem dpremB_fact (hB : BuiltinsEF B) {O : ElseI} {els : Prop} :
    ∀ {ρ : VarEnv} {pr : Prem}, GoodXs (evPrem pr) → DPremB (utf8Env B) O els ρ pr →
      PremFact B ρ pr
  | _, _, _, .ifPr h => h
  | _, _, _, .elsePr _ => trivial
  | _, _, _, .letPr h₂ h₁ => ⟨_, h₂, h₁⟩
  | _, _, hG, .rulePr _ he hd =>
    ⟨_, he, fun hin => (dderivesB_E hB (goodXs_rulePr hG).1 hin hd).2⟩
  | _, _, _, .iterOptNone _ _ _ => trivial
  | _, _, _, .iterOptSome _ _ _ _ => trivial
  | _, _, _, .iterList _ _ _ _ _ _ => trivial
  | _, _, _, .iterListN _ _ _ _ _ _ => trivial
termination_by structural _ _ _ hd => hd

/-- **A premise over known variables is a `DPremBE` premise.** -/
theorem dpremB_E (hB : BuiltinsEF B) {O : ElseI} {els els' : Prop} {K : List IL.Id} :
    ∀ {ρ : VarEnv} {pr : Prem}, premDetOk K pr = true → EFOn ρ K → DefsOk ρ →
      GoodXs (evPrem pr) → (els → els') → DPremB (utf8Env B) O els ρ pr →
      DPremBE (utf8Env B) (ElseEF O) els' ρ pr
  | _, _, _, _, _, _, _, .ifPr h => .ifPr h
  | _, _, _, _, _, _, hels, .elsePr h => .elsePr (hels h)
  | _, _, _, _, _, _, _, .letPr h₂ h₁ => .letPr h₂ h₁
  | _, .rulePr _ _ _ e, hok, hK, hD, hG, _, .rulePr ha he hd =>
    .rulePr ha he (dderivesB_E hB (goodXs_rulePr hG).1 (inEF_of_premDetOk hB hD hG hK hok he) hd).1
  | _, _, _, _, _, _, _, .iterOptNone hd hne hall => .iterOptNone hd hne hall
  | _, _, hok, hK, hD, hG, hels, .iterOptSome (row := row) hd hne hs hp => by
    have hok' := premDetOk_iterPr hok
    have hG' := goodXs_iterPr hG
    have hrow := ef_domSomes (ef_evalDoms hB hD hG'.2 hK hok'.1 hd) hs
    exact .iterOptSome hd hne hs
      (dpremB_E hB hok'.2 (efOn_bindVals hK hrow) (defsOk_bindVals hD row) hG'.1 hels hp)
  | _, _, hok, hK, hD, hG, hels, .iterList hit hd hne hl hk hp => by
    have hok' := premDetOk_iterPr hok
    have hG' := goodXs_iterPr hG
    have hx := ef_evalDoms hB hD hG'.2 hK hok'.1 hd
    exact .iterList hit hd hne hl hk fun r hr =>
      dpremB_E hB hok'.2 (efOn_bindVals hK (ef_rows hx hl none _ r hr)) (defsOk_bindVals hD r)
        hG'.1 hels (hp r hr)
  | _, _, hok, hK, hD, hG, hels, .iterListN hd he hk hl hlen hp => by
    have hok' := premDetOk_iterPr hok
    have hG' := goodXs_iterPr hG
    have hx := ef_evalDoms hB hD hG'.2 hK hok'.1 hd
    exact .iterListN hd he hk hl hlen fun r hr =>
      dpremB_E hB hok'.2 (efOn_bindVals hK (ef_rows hx hl _ _ r hr)) (defsOk_bindVals hD r)
        hG'.1 hels (hp r hr)
termination_by structural _ _ _ _ _ _ _ hd => hd
end

end Silmaril.Wasm.SpecTec.Sim.Round7.Determ
