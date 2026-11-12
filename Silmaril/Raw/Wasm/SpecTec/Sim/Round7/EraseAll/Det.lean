module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseAll.DetMode

/-!
# Round 7, the export swap: derivations from swap-set inputs bind swap-set quantifiers (unrefined)

`dderivesB_AI`, the `AllIn Q` copy of `Round7.Determ.dderivesB_E`, for the relations of the
checked part of the script (`grE`): in `utf8Env B`, under the hypotheses of the evaluator-level
erasure (`Hyps Q grE gdE (utf8Env B)`), every `DDerivesB` derivation at a value whose input is in
the swap set is a `DDerivesBQ (AllIn Q)` derivation, and its value is in the swap set. Its
`otherwise` premises are read at swap-set inputs only (`ElseAI Q O`).

The proof is the original's, by structural recursion on the derivation: each premise gives its
`PremFactQ`, the mode check is sound (`aiOn_ruleK`), and every premise is rebuilt with its relation
premises, whose inputs are known (`premDetOk`), through the recursion. The syntactic facts are
the kernel checks `xRelsOk_fixed` (premises) and `xAltsOk_fixed` (conclusion alternatives) in
place of the original's `GoodXs`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (tyA TypsOk typsOk_empty typsOk_of_typs)
open Silmaril.Wasm.SpecTec.Sim.Round7.Transfer (bindParams_nil)
open Silmaril.Wasm.SpecTec.Sim.Round7.Determ (premDetOk fvIn detFacts premDetOk_rulePr
  premDetOk_iterPr quantNames ruleK)
open Round6.Reading (DDerivesB DPremB conclAlts)

variable {Q : Value → Prop} {B : Builtins}

/-! ## The syntactic facts at one rule -/

theorem reach_of_grE {x : String} (h : grE x = true) : (0, x) ∈ Script.stepReach := by
  unfold grE stepReachE at h
  exact (List.mem_filter.1 (List.contains_iff_mem.1 h)).1

theorem defsG_empty {gd : String → Bool} : DefsG gd VarEnv.empty := fun _ hp => by cases hp

/-- What the kernel checks say about one rule of a checked relation. -/
structure XFacts (e : Exp) (prems : List Prem) : Prop where
  prems : ∀ pr ∈ prems, xPrem grE gdE pr = true
  alts : ∀ e' ∈ conclAlts e, xExp grE gdE e' = true

theorem xFacts {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i : Nat}
    {nm : IL.Id} {qs : List Param} {e : Exp} {prems : List Prem} (hx : grE x = true)
    (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e prems)) : XFacts e prems := by
  have hr : Rule.ruleD nm qs op e prems ∈ rules := List.mem_of_getElem? hrule
  have hx₁ := rels_utf8Env B x _ hx hrel _ hr
  simp only [xRule, Bool.and_eq_true] at hx₁
  rw [findRel?_utf8Env] at hrel
  have h := List.all_eq_true.1 xAltsOk_fixed _ (mem_rels_of_findRel' hrel)
  simp only [hx, Bool.not_true, Bool.false_or, List.all_eq_true] at h
  have h₂ := h _ hr
  simp only [List.all_eq_true] at h₂
  refine ⟨xPrems_mem hx₁.2, fun e' he' => ?_⟩
  rcases List.mem_cons.1 he' with rfl | he'
  · exact hx₁.1
  · exact h₂ e' he'

/-! ## Inputs of relation premises -/

theorem inAI_of_tupE (H : Hyps Q grE gdE (utf8Env B)) {ρ : VarEnv} {K : List IL.Id} {a : Exp}
    {rest : List Exp} {w : Value} (hD : DefsG gdE ρ) (hxa : xExp grE gdE a = true)
    (hK : AIOn Q ρ K) (hfv : fvIn K a = true)
    (he : EvalExp (utf8Env B) ρ (.tupE (a :: rest)) w) : InAI Q w := by
  obtain ⟨va, vs, rfl, ha⟩ := Determ.evalExp_tupE_cons he
  have hva : AllIn Q va := ai_eval_on H hD hxa hK hfv ha
  intro a' r' heq
  cases heq
  exact hva

theorem inAI_of_premDetOk (H : Hyps Q grE gdE (utf8Env B)) {ρ : VarEnv} {K : List IL.Id}
    {x : IL.Id} {args : List Arg} {op : MixopS} {e : Exp} {w : Value} (hD : DefsG gdE ρ)
    (hX : xPrem grE gdE (.rulePr x args op e) = true) (hK : AIOn Q ρ K)
    (hok : premDetOk K (.rulePr x args op e) = true) (he : EvalExp (utf8Env B) ρ e w) :
    InAI Q w := by
  obtain ⟨a, rest, rfl, hfv⟩ := premDetOk_rulePr hok
  have hxa : xExp grE gdE a = true := by
    simp only [xPrem, xExp, xExps, Bool.and_eq_true] at hX
    exact hX.2.1
  exact inAI_of_tupE H hD hxa hK hfv he

theorem xPrem_rulePr {x : IL.Id} {args : List Arg} {op : MixopS} {e : Exp}
    (h : xPrem grE gdE (.rulePr x args op e) = true) : grE x = true := by
  simp only [xPrem, Bool.and_eq_true] at h
  exact h.1.1

theorem xPrem_iterPr {pr : Prem} {it : Iter} {ds : List Dom}
    (h : xPrem grE gdE (.iterPr pr (.mk it ds)) = true) :
    xPrem grE gdE pr = true ∧ xDoms grE gdE ds = true := by
  simp only [xPrem, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.2⟩

mutual
/-- **Rule quantifiers in the swap set.** -/
theorem dderivesB_AI (H : Hyps Q grE gdE (utf8Env B)) {O : ElseI} :
    ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}, grE x = true → InAI Q v →
      DDerivesB (utf8Env B) O x op args v →
      DDerivesBQ (AllIn Q) (utf8Env B) (ElseAI Q O) x op args v ∧ AllIn Q v
  | _, _, _, _, hx, hin, .rule (σ := σ) (ρ₀ := ρ₀) hrel hrule halt hps hq he hp => by
    have hrel' := hrel
    rw [findRel?_utf8Env] at hrel'
    have hF := detFacts (reach_of_grE hx) hrel' hrule
    have hX := xFacts hx hrel hrule
    have hρ : ρ₀ = VarEnv.empty := bindParams_nil (hF.params ▸ hps)
    have hD : DefsG gdE (ρ₀.bindVals σ) := hρ ▸ defsG_bindVals defsG_empty σ
    have hT : TypsOk tyA (ρ₀.bindVals σ) := hρ ▸ typsOk_of_typs (typsOk_empty tyA) rfl
    obtain ⟨-, hqK, hfvK, hpK⟩ := hF.concl _ halt
    have hfact : ∀ pr ∈ _, PremFactQ Q (utf8Env B) (ρ₀.bindVals σ) pr := fun pr hpr =>
      dpremB_factQ H (hX.prems pr hpr) (hp pr hpr)
    have hK := aiOn_ruleK H hD hT hq he hin hX.prems hfact
    have hxf : QuantsP (AllIn Q) (ρ₀.bindVals σ) _ := fun y t w hy hw =>
      hK y (List.contains_iff_mem.1 (List.all_eq_true.1 hqK y (List.mem_filterMap.2 ⟨_, hy, rfl⟩)))
        w hw
    refine ⟨.rule (σ := σ) hrel hrule halt hps hq hxf he fun pr hpr => ?_,
      ai_eval_on H hD (hX.alts _ halt) hK hfvK he⟩
    exact dpremB_AI H (hpK pr hpr) hK hD (hX.prems pr hpr) (fun h => ⟨h, hin, hx⟩) (hp pr hpr)
termination_by structural _ _ _ _ _ _ hd => hd

/-- **A premise that holds gives its `PremFactQ`.** -/
theorem dpremB_factQ (H : Hyps Q grE gdE (utf8Env B)) {O : ElseI} {els : Prop} :
    ∀ {ρ : VarEnv} {pr : Prem}, xPrem grE gdE pr = true → DPremB (utf8Env B) O els ρ pr →
      PremFactQ Q (utf8Env B) ρ pr
  | _, _, _, .ifPr h => h
  | _, _, _, .elsePr _ => trivial
  | _, _, _, .letPr h₂ h₁ => ⟨_, h₂, h₁⟩
  | _, _, hX, .rulePr _ he hd =>
    ⟨_, he, fun hin => (dderivesB_AI H (xPrem_rulePr hX) hin hd).2⟩
  | _, _, _, .iterOptNone _ _ _ => trivial
  | _, _, _, .iterOptSome _ _ _ _ => trivial
  | _, _, _, .iterList _ _ _ _ _ _ => trivial
  | _, _, _, .iterListN _ _ _ _ _ _ => trivial
termination_by structural _ _ _ hd => hd

/-- **A premise over known variables is a `DPremBQ (AllIn Q)` premise.** -/
theorem dpremB_AI (H : Hyps Q grE gdE (utf8Env B)) {O : ElseI} {els els' : Prop}
    {K : List IL.Id} :
    ∀ {ρ : VarEnv} {pr : Prem}, premDetOk K pr = true → AIOn Q ρ K → DefsG gdE ρ →
      xPrem grE gdE pr = true → (els → els') → DPremB (utf8Env B) O els ρ pr →
      DPremBQ (AllIn Q) (utf8Env B) (ElseAI Q O) els' ρ pr
  | _, _, _, _, _, _, _, .ifPr h => .ifPr h
  | _, _, _, _, _, _, hels, .elsePr h => .elsePr (hels h)
  | _, _, _, _, _, _, _, .letPr h₂ h₁ => .letPr h₂ h₁
  | _, .rulePr _ _ _ e, hok, hK, hD, hX, _, .rulePr ha he hd =>
    .rulePr ha he (dderivesB_AI H (xPrem_rulePr hX) (inAI_of_premDetOk H hD hX hK hok he) hd).1
  | _, _, _, _, _, _, _, .iterOptNone hd hne hall => .iterOptNone hd hne hall
  | _, _, hok, hK, hD, hX, hels, .iterOptSome (row := row) hd hne hs hp => by
    have hok' := premDetOk_iterPr hok
    have hX' := xPrem_iterPr hX
    have hrow := ai_domSomes (ai_evalDoms H hD hX'.2 hK hok'.1 hd) hs
    exact .iterOptSome hd hne hs
      (dpremB_AI H hok'.2 (aiOn_bindVals hK hrow) (defsG_bindVals hD row) hX'.1 hels hp)
  | _, _, hok, hK, hD, hX, hels, .iterList hit hd hne hl hk hp => by
    have hok' := premDetOk_iterPr hok
    have hX' := xPrem_iterPr hX
    have hx := ai_evalDoms H hD hX'.2 hK hok'.1 hd
    exact .iterList hit hd hne hl hk fun r hr =>
      dpremB_AI H hok'.2 (aiOn_bindVals hK (ai_rows hx hl none _ r hr)) (defsG_bindVals hD r)
        hX'.1 hels (hp r hr)
  | _, _, hok, hK, hD, hX, hels, .iterListN hd he hk hl hlen hp => by
    have hok' := premDetOk_iterPr hok
    have hX' := xPrem_iterPr hX
    have hx := ai_evalDoms H hD hX'.2 hK hok'.1 hd
    exact .iterListN hd he hk hl hlen fun r hr =>
      dpremB_AI H hok'.2 (aiOn_bindVals hK (ai_rows hx hl _ _ r hr)) (defsG_bindVals hD r)
        hX'.1 hels (hp r hr)
termination_by structural _ _ _ _ _ _ _ hd => hd
end

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
