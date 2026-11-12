module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseDer.AIG

/-!
# Round 7, moving derivations across erasure: `otherwise` (unrefined)

`otherwiseAtB env x args i v` says no earlier rule of `x` fires at a value with the left-hand side
of `v` (relation premises read by `DDerivesB env noElse`). It reads alike at a swap-set input and
at its erasure (`otherwiseAtB_erase_iff`), by strong induction on `i`, as
`Round7.Determ.otherwiseAtB_iff` does for the change of environment:

* a rule body at a swap-set input goes to the erased side (`ruleBodyB_fwd`): the mode analysis of
  `Round7.EraseAll.dderivesB_AI` puts its quantifiers in the swap set, and the instance-level
  transfer `inst_fwd` (the rule case of `dderivesB_fwd`) moves it;
* a rule body on the erased side at an erased input comes back (`ruleBodyB_bwd`), by the same
  analysis at `EImg Q` and `inst_bwd`;
* the bodies' own `otherwise` premises are read at values with the same input, where the
  induction hypothesis applies.

Then the two transfers hold with `otherwise` read as SpecTec reads it (`dderivesB_erase_fwd`,
`dderivesB_erase_bwd`), for the relations of the checked part.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (DDerivesBQ DPremBQ QuantsP Hyps xPrem xExp eraseP
  grE gdE InAI ElseAI DefsG)
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (tyA TypsOk typsOk_empty typsOk_of_typs)
open Silmaril.Wasm.SpecTec.Sim.Round7.Determ (quantNames premW_dpremB dpremB_premW
  otherwiseAtB_unfold)
open Round6.Reading (DDerivesB DPremB conclAlts RuleBodyB otherwiseAtB otherwiseB SStepB)

variable {Q : Value → Prop}

/-! ## One rule instance -/

section Inst

set_option linter.unusedSectionVars false

variable {gr gd : String → Bool} {env : Env} (H : Hyps Q gr gd env) (hF : AllRFacts gr gd env)
include H hF

/-- **A swap-set rule instance goes to the erased side.** -/
theorem inst_fwd (hT : TypFwd Q gd env) {O₁ O' : ElseI}
    (hO : ∀ x args i v, O₁ x args i v → O' x (args.map eraseA) i (eraseV v))
    {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i : Nat}
    {nm : IL.Id} {qs : List Param} {e e' : Exp} {prems : List Prem} {σ : List (IL.Id × Value)}
    {v : Value} {els els' : Prop} (hx : gr x = true)
    (hrel : env.findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e prems)) (halt : e' ∈ conclAlts e)
    (hq : QuantsOk env (VarEnv.empty.bindVals σ) qs)
    (hxq : QuantsP (AllIn Q) (VarEnv.empty.bindVals σ) qs)
    (he : EvalExp env (VarEnv.empty.bindVals σ) e' v) (hels : els → els')
    (hp : ∀ pr ∈ prems, DPremBQ (AllIn Q) env O₁ els (VarEnv.empty.bindVals σ) pr) :
    QuantsOk env (VarEnv.empty.bindVals (σ.map eraseP)) qs ∧
      EvalExp env (VarEnv.empty.bindVals (σ.map eraseP)) e' (eraseV v) ∧
      ∀ pr ∈ prems, DPremB env O' els' (VarEnv.empty.bindVals (σ.map eraseP)) pr := by
  have hRF := hF hx hrel hrule
  have hR : ∀ S : Sets, varsIn (quantNames qs) S = true →
      ErRel Q gd S (VarEnv.empty.bindVals σ) (VarEnv.empty.bindVals (σ.map eraseP)) :=
    fun S hS => erRel_inst (ai_of_varsIn hxq hS)
  obtain ⟨hxe, hfe⟩ := hRF.alts _ halt
  refine ⟨fun y ty hy => ?_, (evalExp_fwd H (hR _ hfe) hxe he).1, fun pr hpr => ?_⟩
  · obtain ⟨w, hw, hty⟩ := hq y ty hy
    obtain ⟨ht, hft⟩ := hRF.quants y ty hy
    refine ⟨eraseV w, by rw [findVal?_inst, hw]; rfl, ?_⟩
    exact hT _ _ _ _ (hR _ hft) rfl rfl rfl rfl rfl ht (hxq y ty w hy hw) hty
  · exact dpremB_fwd H hF hT hO (hRF.prems pr hpr).1 (hR _ (hRF.prems pr hpr).2) hels (hp pr hpr)

/-- **A rule instance on the erased side comes back.** -/
theorem inst_bwd (hT : TypBwd Q gd env) (hQA : ∀ r, Q r → AllIn Q r) {O₂ O : ElseI}
    (hO : ∀ x args i v', O₂ x args i v' → args = [] → AllIn (EImg Q) v' →
      O x [] i (unerase Q v'))
    {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i : Nat}
    {nm : IL.Id} {qs : List Param} {e e' : Exp} {prems : List Prem} {σ' : List (IL.Id × Value)}
    {v' : Value} {els' els : Prop} (hx : gr x = true)
    (hrel : env.findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e prems)) (halt : e' ∈ conclAlts e)
    (hq : QuantsOk env (VarEnv.empty.bindVals σ') qs)
    (hxq : QuantsP (AllIn (EImg Q)) (VarEnv.empty.bindVals σ') qs)
    (he : EvalExp env (VarEnv.empty.bindVals σ') e' v') (hels : els' → els)
    (hp : ∀ pr ∈ prems, DPremBQ (AllIn (EImg Q)) env O₂ els' (VarEnv.empty.bindVals σ') pr) :
    QuantsOk env (VarEnv.empty.bindVals (σ'.map (uneraseP Q))) qs ∧
      EvalExp env (VarEnv.empty.bindVals (σ'.map (uneraseP Q))) e' (unerase Q v') ∧
      ∀ pr ∈ prems, DPremB env O els (VarEnv.empty.bindVals (σ'.map (uneraseP Q))) pr := by
  have hRF := hF hx hrel hrule
  have hR : ∀ S : Sets, varsIn (quantNames qs) S = true →
      ErRel Q gd S (VarEnv.empty.bindVals (σ'.map (uneraseP Q))) (VarEnv.empty.bindVals σ') :=
    fun S hS => erRel_unerase hQA (ai_of_varsIn hxq hS)
  obtain ⟨hxe, hfe⟩ := hRF.alts _ halt
  obtain ⟨v, hv, hve, hva⟩ := evalExp_bwd H (hR _ hfe) hxe he
  have hvu : unerase Q v' = v := hve ▸ unerase_eraseV H.inj v hva
  refine ⟨fun y ty hy => ?_, hvu ▸ hv, fun pr hpr => ?_⟩
  · obtain ⟨w', hw', hty⟩ := hq y ty hy
    obtain ⟨ht, hft⟩ := hRF.quants y ty hy
    obtain ⟨hu₁, hu₂⟩ := unerase_eImg hQA w' (hxq y ty w' hy hw')
    refine ⟨unerase Q w', by rw [findVal?_uninst, hw']; rfl, ?_⟩
    exact hT _ _ _ _ (hR _ hft) rfl rfl rfl rfl rfl ht hu₁ (by rw [hu₂]; exact hty)
  · exact dpremB_bwd H hF hT hQA hO (hRF.prems pr hpr).1 (hR _ (hRF.prems pr hpr).2) hels
      (hp pr hpr)

end Inst

/-! ## Pairs -/

theorem eraseV_eq_pair {v a b : Value} (h : eraseV v = .tuple [a, b]) :
    ∃ a₀ b₀, v = .tuple [a₀, b₀] ∧ eraseV a₀ = a ∧ eraseV b₀ = b := by
  rcases v with _ | _ | _ | vs | _ | _ | _ | (_ | _) <;> simp [eraseV] at h
  rw [eraseVs_eq_map] at h
  match vs, h with
  | [a₀, b₀], h =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at h
    exact ⟨a₀, b₀, rfl, h.1, h.2.1⟩

theorem inAI_pair {Q : Value → Prop} {a b : Value} (h : InAI Q (.tuple [a, b])) : AllIn Q a :=
  h a [b] rfl

theorem inAI_of_pair {Q : Value → Prop} {a b : Value} (h : AllIn Q a) : InAI Q (.tuple [a, b]) :=
  fun a' rest heq => by cases heq; exact h

theorem unerase_pair (hQ : QInj Q) {a : Value} (ha : AllIn Q a) (c : Value) :
    unerase Q (.tuple [eraseV a, c]) = .tuple [a, unerase Q c] := by
  simp [unerase, uneraseS, unerase_eraseV hQ a ha]

theorem inAI_of_allIn {Q : Value → Prop} {v : Value} (h : AllIn Q v) : InAI Q v :=
  fun a rest heq => by subst heq; exact h.1

/-! ## Rule bodies at a checked part -/

section Body

set_option linter.unusedSectionVars false

variable {B : Builtins} {gr gd : String → Bool} (G : GFacts gr gd B)
  (H : Hyps Q gr gd (utf8Env B)) (H' : Hyps (EImg Q) gr gd (utf8Env B))
  (hT : TypFwd Q gd (utf8Env B)) (hTb : TypBwd Q gd (utf8Env B))
  (hQA : ∀ r, Q r → AllIn Q r)
include G H H' hT hTb hQA

/-- **A rule body at a swap-set input goes to the erased side**, and its value is in the swap
set. -/
theorem ruleBodyB_fwd {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {j : Nat} {r : Rule} (hx : gr x = true)
    (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules)) (hr : rules[j]? = some r)
    {els els' : Prop} (hels : els → els') {args : List ArgV} {w : Value} (hin : InAI Q w)
    (h : RuleBodyB (utf8Env B) (DDerivesB (utf8Env B) noElse) els ps args op r w) :
    RuleBodyB (utf8Env B) (DDerivesB (utf8Env B) noElse) els' ps (args.map eraseA) op r
      (eraseV w) ∧ AllIn Q w := by
  obtain ⟨nm, qs, op', e, prems⟩ := r
  obtain ⟨e', he', hop, ρ₀, σ, hps, hq, he, hp⟩ := h
  have hr' : rules[j]? = some (.ruleD nm qs op e prems) := hop ▸ hr
  subst hop
  have hRF := G.rf hx hrel hr'
  obtain ⟨rfl, rfl⟩ := bindParams_nil_args (hRF.params ▸ hps)
  have hrel' := hrel
  rw [findRel?_utf8Env] at hrel'
  have hFd := Determ.detFacts (G.reach _ hx) hrel' hr'
  have hD : DefsG gd (VarEnv.empty.bindVals σ) :=
    EraseAll.defsG_bindVals EraseAll.defsG_empty σ
  have hT0 : TypsOk tyA (VarEnv.empty.bindVals σ) := typsOk_of_typs (typsOk_empty tyA) rfl
  obtain ⟨-, hqK, hfvK, hpK⟩ := hFd.concl _ he'
  have hp' : ∀ pr ∈ prems, DPremB (utf8Env B) noElse els (VarEnv.empty.bindVals σ) pr :=
    fun pr hpr => premW_dpremB (hp pr hpr)
  have hfact := fun pr hpr => dpremB_factQG G H (hRF.prems pr hpr).1 (hp' pr hpr)
  have hK := EraseAll.aiOn_ruleK H hD hT0 hq he hin (fun pr hpr => (hRF.prems pr hpr).1) hfact
  have hxq : QuantsP (AllIn Q) (VarEnv.empty.bindVals σ) qs := fun y _ w hy hw =>
    hK y (List.contains_iff_mem.1 (List.all_eq_true.1 hqK y (List.mem_filterMap.2 ⟨_, hy, rfl⟩)))
      w hw
  have hpQ : ∀ pr ∈ prems, DPremBQ (AllIn Q) (utf8Env B) (ElseAIg gr Q noElse) els
      (VarEnv.empty.bindVals σ) pr := fun pr hpr =>
    dpremB_AIG G H (hpK pr hpr) hK hD (hRF.prems pr hpr).1 id (hp' pr hpr)
  obtain ⟨hq', he'', hp''⟩ := inst_fwd H G.rf hT (O₁ := ElseAIg gr Q noElse) (O' := noElse)
    (fun _ _ _ _ h => h.1.elim) hx hrel hr' he' hq hxq he hels hpQ
  exact ⟨⟨e', he', rfl, VarEnv.empty, σ.map eraseP, hRF.params ▸ rfl, hq', he'',
    fun pr hpr => dpremB_premW (hp'' pr hpr)⟩, EraseAll.ai_eval_on H hD (hRF.alts _ he').1 hK hfvK he⟩

/-- **A rule body on the erased side at an erased input comes back**, and its value is in the
erased swap set. -/
theorem ruleBodyB_bwd {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {j : Nat} {r : Rule} (hx : gr x = true)
    (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules)) (hr : rules[j]? = some r)
    {els' els : Prop} (hels : els' → els) {args : List ArgV} {w' : Value} (hin : InAI (EImg Q) w')
    (h : RuleBodyB (utf8Env B) (DDerivesB (utf8Env B) noElse) els' ps args op r w') :
    RuleBodyB (utf8Env B) (DDerivesB (utf8Env B) noElse) els ps [] op r (unerase Q w') ∧
      AllIn (EImg Q) w' ∧ args = [] := by
  obtain ⟨nm, qs, op', e, prems⟩ := r
  obtain ⟨e', he', hop, ρ₀, σ', hps, hq, he, hp⟩ := h
  have hr' : rules[j]? = some (.ruleD nm qs op e prems) := hop ▸ hr
  subst hop
  have hRF := G.rf hx hrel hr'
  obtain ⟨rfl, rfl⟩ := bindParams_nil_args (hRF.params ▸ hps)
  have hrel' := hrel
  rw [findRel?_utf8Env] at hrel'
  have hFd := Determ.detFacts (G.reach _ hx) hrel' hr'
  have hD : DefsG gd (VarEnv.empty.bindVals σ') :=
    EraseAll.defsG_bindVals EraseAll.defsG_empty σ'
  have hT0 : TypsOk tyA (VarEnv.empty.bindVals σ') := typsOk_of_typs (typsOk_empty tyA) rfl
  obtain ⟨-, hqK, hfvK, hpK⟩ := hFd.concl _ he'
  have hp' : ∀ pr ∈ prems, DPremB (utf8Env B) noElse els' (VarEnv.empty.bindVals σ') pr :=
    fun pr hpr => premW_dpremB (hp pr hpr)
  have hfact := fun pr hpr => dpremB_factQG G H' (hRF.prems pr hpr).1 (hp' pr hpr)
  have hK := EraseAll.aiOn_ruleK H' hD hT0 hq he hin (fun pr hpr => (hRF.prems pr hpr).1) hfact
  have hxq : QuantsP (AllIn (EImg Q)) (VarEnv.empty.bindVals σ') qs := fun y _ w hy hw =>
    hK y (List.contains_iff_mem.1 (List.all_eq_true.1 hqK y (List.mem_filterMap.2 ⟨_, hy, rfl⟩)))
      w hw
  have hpQ : ∀ pr ∈ prems, DPremBQ (AllIn (EImg Q)) (utf8Env B) (ElseAIg gr (EImg Q) noElse) els'
      (VarEnv.empty.bindVals σ') pr := fun pr hpr =>
    dpremB_AIG G H' (hpK pr hpr) hK hD (hRF.prems pr hpr).1 id (hp' pr hpr)
  obtain ⟨hq', he'', hp''⟩ := inst_bwd H G.rf hTb hQA (O₂ := ElseAIg gr (EImg Q) noElse)
    (O := noElse) (fun _ _ _ _ h _ _ => h.1.elim) hx hrel hr' he' hq hxq he hels hpQ
  exact ⟨⟨e', he', rfl, VarEnv.empty, σ'.map (uneraseP Q), hRF.params ▸ rfl, hq', he'',
    fun pr hpr => dpremB_premW (hp'' pr hpr)⟩,
    EraseAll.ai_eval_on H' hD (hRF.alts _ he').1 hK hfvK he, rfl⟩

/-- **`otherwise` reads alike at a swap-set input and at its erasure.** -/
theorem otherwiseAtB_erase_iff {x : IL.Id} (hx : gr x = true) :
    ∀ i v, InAI Q v → ∀ args,
      (otherwiseAtB (utf8Env B) x args i v ↔
        otherwiseAtB (utf8Env B) x (args.map eraseA) i (eraseV v)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro v hv args
    rw [otherwiseAtB_unfold, otherwiseAtB_unfold]
    constructor
    · intro hc j hj ps op t rules r hrel hr w' hS hbody
      obtain ⟨a, b, c', hve, rfl⟩ := hS
      obtain ⟨a₀, b₀, rfl, rfl, rfl⟩ := eraseV_eq_pair hve
      have ha₀ : AllIn Q a₀ := hv a₀ [b₀] rfl
      have hin' : InAI (EImg Q) (.tuple [eraseV a₀, c']) := inAI_of_pair (allIn_eImg_eraseV a₀ ha₀)
      have hw'a := (ruleBodyB_bwd G H H' hT hTb hQA hx hrel hr id hin' hbody).2.1
      obtain ⟨-, hu⟩ := unerase_eImg hQA _ hw'a
      have hinu : InAI Q (unerase Q (.tuple [eraseV a₀, c'])) := by
        rw [unerase_pair H.inj ha₀]; exact inAI_of_pair ha₀
      have hels : otherwiseAtB (utf8Env B) x (args.map eraseA) j (.tuple [eraseV a₀, c']) →
          otherwiseAtB (utf8Env B) x args j (unerase Q (.tuple [eraseV a₀, c'])) := fun h =>
        (ih j hj _ hinu args).2 (by rw [hu]; exact h)
      obtain ⟨hb, -, hargs⟩ := ruleBodyB_bwd G H H' hT hTb hQA hx hrel hr hels hin' hbody
      have hargs' : args = [] := List.map_eq_nil_iff.1 hargs
      subst hargs'
      refine hc j hj ps op t rules r hrel hr _ ?_ hb
      rw [unerase_pair H.inj ha₀]
      exact ⟨a₀, b₀, _, rfl, rfl⟩
    · intro hs j hj ps op t rules r hrel hr w hS hbody
      obtain ⟨a, b, c, rfl, rfl⟩ := hS
      have ha : AllIn Q a := hv a [b] rfl
      have hinw : InAI Q (.tuple [a, c]) := inAI_of_pair ha
      obtain ⟨hb, -⟩ := ruleBodyB_fwd G H H' hT hTb hQA hx hrel hr (ih j hj _ hinw args).1 hinw hbody
      refine hs j hj ps op t rules r hrel hr _ ?_ hb
      exact ⟨eraseV a, eraseV b, eraseV c, rfl, rfl⟩

/-! ## The transfers with SpecTec's `otherwise` -/

/-- **A derivation at a swap-set input goes to the erased side**, `otherwise` read as SpecTec
reads it. -/
theorem dderivesB_erase_fwd {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}
    (hx : gr x = true) (hin : InAI Q v)
    (h : DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op args v) :
    DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op (args.map eraseA) (eraseV v) ∧
      AllIn Q v := by
  obtain ⟨hQd, hv⟩ := dderivesB_AIg G H hx hin h
  refine ⟨dderivesB_fwd H G.rf hT (fun y as₀ i u hO => ?_) hx hQd, hv⟩
  exact (otherwiseAtB_erase_iff G H H' hT hTb hQA hO.2.2 i u hO.2.1 as₀).1 hO.1

/-- **A derivation on the erased side at an erased input comes back**, `otherwise` read as
SpecTec reads it. -/
theorem dderivesB_erase_bwd {x : IL.Id} {op : MixopS} {args' : List ArgV} {v' : Value}
    (hx : gr x = true) (hin : InAI (EImg Q) v')
    (h : DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op args' v') :
    args' = [] ∧ DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op [] (unerase Q v') ∧
      AllIn (EImg Q) v' := by
  obtain ⟨hQd, hv⟩ := dderivesB_AIg G H' hx hin h
  have hO : ∀ y as₀ i u, ElseAIg gr (EImg Q) (otherwiseB (utf8Env B)) y as₀ i u → as₀ = [] →
      AllIn (EImg Q) u → otherwiseB (utf8Env B) y [] i (unerase Q u) := by
    intro y as₀ i u hO has hu
    subst has
    obtain ⟨hu₁, hu₂⟩ := unerase_eImg hQA u hu
    refine (otherwiseAtB_erase_iff G H H' hT hTb hQA hO.2.2 i _ (inAI_of_allIn hu₁) []).2 ?_
    rw [hu₂]; exact hO.1
  obtain ⟨h₁, h₂⟩ := dderivesB_bwd H G.rf hTb hQA hO hx hQd
  exact ⟨h₁, h₂, hv⟩

end Body

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
