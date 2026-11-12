module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Determ.Det

/-!
# Round 7, determination: `otherwise` reads alike in the two environments

`otherwiseB env x args i v` says that no earlier rule of `x` fires at any `w` with the same
left-hand side as `v`, where "fires" is `RuleBodyB` with relation premises read by
`DDerivesB env noElse`. At an `ExpFree` input the two environments agree on it
(`otherwiseAtB_iff`), by strong induction on `i`:

* a rule body in `simEnv B` is one in `utf8Env B` by monotonicity (`ruleBodyB_utf8Env`);
* a rule body in `utf8Env B` at an `ExpFree` input is one in `simEnv B` by determination
  (`ruleBodyB_simEnv`): the rule case of `Round7.Determ.dderivesB_E`, followed by the transfer
  `Round7.Transfer.dpremB_simEnv_of_E`;
* the bodies' own `otherwise` premises are read at `w`, whose input is that of `v`, so the
  induction hypothesis applies to them.

`sStepB_utf8Env_iff` is then the agreement of SpecTec's `Step` at an `ExpFree` configuration.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Determ

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (ExpFree tyA TypsOk typsOk_empty typsOk_of_typs
  quantsOk_utf8Env_iff)
open Silmaril.Wasm.SpecTec.Sim.Round7.Transfer (DDerivesBE DPremBE QuantsExpFree bindParams_nil
  dderivesB_simEnv_of_E dpremB_simEnv_of_E dderivesB_of_E)
open Round6.Reading (DDerivesB DPremB conclAlts RuleBodyB otherwiseAtB otherwiseB SStepB)

variable {B : Builtins}

/-! ## `PremW` over `noElse` relations is `DPremB` at `noElse` -/

theorem premW_dpremB {env : Env} {els : Prop} :
    ∀ {ρ : VarEnv} {pr : Prem}, PremW env (DDerivesB env noElse) els ρ pr →
      DPremB env noElse els ρ pr
  | _, _, .ifPr h => .ifPr h
  | _, _, .elsePr h => .elsePr h
  | _, _, .letPr h₂ h₁ => .letPr h₂ h₁
  | _, _, .rulePr ha he hd => .rulePr ha he hd
  | _, _, .iterOptNone hd hne hall => .iterOptNone hd hne hall
  | _, _, .iterOptSome hd hne hs hp => .iterOptSome hd hne hs (premW_dpremB hp)
  | _, _, .iterList hit hd hne hl hk hp => .iterList hit hd hne hl hk fun r hr => premW_dpremB (hp r hr)
  | _, _, .iterListN hd he hk hl hlen hp =>
    .iterListN hd he hk hl hlen fun r hr => premW_dpremB (hp r hr)

theorem dpremB_premW {env : Env} {els : Prop} :
    ∀ {ρ : VarEnv} {pr : Prem}, DPremB env noElse els ρ pr →
      PremW env (DDerivesB env noElse) els ρ pr
  | _, _, .ifPr h => .ifPr h
  | _, _, .elsePr h => .elsePr h
  | _, _, .letPr h₂ h₁ => .letPr h₂ h₁
  | _, _, .rulePr ha he hd => .rulePr ha he hd
  | _, _, .iterOptNone hd hne hall => .iterOptNone hd hne hall
  | _, _, .iterOptSome hd hne hs hp => .iterOptSome hd hne hs (dpremB_premW hp)
  | _, _, .iterList hit hd hne hl hk hp => .iterList hit hd hne hl hk fun r hr => dpremB_premW (hp r hr)
  | _, _, .iterListN hd he hk hl hlen hp =>
    .iterListN hd he hk hl hlen fun r hr => dpremB_premW (hp r hr)

/-! ## Changing the reading of `otherwise` -/

mutual
/-- A derivation read with `O` is one read with any `O'` that `O` implies. -/
theorem dderivesB_mapO {env : Env} {O O' : ElseI} (hO : ∀ x args i v, O x args i v → O' x args i v) :
    ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value},
      DDerivesB env O x op args v → DDerivesB env O' x op args v
  | _, _, _, _, .rule hrel hrule halt hps hq he hp =>
    .rule hrel hrule halt hps hq he fun pr hpr => dpremB_mapO hO (hO _ _ _ _) (hp pr hpr)
termination_by structural _ _ _ _ hd => hd

/-- `dderivesB_mapO` for premises. -/
theorem dpremB_mapO {env : Env} {O O' : ElseI} (hO : ∀ x args i v, O x args i v → O' x args i v)
    {els els' : Prop} (hels : els → els') :
    ∀ {ρ : VarEnv} {pr : Prem}, DPremB env O els ρ pr → DPremB env O' els' ρ pr
  | _, _, .ifPr h => .ifPr h
  | _, _, .elsePr h => .elsePr (hels h)
  | _, _, .letPr h₂ h₁ => .letPr h₂ h₁
  | _, _, .rulePr ha he hd => .rulePr ha he (dderivesB_mapO hO hd)
  | _, _, .iterOptNone hd hne hall => .iterOptNone hd hne hall
  | _, _, .iterOptSome hd hne hs hp => .iterOptSome hd hne hs (dpremB_mapO hO hels hp)
  | _, _, .iterList hit hd hne hl hk hp =>
    .iterList hit hd hne hl hk fun r hr => dpremB_mapO hO hels (hp r hr)
  | _, _, .iterListN hd he hk hl hlen hp =>
    .iterListN hd he hk hl hlen fun r hr => dpremB_mapO hO hels (hp r hr)
termination_by structural _ _ hd => hd
end

/-! ## Rule bodies -/

/-- **A rule body in `simEnv B` is one in `utf8Env B`.** -/
theorem ruleBodyB_utf8Env (hBu : ∀ ws, B.call "utf8" ws = none) {els els' : Prop}
    (hels : els → els') {ps : List Param} {args : List ArgV} {op : MixopS} {r : Rule} {w : Value}
    (h : RuleBodyB (simEnv B) (DDerivesB (simEnv B) noElse) els ps args op r w) :
    RuleBodyB (utf8Env B) (DDerivesB (utf8Env B) noElse) els' ps args op r w := by
  obtain ⟨nm, qs, op', e, prems⟩ := r
  obtain ⟨e', he', hop, ρ₀, σ, hps, hq, he, hp⟩ := h
  refine ⟨e', he', hop, ρ₀, σ, hps, Round7.quantsOk_utf8Env hBu hq,
    Round7.evalExp_utf8Env hBu he, fun pr hpr => ?_⟩
  exact dpremB_premW (Round7.dpremB_utf8Env hBu (fun _ _ _ _ h => h) hels
    (premW_dpremB (hp pr hpr)))

/-- **A rule body in `utf8Env B` at an `ExpFree` input is one in `simEnv B`**, for a rule of a
relation `Step` reaches. -/
theorem ruleBodyB_simEnv (hB : BuiltinsEF B) (hBu : ∀ ws, B.call "utf8" ws = none)
    {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {j : Nat}
    {r : Rule} (hx : (0, x) ∈ stepReach) (hrel : (simEnv B).findRel? x = some (ps, op, t, rules))
    (hr : rules[j]? = some r) {els els' : Prop} (hels : els → els') {args : List ArgV}
    {w : Value} (hin : InEF w)
    (h : RuleBodyB (utf8Env B) (DDerivesB (utf8Env B) noElse) els ps args op r w) :
    RuleBodyB (simEnv B) (DDerivesB (simEnv B) noElse) els' ps args op r w := by
  obtain ⟨nm, qs, op', e, prems⟩ := r
  obtain ⟨e', he', hop, ρ₀, σ, hps, hq, he, hp⟩ := h
  have hr' : rules[j]? = some (.ruleD nm qs op e prems) := hop ▸ hr
  have hF := detFacts hx hrel hr'
  subst hop
  have hρ : ρ₀ = VarEnv.empty := bindParams_nil (hF.params ▸ hps)
  have hD : DefsOk (ρ₀.bindVals σ) := hρ ▸ defsOk_bindVals defsOk_empty σ
  have hT : TypsOk tyA (ρ₀.bindVals σ) := hρ ▸ typsOk_of_typs (typsOk_empty tyA) rfl
  obtain ⟨hGe, hqK, _, hpK⟩ := hF.concl _ he'
  have hp' : ∀ pr ∈ prems, DPremB (utf8Env B) noElse els (ρ₀.bindVals σ) pr :=
    fun pr hpr => premW_dpremB (hp pr hpr)
  have hfact : ∀ pr ∈ prems, PremFact B (ρ₀.bindVals σ) pr := fun pr hpr =>
    dpremB_fact hB (hF.goodPrems pr hpr) (hp' pr hpr)
  have hK := efOn_ruleK hB hD hT hq he hin hF.goodPrems hfact
  have hxf : ∀ y t w', Param.expP y t ∈ qs → (ρ₀.bindVals σ).findVal? y = some w' →
      ExpFree w' := fun y t w' hy hw =>
    hK y (List.contains_iff_mem.1 (List.all_eq_true.1 hqK y (List.mem_filterMap.2 ⟨_, hy, rfl⟩)))
      w' hw
  refine ⟨e', he', rfl, ρ₀, σ, hps, (quantsOk_utf8Env_iff hBu hD hT hF.quants hxf).1 hq,
    (evalExp_utf8Env_iff hBu hD (goodEvs_of_goodXs hGe)).1 he, fun pr hpr => ?_⟩
  have hE : DPremBE (utf8Env B) (ElseEF noElse) els (ρ₀.bindVals σ) pr :=
    dpremB_E hB (hpK pr hpr) hK hD (hF.goodPrems pr hpr) id (hp' pr hpr)
  exact dpremB_premW (dpremB_simEnv_of_E hBu (fun _ _ _ _ h => h.1) hels hD hT
    (goodEvs_of_goodXs (hF.goodPrems pr hpr)) hE)

/-! ## `otherwise` -/

theorem inEF_of_sameLhs {v w : Value} (hv : InEF v) (h : SameLhs v w) : InEF w := by
  obtain ⟨a, b, c, rfl, rfl⟩ := h
  intro a' rest heq
  cases heq
  exact hv a [b] rfl

theorem otherwiseAtB_unfold (env : Env) (x : IL.Id) (args : List ArgV) (i : Nat) (v : Value) :
    otherwiseAtB env x args i v ↔ ∀ j, j < i → ∀ ps op t rules r,
      env.findRel? x = some (ps, op, t, rules) → rules[j]? = some r → ∀ w, SameLhs v w →
      ¬ RuleBodyB env (DDerivesB env noElse) (otherwiseAtB env x args j w) ps args op r w := by
  rw [otherwiseAtB]

/-- **`otherwise` reads alike at an `ExpFree` input**, for a relation `Step` reaches. -/
theorem otherwiseAtB_iff (hB : BuiltinsEF B) (hBu : ∀ ws, B.call "utf8" ws = none) {x : IL.Id}
    (hx : (0, x) ∈ stepReach) (args : List ArgV) :
    ∀ i v, InEF v → (otherwiseAtB (utf8Env B) x args i v ↔ otherwiseAtB (simEnv B) x args i v) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro v hv
    rw [otherwiseAtB_unfold, otherwiseAtB_unfold]
    constructor
    · intro hu j hj ps op t rules r hrel hr w hS hbody
      have hw : InEF w := inEF_of_sameLhs hv hS
      have hrel' : (utf8Env B).findRel? x = some (ps, op, t, rules) := by
        rw [Round7.findRel?_utf8Env]; exact hrel
      exact hu j hj ps op t rules r hrel' hr w hS
        (ruleBodyB_utf8Env hBu (ih j hj w hw).2 hbody)
    · intro hs j hj ps op t rules r hrel hr w hS hbody
      have hw : InEF w := inEF_of_sameLhs hv hS
      have hrel' : (simEnv B).findRel? x = some (ps, op, t, rules) := by
        rw [← Round7.findRel?_utf8Env]; exact hrel
      exact hs j hj ps op t rules r hrel' hr w hS
        (ruleBodyB_simEnv hB hBu hx hrel' hr (ih j hj w hw).1 hw hbody)

/-! ## SpecTec's `Step` -/

/-- **SpecTec's `Step` reads alike in the two environments at an `ExpFree` configuration.** -/
theorem sStepB_utf8Env_iff (hB : BuiltinsEF B) (hBu : ∀ ws, B.call "utf8" ws = none)
    {c w : Value} (hc : ExpFree c) : SStepB (utf8Env B) c w ↔ SStepB (simEnv B) c w := by
  have hin : InEF (.tuple [c, w]) := fun a rest heq => by cases heq; exact hc
  constructor
  · intro h
    have hE := (dderivesB_E hB step_mem_stepReach hin h).1
    exact dderivesB_simEnv_of_E hBu (fun y args i v hO =>
      (otherwiseAtB_iff hB hBu hO.2.2 args i v hO.2.1).1 hO.1) step_mem_stepReach hE
  · intro h
    have hU : DDerivesB (utf8Env B) (otherwiseB (simEnv B)) "Step" "%~>%" [] (.tuple [c, w]) :=
      Round7.dderivesB_utf8Env hBu (fun _ _ _ _ h => h) h
    have hE := (dderivesB_E hB step_mem_stepReach hin hU).1
    exact dderivesB_mapO (fun y args i v hO =>
      (otherwiseAtB_iff hB hBu hO.2.2 args i v hO.2.1).2 hO.1) (dderivesB_of_E hE)

end Silmaril.Wasm.SpecTec.Sim.Round7.Determ
