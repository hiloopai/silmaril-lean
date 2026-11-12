module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Transfer.Check
public import Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.Script.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.Utf8.Thms

/-!
# Round 7: derivations with `ExpFree` quantifiers move from `utf8Env B` to `simEnv B`

`dderivesB_simEnv_of_E`: a `DDerivesBE (utf8Env B) O` derivation of a relation `Step` reaches is
a `DDerivesB (simEnv B) O'` derivation, for any `O ≤ O'`, when `B` leaves `$utf8`
uninterpreted. At each rule instance:

* the relation has no parameters, so the scope binds term variables only (`DefsOk`, `TypsOk tyA`);
* its quantifiers are over `tyB` (`Round7.TypAgree.relQuantsOk_B`) and bound to `ExpFree`
  values (the side condition of `DDerivesBE`), so they are typed alike
  (`Round7.TypAgree.quantsOk_utf8Env_iff`);
* its conclusion alternatives and premises are harmless (`relRulesOk_fixed`), so they evaluate
  alike (`Round7.Script.evalExp_utf8Env_iff` and the argument and domain versions below), and
  every relation a premise names is reachable.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Transfer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (tyA tyB tyOk TypsOk quantsOk relQuantsOk
  relQuantsOk_B quantsOk_utf8Env_iff goodEvs_of_goodEvsB typsOk_empty typsOk_of_typs)
open Round6.Reading (DDerivesB DPremB conclAlts)

variable {B : Builtins}

/-! ## Arguments and domains evaluate alike -/

theorem evalArgs_utf8Env_iff (hB : ∀ ws, B.call "utf8" ws = none) {ρ : VarEnv} {ags : List Arg}
    {ws : List ArgV} (hD : DefsOk ρ) (hG : GoodEvs (evArgs ags)) :
    EvalArgs (utf8Env B) ρ ags ws ↔ EvalArgs (simEnv B) ρ ags ws := by
  have h : ∀ n, evalArgs n (utf8Env B) ρ ags = evalArgs n (simEnv B) ρ ags := fun n =>
    le_antisymm' ((agreeAt B n).args ρ ags hD hG) ((Round7.envMonoAt B hB n).args ρ ags)
  simp only [EvalArgs, h]

theorem evalDoms_utf8Env_iff (hB : ∀ ws, B.call "utf8" ws = none) {ρ : VarEnv} {ds : List Dom}
    {xvs : List (IL.Id × Value)} (hD : DefsOk ρ) (hG : GoodEvs (evDoms ds)) :
    EvalDoms (utf8Env B) ρ ds xvs ↔ EvalDoms (simEnv B) ρ ds xvs := by
  have h : ∀ n, evalDoms n (utf8Env B) ρ ds = evalDoms n (simEnv B) ρ ds := fun n =>
    le_antisymm' ((agreeAt B n).doms ρ ds hD hG) ((Round7.envMonoAt B hB n).doms ρ ds)
  simp only [EvalDoms, h]

/-! ## The script facts at a reachable relation -/

theorem mem_rels_of_findRel {x : IL.Id} {v : RelDef} (h : (simEnv B).findRel? x = some v) :
    (x, v) ∈ relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed := by
  unfold simEnv baseEnv at h
  rw [Env.findRel?_withBuiltins, envOfScript, envOfDefs_eq] at h
  have hm := mem_of_find? h
  rw [List.mem_append] at hm
  rcases hm with hm | hm
  · exact hm
  · simp [Env.empty, Map.empty] at hm

/-- What the kernel checks say about one rule of a reachable relation. -/
structure RuleFacts (ps : List Param) (qs : List Param) (e : Exp) (prems : List Prem) : Prop where
  params : ps = []
  concl : ∀ e' ∈ conclAlts e, GoodEvs (evExp e')
  prems : GoodEvs (evPrems prems)
  quants : ∀ y t, Param.expP y t ∈ qs → tyOk tyA tyB t = true

theorem ruleFacts {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {i : Nat} {nm : IL.Id} {qs : List Param} {e : Exp} {prems : List Prem}
    (hx : (0, x) ∈ stepReach) (hrel : (simEnv B).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e prems)) : RuleFacts ps qs e prems := by
  have hm := mem_rels_of_findRel hrel
  have hc : stepReach.contains (0, x) = true := by simpa using hx
  have h₁ := List.all_eq_true.1 relRulesOk_fixed _ hm
  have h₂ := List.all_eq_true.1 relQuantsOk_B _ hm
  simp only [hc, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.isEmpty_iff] at h₁ h₂
  have hr : Rule.ruleD nm qs op e prems ∈ rules := List.mem_of_getElem? hrule
  have h₃ := List.all_eq_true.1 h₁.2 _ hr
  have h₄ := List.all_eq_true.1 h₂ _ hr
  simp only [Bool.and_eq_true, List.all_eq_true] at h₃
  simp only [quantsOk, List.all_eq_true] at h₄
  refine ⟨h₁.1, fun e' he' => goodEvs_of_goodEvsB (h₃.1 e' he'),
    goodEvs_of_goodEvsB h₃.2, fun y t hy => ?_⟩
  simpa using h₄ _ hy

theorem bindParams_nil {ρ ρ' : VarEnv} {args : List ArgV} (h : bindParams ρ [] args = some ρ') :
    ρ' = ρ := by
  cases args with
  | nil => exact (Option.some.inj h).symm
  | cons _ _ => simp [bindParams] at h

theorem typsOk_bindVals {ρ : VarEnv} (h : TypsOk tyA ρ) (xs : List (IL.Id × Value)) :
    TypsOk tyA (ρ.bindVals xs) := typsOk_of_typs h rfl

theorem goodEvs_iterPr {pr : Prem} {it : IterExp} (h : GoodEvs (evPrem (.iterPr pr it))) :
    GoodEvs (evPrem pr) ∧ GoodEvs (evIterExp it) := by
  simpa [evPrem] using h

theorem goodEvs_iterDoms {it : Iter} {ds : List Dom} (h : GoodEvs (evIterExp (.mk it ds))) :
    GoodEvs (evIter it) ∧ GoodEvs (evDoms ds) := by
  simpa [evIterExp] using h

/-! ## The transfer -/


mutual
/-- **Derivations with `ExpFree` quantifiers move from `utf8Env B` to `simEnv B`**, along any
inclusion of the readings of `otherwise`, for a relation `Step` reaches. -/
theorem dderivesB_simEnv_of_E (hB : ∀ ws, B.call "utf8" ws = none) {O O' : ElseI}
    (hO : ∀ x args i v, O x args i v → O' x args i v) :
    ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}, (0, x) ∈ stepReach →
      DDerivesBE (utf8Env B) O x op args v → DDerivesB (simEnv B) O' x op args v
  | _, _, _, _, hx, .rule (σ := σ) (ρ₀ := ρ₀) hrel hrule halt hps hq hxf he hp => by
    rw [Round7.findRel?_utf8Env] at hrel
    obtain ⟨hps₀, hconcl, hprems, hquants⟩ := ruleFacts hx hrel hrule
    have hρ : ρ₀ = VarEnv.empty := bindParams_nil (hps₀ ▸ hps)
    have hD : DefsOk (ρ₀.bindVals σ) := hρ ▸ defsOk_bindVals defsOk_empty σ
    have hT : TypsOk tyA (ρ₀.bindVals σ) := hρ ▸ typsOk_bindVals (typsOk_empty tyA) σ
    refine .rule (σ := σ) hrel hrule halt hps ?_ ?_ ?_
    · exact (quantsOk_utf8Env_iff hB hD hT hquants hxf).1 hq
    · exact (evalExp_utf8Env_iff hB hD (hconcl _ halt)).1 he
    · intro pr hpr
      exact dpremB_simEnv_of_E hB hO (hO _ _ _ _) hD hT (goodEvs_prems hprems pr hpr)
        (hp pr hpr)
termination_by structural _ _ _ _ _ hd => hd

/-- `dderivesB_simEnv_of_E` for premises, in a scope that binds only reachable definitions and
types over `tyA`. -/
theorem dpremB_simEnv_of_E (hB : ∀ ws, B.call "utf8" ws = none) {O O' : ElseI}
    (hO : ∀ x args i v, O x args i v → O' x args i v) {els els' : Prop} (hels : els → els') :
    ∀ {ρ : VarEnv} {pr : Prem}, DefsOk ρ → TypsOk tyA ρ → GoodEvs (evPrem pr) →
      DPremBE (utf8Env B) O els ρ pr → DPremB (simEnv B) O' els' ρ pr
  | _, _, hD, _, hG, .ifPr h => .ifPr ((evalExp_utf8Env_iff hB hD hG).1 h)
  | _, _, _, _, _, .elsePr h => .elsePr (hels h)
  | _, _, hD, _, hG, .letPr h₂ h₁ => by
    simp only [evPrem, goodEvs_append] at hG
    exact .letPr ((evalExp_utf8Env_iff hB hD hG.2).1 h₂) ((evalExp_utf8Env_iff hB hD hG.1).1 h₁)
  | _, _, hD, _, hG, .rulePr ha he hd => by
    simp only [evPrem, goodEvs_cons, goodEvs_append, goodEv_ref0] at hG
    exact .rulePr ((evalArgs_utf8Env_iff hB hD hG.2.1).1 ha)
      ((evalExp_utf8Env_iff hB hD hG.2.2).1 he) (dderivesB_simEnv_of_E hB hO hG.1 hd)
  | _, _, hD, _, hG, .iterOptNone hd hne hall => by
    have hI := goodEvs_iterDoms (goodEvs_iterPr hG).2
    exact .iterOptNone ((evalDoms_utf8Env_iff hB hD hI.2).1 hd) hne hall
  | _, _, hD, hT, hG, .iterOptSome (row := row) hd hne hs hp => by
    have hG' := goodEvs_iterPr hG
    have hI := goodEvs_iterDoms hG'.2
    exact .iterOptSome ((evalDoms_utf8Env_iff hB hD hI.2).1 hd) hne hs
      (dpremB_simEnv_of_E hB hO hels (defsOk_bindVals hD row) (typsOk_bindVals hT row) hG'.1 hp)
  | _, _, hD, hT, hG, .iterList hit hd hne hl hk hp => by
    have hG' := goodEvs_iterPr hG
    have hI := goodEvs_iterDoms hG'.2
    exact .iterList hit ((evalDoms_utf8Env_iff hB hD hI.2).1 hd) hne hl hk fun r hr =>
      dpremB_simEnv_of_E hB hO hels (defsOk_bindVals hD r) (typsOk_bindVals hT r) hG'.1 (hp r hr)
  | _, _, hD, hT, hG, .iterListN hd he hk hl hlen hp => by
    have hG' := goodEvs_iterPr hG
    simp only [evIterExp, evIter, goodEvs_append] at hG'
    exact .iterListN ((evalDoms_utf8Env_iff hB hD hG'.2.2).1 hd)
      ((evalExp_utf8Env_iff hB hD hG'.2.1).1 he) hk hl hlen fun r hr =>
      dpremB_simEnv_of_E hB hO hels (defsOk_bindVals hD r) (typsOk_bindVals hT r) hG'.1 (hp r hr)
termination_by structural _ _ _ _ _ hd => hd
end

mutual
/-- Forgetting the side condition. -/
theorem dderivesB_of_E {env : Env} {O : ElseI} :
    ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value},
      DDerivesBE env O x op args v → DDerivesB env O x op args v
  | _, _, _, _, .rule hrel hrule halt hps hq _ he hp =>
    .rule hrel hrule halt hps hq he fun pr hpr => dpremB_of_E (hp pr hpr)

/-- `dderivesB_of_E` for premises. -/
theorem dpremB_of_E {env : Env} {O : ElseI} {els : Prop} :
    ∀ {ρ : VarEnv} {pr : Prem}, DPremBE env O els ρ pr → DPremB env O els ρ pr
  | _, _, .ifPr h => .ifPr h
  | _, _, .elsePr h => .elsePr h
  | _, _, .letPr h₂ h₁ => .letPr h₂ h₁
  | _, _, .rulePr ha he hd => .rulePr ha he (dderivesB_of_E hd)
  | _, _, .iterOptNone hd hne hall => .iterOptNone hd hne hall
  | _, _, .iterOptSome hd hne hs hp => .iterOptSome hd hne hs (dpremB_of_E hp)
  | _, _, .iterList hit hd hne hl hk hp =>
    .iterList hit hd hne hl hk fun r hr => dpremB_of_E (hp r hr)
  | _, _, .iterListN hd he hk hl hlen hp =>
    .iterListN hd he hk hl hlen fun r hr => dpremB_of_E (hp r hr)
end

/-- **SpecTec's `Step` moves from `utf8Env B` to `simEnv B`** at derivations with `ExpFree`
quantifiers, given that `otherwise` reads no more permissively in `utf8Env B` than in
`simEnv B`. -/
theorem sStepB_simEnv_of_E (hB : ∀ ws, B.call "utf8" ws = none)
    (hO : ∀ x args i v, Round6.Reading.otherwiseB (utf8Env B) x args i v →
      Round6.Reading.otherwiseB (simEnv B) x args i v) {c w : Value}
    (h : DDerivesBE (utf8Env B) (Round6.Reading.otherwiseB (utf8Env B)) "Step" "%~>%" []
      (.tuple [c, w])) :
    Round6.Reading.SStepB (simEnv B) c w :=
  dderivesB_simEnv_of_E hB hO step_mem_stepReach h

/-- The `noElse` reading moves with no hypothesis on `otherwise`. -/
theorem dderivesB_noElse_simEnv_of_E (hB : ∀ ws, B.call "utf8" ws = none) {x : IL.Id}
    {op : MixopS} {args : List ArgV} {v : Value} (hx : (0, x) ∈ stepReach)
    (h : DDerivesBE (utf8Env B) noElse x op args v) : DDerivesB (simEnv B) noElse x op args v :=
  dderivesB_simEnv_of_E hB (fun _ _ _ _ h => h) hx h

end Silmaril.Wasm.SpecTec.Sim.Round7.Transfer
