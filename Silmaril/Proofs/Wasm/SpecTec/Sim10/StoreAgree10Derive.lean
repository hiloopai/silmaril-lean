module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreAgree10Env
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdTable
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreFix10Closed

/-!
# Every step of `simEnv10 B` is a step of `simEnv10T B`, with no hypothesis

2.0's generic transfer (`Sim20.StoreAgree.dderives_of`) moves a declarative derivation from
`e₁` to `e₂` when the two environments evaluate alike and typing grows, given that every
`otherwise` premise used in `e₁` also holds in `e₂`. For 2.0 that condition is open
(`Sim20.StoreAgree.Task.elseAgree20T`, seventeen rules). For 1.0 it is proved here:

* `else10_only` (kernel): in the whole wasm-1.0 script, the only rule with an `otherwise`
  premise is rule 4 of `Step_read`, `call_indirect-trap`. So a `RuleCtx` of `simEnv10 B` is at
  `Step_read`, rule 4, with no arguments (`ruleCtx10_inv`).
* `otherwise10T_of_10` (**`elseAgree10T`**): there, `otherwise` in `simEnv10` gives `otherwise` in
  `simEnv10T`. Rules 0–2 (`block`, `loop`, `call`) have a one-instruction left-hand side and
  cannot match the two instructions of `call_indirect-trap`'s (`not_body_one`, by evaluation, in
  any environment). A firing of rule 3 (`call_indirect-call`) in `simEnv10T` is one in
  `simEnv10` (`body3_back`): its premises are evaluations, which agree; its quantifiers `z`, `i`,
  `x` are bound by the shared left-hand side to the values of `call_indirect-trap`'s own
  quantifiers, which `RuleCtx` types in `simEnv10` (`lhsCI_inv`); and `a : addr` is typed alike in
  both, `addr` being an alias of `nat` (`hasTyp_aliasNum_move`).
* **`sstepB10T_of_sstepB10`**: every `SStepB` step of `simEnv10 B` is one of `simEnv10T B`, at
  every builtins, with no hypothesis.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.StoreAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm.SpecTec.Sim (Interp ElseI QuantsOk DDerives RuleBody PremW otherwise otherwiseAt
  noElse SameLhs ValsOnly SStep)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (EnvSame TypRepair RuleCtx hasElseB dderives_of
  evalExp_eq)

/-! ## The one `otherwise` rule of wasm-1.0 -/

/-- A rule without an `otherwise` premise. -/
def elseFreeB : Rule → Bool
  | .ruleD _ _ _ _ prems => !(prems.any hasElseB)

/-- Only rule 4 of `Step_read` may have an `otherwise` premise. -/
def elseOnlyB (p : IL.Id × (List Param × MixopS × Typ × List Rule)) : Bool :=
  (List.range p.2.2.2.2.length).all fun i =>
    (p.1 == "Step_read" && i == 4) || (p.2.2.2.2[i]?.all elseFreeB)

set_option maxRecDepth 100000 in
/-- **In the wasm-1.0 script only `Step_read`'s rule 4 has an `otherwise` premise** (kernel). -/
theorem else10_only' : baseEnv10.rels.all elseOnlyB = true := by
  decide +kernel

set_option maxRecDepth 8000000 in
theorem else10_only (B : Builtins) : (simEnv10 B).rels.all elseOnlyB = true :=
  else10_only'

theorem mem_of_find? {α : Type} : ∀ {m : Map α} {x : IL.Id} {v : α}, Map.find? m x = some v →
    (x, v) ∈ m
  | [], _, _, h => by simp [Map.find?] at h
  | (y, w) :: m, x, v, h => by
    simp only [Map.find?] at h
    split at h
    · rename_i hy
      subst hy
      cases h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_find? h)

/-- A rule instance without parameters takes no arguments, in the empty scope. -/
theorem bindParams_nil_inv {args : List ArgV} {ρ₀ : VarEnv}
    (h : bindParams VarEnv.empty [] args = some ρ₀) : args = [] ∧ ρ₀ = VarEnv.empty := by
  cases args with
  | nil => exact ⟨rfl, (Option.some.inj h).symm⟩
  | cons a l => cases a <;> simp [bindParams] at h

/-- A `RuleCtx` of `simEnv10 B` is at `Step_read`'s rule 4, with no arguments. -/
theorem ruleCtx10_inv {B : Builtins} {x : IL.Id} {args : List ArgV} {i : Nat} {v : Value}
    (h : RuleCtx (simEnv10 B) x args i v) : x = "Step_read" ∧ i = 4 ∧ args = [] := by
  obtain ⟨ps, op, t, rules, nm, qs, e, prems, ρ₀, σ, hrel, hr, ⟨pr, hpr, hel⟩, hps, -, -⟩ := h
  have hmem := mem_of_find? (show Map.find? (simEnv10 B).rels x = _ from hrel)
  have hall := List.all_eq_true.1 (else10_only B) _ hmem
  have hi : i < rules.length := (List.getElem?_eq_some_iff.1 hr).1
  have hk := List.all_eq_true.1 hall i (List.mem_range.2 hi)
  simp only [hr, Option.all_some, elseFreeB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    Bool.not_eq_true', List.any_eq_false] at hk
  rcases hk with ⟨rfl, rfl⟩ | hk
  · refine ⟨rfl, rfl, ?_⟩
    obtain ⟨ps', t', rules', hrel', rfl, -⟩ := Whole.hasRuleAt10_callIndirectTrap B
    rw [hrel'] at hrel
    obtain rfl : ps = [] := by simp at hrel; exact hrel.1
    exact (bindParams_nil_inv hps).1
  · exact absurd hel (by simp [hk pr hpr])

/-! ## Typing `addr` alike -/

/-- An alias of a number type is typed alike in two environments that both declare it, in any
two scopes binding term variables only. -/
theorem hasTyp_aliasNum_move {e₁ e₂ : Env} {x : IL.Id} {t : NumTyp} {ρ ρ' : VarEnv}
    (h₁ : e₁.findTyp? x = some ([], [.instD [] [] (.aliasT (.numT t))]))
    (h₂ : e₂.findTyp? x = some ([], [.instD [] [] (.aliasT (.numT t))]))
    (hρ : ValsOnly ρ) (hρ' : ValsOnly ρ') {v : Value} (h : HasTyp e₂ ρ (.varT x []) v) :
    HasTyp e₁ ρ' (.varT x []) v := by
  have hl : localTyp? ρ x [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd, hargs, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  obtain rfl := Equiv.Validation.evalArgs_nil_iff.1 hargs
  rw [h₂] at htd
  obtain rfl := (Option.some.inj htd).symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, -, hd⟩ | hi'
  · obtain ⟨m, rfl, hm⟩ := hasTyp_numT_iff.1 (hasTypDef_aliasT_iff.1 hd)
    exact Sim20.Whole.typedV_aliasG h₁ (hasTyp_numT_iff.2 ⟨m, rfl, hm⟩) ρ' hρ'
  · exact absurd hi' not_hasTypInsts_nil

/-! ## Evaluation, backwards -/

variable {e₁ e₂ : Env}

theorem evalExp_back (hS : EnvSame e₁ e₂) {ρ : VarEnv} {e : Exp} {v : Value}
    (h : EvalExp e₂ ρ e v) : EvalExp e₁ ρ e v :=
  let ⟨n, hn⟩ := h
  ⟨n, (evalExp_eq hS n ρ e).symm.trans hn⟩

/-! ## The left-hand sides -/

/-- A conclusion `z; [e] ~> rh` evaluates to a configuration with one instruction. -/
theorem lhs_one {env : Env} {ρ : VarEnv} {e rh : Exp} {a d : Value}
    (h : EvalExp env ρ (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [e]]), rh]) (.tuple [a, d])) :
    ∃ z u, a = .case "%;%" (.tuple [z, .list [u]]) := by
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 (Sim.RefsGC.lhs_of_concl h)
  obtain ⟨w₁, w₂, -, hw₂, rfl⟩ := Sim.State.evalExp_tup2_inv hu
  obtain ⟨vs, hvs, rfl⟩ := evalExp_listE_iff.1 hw₂
  obtain ⟨u, us, -, hus, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain rfl := evalExps_nil_iff.1 hus
  exact ⟨w₁, u, rfl⟩

/-- `call_indirect`'s left-hand side `z; CONST I32 i, CALL_INDIRECT x`, read back: the values of
`z`, `i` and `x`. -/
theorem lhsCI_inv {env : Env} {ρ : VarEnv} {a : Value}
    (h : EvalExp env ρ (.caseE "%;%" (.tupE [.varE "z", .listE [Sim20.Whole.constIE,
      .caseE "CALL_INDIRECT" (.varE "x")]])) a) :
    ∃ z i x, ρ.findVal? "z" = some z ∧ ρ.findVal? "i" = some i ∧ ρ.findVal? "x" = some x ∧
      a = .case "%;%" (.tuple [z, .list [.case "CONST" (.tuple [.case "I32" (.tuple []), i]),
        .case "CALL_INDIRECT" x]]) := by
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨w₁, w₂, hw₁, hw₂, rfl⟩ := Sim.State.evalExp_tup2_inv hu
  obtain ⟨vs, hvs, rfl⟩ := evalExp_listE_iff.1 hw₂
  obtain ⟨c₁, us, hc₁, hus, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨c₂, us', hc₂, hus', rfl⟩ := evalExps_cons_iff.1 hus
  obtain rfl := evalExps_nil_iff.1 hus'
  obtain ⟨p, hp, rfl⟩ := evalExp_caseE_iff.1 hc₁
  obtain ⟨p₁, p₂, hp₁, hp₂, rfl⟩ := Sim.State.evalExp_tup2_inv hp
  obtain ⟨q, hq, rfl⟩ := evalExp_caseE_iff.1 hp₁
  obtain ⟨qs, hqs, rfl⟩ := evalExp_tupE_iff.1 hq
  obtain rfl := evalExps_nil_iff.1 hqs
  obtain ⟨r, hr, rfl⟩ := evalExp_caseE_iff.1 hc₂
  exact ⟨w₁, p₂, r, evalExp_varE_iff.1 hw₁, evalExp_varE_iff.1 hp₂, evalExp_varE_iff.1 hr, rfl⟩

/-- A rule with a one-instruction left-hand side does not fire on `call_indirect`'s. -/
theorem not_body_one {env : Env} {D : Interp} {els : Prop} {nm : IL.Id} {qs : List Param}
    {e rh : Exp} {prems : List Prem} {args : List ArgV} {z i x d : Value}
    (hb : RuleBody env D els [] args "%~>%"
      (.ruleD nm qs "%~>%" (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [e]]), rh]) prems)
      (.tuple [.case "%;%" (.tuple [z, .list [.case "CONST" (.tuple [.case "I32" (.tuple []), i]),
        .case "CALL_INDIRECT" x]]), d])) : False := by
  obtain ⟨-, ρ₀, σ, -, -, he, -⟩ := hb
  obtain ⟨z', u, hz⟩ := lhs_one he
  simp at hz

/-! ## `call_indirect-call`, backwards across the erratum -/

/-- A quantifier pinned by a value in a well-typed scope is typed there. -/
theorem typ_of_pinned {env : Env} {ρ : VarEnv} {qs : List Param} {y : IL.Id} {t : Typ} {w : Value}
    (hq : QuantsOk env ρ qs) (hm : Param.expP y t ∈ qs) (hy : ρ.findVal? y = some w) :
    HasTyp env ρ t w := by
  obtain ⟨w', hw', ht⟩ := hq y t hm
  have e : w' = w := Option.some.inj (hw'.symm.trans hy)
  exact e ▸ ht

/-- `addr` is declared alike in both environments. -/
theorem findTyp_addr10T (B : Builtins) : (simEnv10T B).findTyp? "addr" =
    some ([], [.instD [] [] (.aliasT (.numT .natT))]) := by
  have hne : ¬ ∃ cs, (simEnv10 B).findTyp? "addr" = some ([], [.instD [] [] (.variantT cs)]) ∧
      (simEnv10T B).findTyp? "addr" = some ([], [.instD [] [] (.variantT (cs.map fixCase10))]) ∧
      (cs = instrCases10 ∨ cs = adminCases10) := by
    rintro ⟨cs, h, -, -⟩
    rw [Whole.findTyp_addr10] at h
    simp at h
  exact (Or.resolve_right (findTyp?_simEnv10T B "addr") hne).trans Whole.findTyp_addr10

/-- The quantifiers of `call_indirect-call`, typed in `simEnv10T` at values the quantifiers of a
typed `call_indirect-trap` instance of `simEnv10` pin, are typed in `simEnv10`. -/
theorem quants3_back {B : Builtins} {ρ₄ ρ : VarEnv} (hρ₄ : ValsOnly ρ₄) (hρ : ValsOnly ρ)
    (hq₄ : QuantsOk (simEnv10 B) ρ₄ [.expP "z" (.varT "state" []), .expP "i" Whole.valI32T',
      .expP "x" (.varT "idx" [])])
    (hq : QuantsOk (simEnv10T B) ρ (match Whole.callIndirectRule10 with | .ruleD _ qs _ _ _ => qs))
    {z i x : Value} (hz : ρ₄.findVal? "z" = some z) (hi : ρ₄.findVal? "i" = some i)
    (hx : ρ₄.findVal? "x" = some x) (hz' : ρ.findVal? "z" = some z)
    (hi' : ρ.findVal? "i" = some i) (hx' : ρ.findVal? "x" = some x) :
    QuantsOk (simEnv10 B) ρ (match Whole.callIndirectRule10 with | .ruleD _ qs _ _ _ => qs) := by
  intro y t hy
  simp only [Whole.callIndirectRule10, List.mem_cons, Param.expP.injEq, List.mem_nil_iff,
    or_false] at hy
  rcases hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨_, hz', Sim.IntNumeric.hasTyp_varT_nil_congr hρ₄ hρ (typ_of_pinned hq₄ (by simp) hz)⟩
  · exact ⟨_, hi', Whole.hasTyp_valI32_congr10 (typ_of_pinned hq₄ (by simp) hi)⟩
  · exact ⟨_, hx', Sim.IntNumeric.hasTyp_varT_nil_congr hρ₄ hρ (typ_of_pinned hq₄ (by simp) hx)⟩
  · obtain ⟨w, hw, ht⟩ := hq "a" (.varT "addr" []) (by simp [Whole.callIndirectRule10])
    exact ⟨w, hw, hasTyp_aliasNum_move Whole.findTyp_addr10 (findTyp_addr10T B) hρ hρ ht⟩

/-- A firing of `call_indirect-call` in `simEnv10T` whose left-hand side is that of a typed
`call_indirect-trap` instance of `simEnv10` is a firing in `simEnv10`. -/
theorem body3_back {B : Builtins} {D₁ D₂ : Interp} {els₁ els₂ : Prop} {args : List ArgV}
    {ρ₄ : VarEnv} (hρ₄ : ValsOnly ρ₄)
    (hq₄ : QuantsOk (simEnv10 B) ρ₄ [.expP "z" (.varT "state" []), .expP "i" Whole.valI32T',
      .expP "x" (.varT "idx" [])])
    {z i x d : Value} (hz : ρ₄.findVal? "z" = some z) (hi : ρ₄.findVal? "i" = some i)
    (hx : ρ₄.findVal? "x" = some x)
    (hb : RuleBody (simEnv10T B) D₂ els₂ [] args "%~>%" Whole.callIndirectRule10
      (.tuple [.case "%;%" (.tuple [z, .list [.case "CONST" (.tuple [.case "I32" (.tuple []), i]),
        .case "CALL_INDIRECT" x]]), d])) :
    RuleBody (simEnv10 B) D₁ els₁ [] args "%~>%" Whole.callIndirectRule10
      (.tuple [.case "%;%" (.tuple [z, .list [.case "CONST" (.tuple [.case "I32" (.tuple []), i]),
        .case "CALL_INDIRECT" x]]), d]) := by
  have hS := envSame10T B
  obtain ⟨-, ρ₀, σ, hps, hq, he, hp⟩ := hb
  obtain ⟨-, rfl⟩ := bindParams_nil_inv hps
  have he₁ := evalExp_back hS he
  obtain ⟨z', i', x', hz', hi', hx', heq⟩ := lhsCI_inv (Sim.RefsGC.lhs_of_concl he₁)
  have hzix : z = z' ∧ i = i' ∧ x = x' := by simpa using heq
  obtain ⟨rfl, rfl, rfl⟩ := hzix
  refine ⟨rfl, _, σ, hps, quants3_back hρ₄ (Sim20.Pure.valsOnly_bindVals σ) hq₄ hq hz hi hx
    hz' hi' hx', he₁, fun pr hpr => ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
  rcases hpr with rfl | rfl
  · exact .ifPr (evalExp_back hS (Sim20.Pure.ifPrem (hp _ (.head _))))
  · exact .ifPr (evalExp_back hS (Sim20.Pure.ifPrem (hp _ (.tail _ (.head _)))))

/-! ## `otherwise` moves, and so does every step -/

/-- Rule `k` of `Step_read`, read off a lookup. -/
theorem ruleAt_read {B : Builtins} {k : Nat} {r r' : Rule} {ps : List Param} {op : MixopS}
    {t : Typ} {rules : List Rule} (hR : HasRuleAt (simEnv10 B) "Step_read" "%~>%" k r)
    (hrel : (simEnv10 B).findRel? "Step_read" = some (ps, op, t, rules)) (hk : rules[k]? = some r') :
    r' = r := by
  obtain ⟨ps', t', rules', hrel', -, hk'⟩ := hR
  rw [hrel'] at hrel
  simp only [Option.some.injEq, Prod.mk.injEq] at hrel
  obtain ⟨-, -, -, rfl⟩ := hrel
  exact Option.some.inj (hk.symm.trans hk')

/-- A `RuleCtx` of `simEnv10 B`, unfolded: `call_indirect-trap`'s typed quantifiers and its
conclusion. -/
theorem ruleCtx10_data {B : Builtins} {x : IL.Id} {args : List ArgV} {i : Nat} {v : Value}
    (hc : RuleCtx (simEnv10 B) x args i v) :
    x = "Step_read" ∧ i = 4 ∧ args = [] ∧ ∃ σ,
      QuantsOk (simEnv10 B) (VarEnv.empty.bindVals σ) [.expP "z" (.varT "state" []),
        .expP "i" Whole.valI32T', .expP "x" (.varT "idx" [])] ∧
      EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ)
        (match Whole.callIndirectTrapRule10 with | .ruleD _ _ _ e _ => e) v := by
  obtain ⟨rfl, rfl, rfl⟩ := ruleCtx10_inv hc
  obtain ⟨ps, op, t, rules, nm, qs, e, prems, ρ₀, σ, hrel, hr, -, hps, hq, he⟩ := hc
  have h4 := ruleAt_read (Whole.hasRuleAt10_callIndirectTrap B) hrel hr
  simp only [Whole.callIndirectTrapRule10, Rule.ruleD.injEq] at h4
  obtain ⟨-, rfl, -, rfl, -⟩ := h4
  have hρ : ρ₀ = VarEnv.empty := by
    obtain ⟨psR, tR, rulesR, hrelR, hpsR, -⟩ := Whole.hasRuleAt10_block B
    have hps' : ps = [] := by
      rw [hrelR] at hrel
      simp only [Option.some.injEq, Prod.mk.injEq] at hrel
      exact hrel.1 ▸ hpsR
    exact (bindParams_nil_inv (hps' ▸ hps)).2
  exact ⟨rfl, rfl, rfl, σ, hρ ▸ hq, hρ ▸ he⟩

/-- No rule `j < 4` of `Step_read` fires in `simEnv10T` on `call_indirect`'s left-hand side
where `call_indirect-trap`'s `otherwise` holds in `simEnv10` at a typed instance. -/
theorem not_earlier10T {B : Builtins} {σ : List (IL.Id × Value)}
    (hq : QuantsOk (simEnv10 B) (VarEnv.empty.bindVals σ) [.expP "z" (.varT "state" []),
      .expP "i" Whole.valI32T', .expP "x" (.varT "idx" [])])
    {z i x b d : Value} (hz : (VarEnv.empty.bindVals σ).findVal? "z" = some z)
    (hi : (VarEnv.empty.bindVals σ).findVal? "i" = some i)
    (hx : (VarEnv.empty.bindVals σ).findVal? "x" = some x)
    (ho : otherwise (simEnv10 B) "Step_read" [] 4 (.tuple [.case "%;%" (.tuple [z,
      .list [.case "CONST" (.tuple [.case "I32" (.tuple []), i]), .case "CALL_INDIRECT" x]]), b]))
    {j : Nat} (hj : j < 4) {t : Typ} {rules : List Rule} {r : Rule}
    (hrel : (simEnv10 B).findRel? "Step_read" = some ([], "%~>%", t, rules)) (hr : rules[j]? = some r)
    {D : Interp} {els : Prop}
    (hb : RuleBody (simEnv10T B) D els [] [] "%~>%" r (.tuple [.case "%;%" (.tuple [z,
      .list [.case "CONST" (.tuple [.case "I32" (.tuple []), i]), .case "CALL_INDIRECT" x]]), d])) :
    False := by
  match j, hj with
  | 0, _ => exact not_body_one ((ruleAt_read (Whole.hasRuleAt10_block B) hrel hr) ▸ hb)
  | 1, _ => exact not_body_one ((ruleAt_read (Whole.hasRuleAt10_loop B) hrel hr) ▸ hb)
  | 2, _ => exact not_body_one ((ruleAt_read (Whole.hasRuleAt10_call B) hrel hr) ▸ hb)
  | 3, _ =>
    have e3 := ruleAt_read (Whole.hasRuleAt10_callIndirect B) hrel hr
    subst e3
    rw [otherwise, otherwiseAt] at ho
    exact ho 3 (by omega) [] "%~>%" t rules _ hrel hr _ ⟨_, b, d, rfl, rfl⟩
      (body3_back (Sim20.Pure.valsOnly_bindVals σ) hq hz hi hx hb)
  | k + 4, hk => omega

/-- **`otherwise` in `simEnv10` gives `otherwise` in `simEnv10T`**, wherever the rest of the rule
holds in `simEnv10`. The 1.0 counterpart of `Sim20.StoreAgree.ElseAgree20T`, proved. -/
theorem elseAgree10T (B : Builtins) : ∀ x args i v, otherwise (simEnv10 B) x args i v →
    RuleCtx (simEnv10 B) x args i v → otherwise (simEnv10T B) x args i v := by
  intro x args i v ho hc
  obtain ⟨rfl, rfl, rfl, σ, hq, he⟩ := ruleCtx10_data hc
  obtain ⟨psR, tR, rulesR, hrelR, rfl, -⟩ := Whole.hasRuleAt10_block B
  show otherwiseAt (simEnv10T B) "Step_read" [] 4 v
  rw [otherwiseAt]
  intro j hj ps₂ op₂ t₂ rules₂ r hrel₂ hr₂ w hw hb
  obtain ⟨a, b, d, rfl, rfl⟩ := hw
  obtain ⟨z, i, x, hz, hi, hx, rfl⟩ := lhsCI_inv (Sim.RefsGC.lhs_of_concl he)
  have hrr : ps₂ = [] ∧ op₂ = "%~>%" ∧ rules₂ = rulesR := by
    rw [findRel?_simEnv10T, hrelR] at hrel₂
    simp only [Option.some.injEq, Prod.mk.injEq] at hrel₂
    exact ⟨hrel₂.1.symm, hrel₂.2.1.symm, hrel₂.2.2.2.symm⟩
  obtain ⟨rfl, rfl, rfl⟩ := hrr
  exact not_earlier10T hq hz hi hx ho hj hrelR hr₂ hb

/-- **Every step of `simEnv10 B` is a step of `simEnv10T B`**, at every builtins, with no
hypothesis. -/
theorem sstepB10T_of_sstepB10 {B : Builtins} {c c' : Value} (h : SStepB (simEnv10 B) c c') :
    SStepB (simEnv10T B) c c' :=
  (sstepB10T_iff B).2 (dderives_of (envSame10T B) (typRepair10T B) (elseAgree10T B)
    ((Whole.sstepB10_iff B).1 h))

/-- The same along runs. -/
theorem rtc_sstepB10T_of_sstepB10 {B : Builtins} {c c' : Value}
    (h : Relation.ReflTransGen (SStepB (simEnv10 B)) c c') :
    Relation.ReflTransGen (SStepB (simEnv10T B)) c c' :=
  by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (sstepB10T_of_sstepB10 hs)

end Silmaril.Wasm.SpecTec.Sim10.StoreAgree
