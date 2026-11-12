module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureRules
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Exn.IterN
public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Parametric

/-!
# Reading one `Step_pure` rule, both ways

`fires_of_ruleAt` builds `Fires` from an assignment; `fires_inv` reads an assignment back. With
`EvalExp.unique`, a rule's conclusion evaluated at the encoded left-hand side pins every
variable the left-hand side mentions, which is how each per-rule `iff` is proved.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Pure

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV evalExp_imm_iff iterPat evalExp_iterPat)
open Silmaril.Wasm.SpecTec.Sim (Fires RuleBody PremW QuantsOk TypedV ValsOnly otherwise DDerives
  evalExp_tup2 evalExp_tup3 evalExp_list1 evalExp_case evalExp_var evalExp_cat)

/-- Build `Fires` for rule `k` of `x` from an assignment. -/
theorem fires_of_ruleAt {env : Env} {x : IL.Id} {k : Nat} {nm : IL.Id} {qs : List Param}
    {e : Exp} {prems : List Prem} (h : HasRuleAt env x "%~>%" k (.ruleD nm qs "%~>%" e prems))
    (σ : List (IL.Id × Value)) {v : Value} (hq : QuantsOk env (VarEnv.empty.bindVals σ) qs)
    (he : EvalExp env (VarEnv.empty.bindVals σ) e v)
    (hp : ∀ pr ∈ prems, PremW env (DDerives env (otherwise env)) (otherwise env x [] k v)
      (VarEnv.empty.bindVals σ) pr) :
    Fires env x k v := by
  obtain ⟨ps, t, rules, hrel, rfl, hk⟩ := h
  exact ⟨t, rules, _, hrel, hk, rfl, VarEnv.empty, σ, rfl, hq, he, hp⟩

/-- Read the assignment of a firing rule back. -/
theorem fires_inv {env : Env} {x : IL.Id} {k : Nat} {nm : IL.Id} {qs : List Param}
    {e : Exp} {prems : List Prem} (h : HasRuleAt env x "%~>%" k (.ruleD nm qs "%~>%" e prems))
    {v : Value} (hf : Fires env x k v) :
    ∃ σ, QuantsOk env (VarEnv.empty.bindVals σ) qs ∧
      EvalExp env (VarEnv.empty.bindVals σ) e v ∧
      ∀ pr ∈ prems, PremW env (DDerives env (otherwise env)) (otherwise env x [] k v)
        (VarEnv.empty.bindVals σ) pr := by
  obtain ⟨ps, t, rules, hrel, rfl, hk⟩ := h
  obtain ⟨t', rules', r, hrel', hr, hb⟩ := hf
  rw [hrel] at hrel'
  obtain ⟨-, -, rfl⟩ : t = t' ∧ True ∧ rules = rules' := by
    simp only [Option.some.injEq, Prod.mk.injEq] at hrel'
    exact ⟨hrel'.2.2.1, trivial, hrel'.2.2.2⟩
  rw [hk] at hr
  cases hr
  obtain ⟨-, ρ₀, σ, hps, hq, he, hp⟩ := hb
  cases hps
  exact ⟨σ, hq, he, hp⟩

/-- No premises. -/
theorem prems_nil {env : Env} {D : Silmaril.Wasm.SpecTec.Sim.Interp} {els : Prop} {ρ : VarEnv} :
    ∀ pr ∈ ([] : List Prem), PremW env D els ρ pr := fun _ h => nomatch h

/-- One premise. -/
theorem prems_one {env : Env} {D : Silmaril.Wasm.SpecTec.Sim.Interp} {els : Prop} {ρ : VarEnv}
    {pr : Prem} (h : PremW env D els ρ pr) : ∀ p ∈ [pr], PremW env D els ρ p := by
  intro p hp
  rw [List.mem_singleton.1 hp]
  exact h

/-- The single `if` premise. -/
theorem ifPrem {env : Env} {D : Silmaril.Wasm.SpecTec.Sim.Interp} {els : Prop} {ρ : VarEnv}
    {e : Exp} (h : PremW env D els ρ (.ifPr e)) : EvalExp env ρ e (.bool true) := by
  cases h with
  | ifPr h => exact h

/-- A quantified variable is bound. -/
theorem quant_val {env : Env} {ρ : VarEnv} {qs : List Param} {x : IL.Id} {t : Typ}
    (hq : QuantsOk env ρ qs) (hm : Param.expP x t ∈ qs) : ∃ v, ρ.findVal? x = some v :=
  let ⟨v, hv, _⟩ := hq x t hm
  ⟨v, hv⟩

/-- A value of a `*` type is a list. -/
theorem hasTyp_list_isList {env : Env} {ρ : VarEnv} {t : Typ} {v : Value}
    (h : HasTyp env ρ (.iterT t .list) v) : ∃ l, v = .list l := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [hasTyp] at hn
  | succ n => cases v <;> simp_all [hasTyp, Value.asList?]

/-- A quantified `*` variable is bound to a list. -/
theorem quant_list {env : Env} {ρ : VarEnv} {qs : List Param} {x : IL.Id} {t : Typ}
    (hq : QuantsOk env ρ qs) (hm : Param.expP x (.iterT t .list) ∈ qs) :
    ∃ l, ρ.findVal? x = some (.list l) := by
  obtain ⟨v, hv, ht⟩ := hq x _ hm
  obtain ⟨l, rfl⟩ := hasTyp_list_isList ht
  exact ⟨l, hv⟩

/-- `x!%.0 op 0` read back, for `op` one of `=/=` and `=`. -/
theorem immCmp_of_eval {env : Env} {ρ : VarEnv} {x : IL.Id} {k : Nat} {op : CmpOp}
    (hx : ρ.findVal? x = some (pctV k))
    (h : EvalExp env ρ (.cmpE op .boolT (.projE (.uncaseE (.varE x) "%") 0) (.numE (.natN 0)))
      (.bool true)) : cmpValues op (.num (.natN k)) (.num (.natN 0)) = .ok (.bool true) := by
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_cmpE_iff.1 h
  have e₁ : v₁ = .num (.natN k) := EvalExp.unique h₁ ((evalExp_imm_iff hx).2 ⟨[], rfl⟩)
  have e₂ : v₂ = .num (.natN 0) := evalExp_numE_iff.1 h₂
  subst e₁ e₂
  exact hc

/-- `x!%.0 op 0`, evaluated. -/
theorem evalExp_immCmp {env : Env} {ρ : VarEnv} {x : IL.Id} {k : Nat} {op : CmpOp} {r : Value}
    (hx : ρ.findVal? x = some (pctV k))
    (hc : cmpValues op (.num (.natN k)) (.num (.natN 0)) = .ok r) :
    EvalExp env ρ (.cmpE op .boolT (.projE (.uncaseE (.varE x) "%") 0) (.numE (.natN 0))) r :=
  evalExp_cmpE_iff.2 ⟨_, _, (evalExp_imm_iff hx).2 ⟨[], rfl⟩, evalExp_numE_iff.2 rfl, hc⟩

/-- A nullary case. -/
theorem evalExp_caseNil {env : Env} {ρ : VarEnv} {op : MixopS} :
    EvalExp env ρ (.caseE op (.tupE [])) (caseNilV op) :=
  evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)

/-- A two-element list literal. -/
theorem evalExp_list2 {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v₁ v₂ : Value}
    (h₁ : EvalExp env ρ e₁ v₁) (h₂ : EvalExp env ρ e₂ v₂) :
    EvalExp env ρ (.listE [e₁, e₂]) (.list [v₁, v₂]) :=
  evalExp_listE_iff.2 ⟨_, evalExps_cons h₁ (evalExps_cons h₂ evalExps_nil), rfl⟩

/-- A three-element list literal. -/
theorem evalExp_list3 {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ : Exp} {v₁ v₂ v₃ : Value}
    (h₁ : EvalExp env ρ e₁ v₁) (h₂ : EvalExp env ρ e₂ v₂) (h₃ : EvalExp env ρ e₃ v₃) :
    EvalExp env ρ (.listE [e₁, e₂, e₃]) (.list [v₁, v₂, v₃]) :=
  evalExp_listE_iff.2 ⟨_, evalExps_cons h₁ (evalExps_cons h₂ (evalExps_cons h₃ evalExps_nil)), rfl⟩

/-- A four-element list literal. -/
theorem evalExp_list4 {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ e₄ : Exp} {v₁ v₂ v₃ v₄ : Value}
    (h₁ : EvalExp env ρ e₁ v₁) (h₂ : EvalExp env ρ e₂ v₂) (h₃ : EvalExp env ρ e₃ v₃)
    (h₄ : EvalExp env ρ e₄ v₄) :
    EvalExp env ρ (.listE [e₁, e₂, e₃, e₄]) (.list [v₁, v₂, v₃, v₄]) :=
  evalExp_listE_iff.2 ⟨_, evalExps_cons h₁ (evalExps_cons h₂ (evalExps_cons h₃
    (evalExps_cons h₄ evalExps_nil))), rfl⟩

/-- The empty list literal. -/
theorem evalExp_list0 {env : Env} {ρ : VarEnv} : EvalExp env ρ (.listE []) (.list []) :=
  evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩

/-- A subsort coercion is transparent. -/
theorem evalExp_sub {env : Env} {ρ : VarEnv} {e : Exp} {t₁ t₂ : Typ} {v : Value}
    (h : EvalExp env ρ e v) : EvalExp env ρ (.subE e t₁ t₂) v :=
  evalExp_subE_iff.2 h

/-- A plain `*` iteration over a bound list. -/
theorem evalExp_iter {env : Env} {ρ : VarEnv} {x y : IL.Id} (hx : x ≠ "_") {vs : List Value}
    (h : ρ.findVal? y = some (.list vs)) :
    EvalExp env ρ (.iterE (.varE x) (.mk .list [.mk x (.varE y)])) (.list vs) :=
  evalExp_iterPat hx h

/-- The two sides of a pair. -/
theorem evalExp_tup2_inv {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v₁ v₂ : Value}
    (h : EvalExp env ρ (.tupE [e₁, e₂]) (.tuple [v₁, v₂])) :
    EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ := by
  obtain ⟨vs, hvs, he⟩ := evalExp_tupE_iff.1 h
  obtain ⟨w₁, ws, rfl, h₁, hws⟩ := Equiv.Validation.evalExps_cons_iff.1 hvs
  obtain ⟨w₂, ws', rfl, h₂, hws'⟩ := Equiv.Validation.evalExps_cons_iff.1 hws
  have e₀ := Equiv.Validation.evalExps_nil_iff.1 hws'
  subst e₀
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨h₁, h₂⟩

/-- One round per element, each evaluating the round's own variable under `val <: admininstr`. -/
theorem mapM_rounds_val {env : Env} {ρ : VarEnv} {x : IL.Id} (hx : x ≠ "_") :
    ∀ ws : List Value, (ws.map fun w => [(x, w)]).mapM
      (fun r => evalExp 2 env (ρ.bindVals r) (.subE (.varE x) (.varT "val" [])
        (.varT "admininstr" []))) = .ok ws
  | [] => rfl
  | w :: ws => by
      have hw : evalExp 2 env (ρ.bindVals [(x, w)])
          (.subE (.varE x) (.varT "val" []) (.varT "admininstr" [])) = .ok w := by
        simp [evalExp, VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind, hx, Res.ofOption]
      have ih := mapM_rounds_val (env := env) (ρ := ρ) hx ws
      simp only [List.map_cons, List.mapM_cons, hw, ih]
      rfl

/-- The wasm-2.0 `val*`, `iterE (val <: admininstr)` over one domain. -/
theorem evalExp_vals {env : Env} {ρ : VarEnv} {x y : IL.Id} (hx : x ≠ "_") {vs : List Value}
    (h : ρ.findVal? y = some (.list vs)) :
    EvalExp env ρ (.iterE (.subE (.varE x) (.varT "val" []) (.varT "admininstr" []))
      (.mk .list [.mk x (.varE y)])) (.list vs) :=
  Equiv.Execution.evalExp_iterBody_var (d := 1)
    (fun σ w hw => by simp [evalExp, hw, Res.ofOption]) hx h

/-- The wasm-2.0 `val^n`, with the counter bound to the domain's length. -/
theorem evalExp_valsN {env : Env} {ρ : VarEnv} {x d c : IL.Id} {ws : List Value}
    (hx : x ≠ "_") (hc : ρ.findVal? c = some (.num (.natN ws.length)))
    (hd : ρ.findVal? d = some (.list ws)) :
    EvalExp env ρ (.iterE (.subE (.varE x) (.varT "val" []) (.varT "admininstr" []))
      (.mk (.listN (.varE c) none) [.mk x (.varE d)])) (.list ws) := by
  refine evalExp_iterE_iff.mpr ⟨5, ?_⟩
  have hdoms : evalDoms 4 env ρ [.mk x (.varE d)] = .ok [(x, Value.list ws)] := by
    simp [evalDoms, domVar, domSrc, evalExp, hd]
  have hcount : evalExp 4 env ρ (.varE c) = .ok (.num (.natN ws.length)) := by
    simp [evalExp, hc]
  have hlist : evalIterList 4 env ρ (.subE (.varE x) (.varT "val" []) (.varT "admininstr" []))
      [(x, Value.list ws)] none ws.length = .ok (.list ws) := by
    rw [evalIterList]
    simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok]
    refine ⟨[(x, ws)], by simp [Value.asList?], by simp, ws, ?_, rfl⟩
    rw [Equiv.Execution.iterRows_singleton, evalRounds]
    exact mapM_rounds_val hx ws
  rw [evalIterE, hdoms]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, hcount]
  exact ⟨_, rfl, _, rfl, ws.length, rfl, hlist⟩

/-- The wasm-2.0 `val^n`, inverted. -/
theorem evalExp_valsN_inv {env : Env} {ρ : VarEnv} {x y m : IL.Id} {v : Value} (hx : x ≠ "_")
    (h : EvalExp env ρ (.iterE (.subE (.varE x) (.varT "val" []) (.varT "admininstr" []))
      (.mk (.listN (.varE m) none) [.mk x (.varE y)])) v) :
    ∃ vs, ρ.findVal? y = some (.list vs) ∧ ρ.findVal? m = some (.num (.natN vs.length)) ∧
      v = .list vs :=
  Silmaril.Wasm.SpecTec.Sim.Exn.evalExp_iterN_inv (fun _ w u hw hu => by
    rw [evalExp_subE_iff, evalExp_varE_iff, hw] at hu
    exact (Option.some.inj hu).symm) hx h

/-! ## `FiresB` on wasm-2.0 `Step_pure` -/

/-- A firing wasm-2.0 `Step_pure` rule, read back to an assignment. -/
theorem firesB20_inv {B : Builtins} {k : Nat} {nm : IL.Id} {qs : List Param} {e : Exp}
    {prems : List Prem}
    (h : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" k (.ruleD nm qs "%~>%" e prems)) {v : Value}
    (hf : Silmaril.Wasm.SpecTec.Sim.Round6.Reading.FiresB (simEnv20 B) "Step_pure" k v) :
    ∃ σ, QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ) qs ∧
      EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) e v ∧
      ∀ pr ∈ prems, PremW (simEnv20 B) (DDerives (simEnv20 B) (otherwise (simEnv20 B)))
        (otherwise (simEnv20 B) "Step_pure" [] k v) (VarEnv.empty.bindVals σ) pr :=
  fires_inv h ((firesB_pure20_iff B).1 hf)

/-- A wasm-2.0 `Step_pure` rule fires at an assignment. -/
theorem firesB20_of {B : Builtins} {k : Nat} {nm : IL.Id} {qs : List Param} {e : Exp}
    {prems : List Prem}
    (h : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" k (.ruleD nm qs "%~>%" e prems))
    (σ : List (IL.Id × Value)) {v : Value}
    (hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ) qs)
    (he : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) e v)
    (hp : ∀ pr ∈ prems, PremW (simEnv20 B) (DDerives (simEnv20 B) (otherwise (simEnv20 B)))
      (otherwise (simEnv20 B) "Step_pure" [] k v) (VarEnv.empty.bindVals σ) pr) :
    Silmaril.Wasm.SpecTec.Sim.Round6.Reading.FiresB (simEnv20 B) "Step_pure" k v :=
  (firesB_pure20_iff B).2 (fires_of_ruleAt h σ hq he hp)

/-! ## The `i32` side conditions -/

/-- `c =/= 0`, read back. -/
theorem ne_zero_of_cmp {c : BitVec 32}
    (h : cmpValues .neOp (.num (.natN c.toNat)) (.num (.natN 0)) = .ok (.bool true)) :
    c ≠ 0 := by
  intro h0
  subst h0
  simp [cmpValues] at h

/-- `c = 0`, read back. -/
theorem eq_zero_of_cmp {c : BitVec 32}
    (h : cmpValues .eqOp (.num (.natN c.toNat)) (.num (.natN 0)) = .ok (.bool true)) :
    c = 0 := by
  have hk : c.toNat = 0 := by simpa [cmpValues] using h
  exact BitVec.eq_of_toNat_eq (hk.trans BitVec.toNat_zero.symm)

/-- `c =/= 0`, evaluated. -/
theorem cmp_ne_zero {c : BitVec 32} (hc : c ≠ 0) :
    cmpValues .neOp (.num (.natN c.toNat)) (.num (.natN 0)) = .ok (.bool true) := by
  have hk : c.toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq (h.trans BitVec.toNat_zero.symm))
  simp [cmpValues, hk]

/-- `0 = 0`, evaluated. -/
theorem cmp_eq_zero :
    cmpValues .eqOp (.num (.natN (0 : BitVec 32).toNat)) (.num (.natN 0)) = .ok (.bool true) := by
  simp [cmpValues]

end Silmaril.Wasm.SpecTec.Sim20.Pure
