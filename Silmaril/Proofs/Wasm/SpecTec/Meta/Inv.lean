module

public import Silmaril.Proofs.Wasm.SpecTec.Meta.Numbin

/-!
# Inverting and building the fragment's rules of `Step_exp`

For each rule `r` of `Step_exp` the fragment reaches, `…_inv` says what a derivation by `r` of
`S |- l ~> x` tells about `l` and `x`, for any environment and any reading `D` of the premises.
The method is uniform: the quantifiers have values (`QuantsOk`), the conclusion is evaluated
forward from them (`evalExp_con`, …), and determinism (`EvalExp.unique`) equates the result with
the given `(S, l, x)`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Meta

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (DDerives QuantsOk TypedV ValsOnly RuleBody PremW Interp)

set_option maxRecDepth 100000

/-! ## Evaluation, forwards -/

theorem evalExps_two {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v₁ v₂ : Value}
    (h₁ : EvalExp env ρ e₁ v₁) (h₂ : EvalExp env ρ e₂ v₂) : EvalExps env ρ [e₁, e₂] [v₁, v₂] :=
  evalExps_cons h₁ (evalExps_cons h₂ evalExps_nil)

theorem evalExps_three {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ : Exp} {v₁ v₂ v₃ : Value}
    (h₁ : EvalExp env ρ e₁ v₁) (h₂ : EvalExp env ρ e₂ v₂) (h₃ : EvalExp env ρ e₃ v₃) :
    EvalExps env ρ [e₁, e₂, e₃] [v₁, v₂, v₃] :=
  evalExps_cons h₁ (evalExps_two h₂ h₃)

theorem evalExp_tuple {env : Env} {ρ : VarEnv} {es : List Exp} {vs : List Value}
    (h : EvalExps env ρ es vs) : EvalExp env ρ (.tupE es) (.tuple vs) :=
  evalExp_tupE_iff.2 ⟨vs, h, rfl⟩

theorem evalExp_con {env : Env} {ρ : VarEnv} {c : MixopS} {es : List Exp} {vs : List Value}
    (h : EvalExps env ρ es vs) : EvalExp env ρ (.caseE c (.tupE es)) (con c vs) :=
  evalExp_caseE_iff.2 ⟨_, evalExp_tuple h, rfl⟩

theorem evalExp_sub {env : Env} {ρ : VarEnv} {e : Exp} {t₁ t₂ : Typ} {v : Value}
    (h : EvalExp env ρ e v) : EvalExp env ρ (.subE e t₁ t₂) v :=
  evalExp_subE_iff.2 h

/-! ## Rule bodies -/

/-- A rule body of a parameterless relation: a scope binding the quantifiers, the conclusion's
value, and the premises. -/
theorem ruleBody_inv {env : Env} {D : Interp} {els : Prop} {op op' : MixopS} {nm : IL.Id}
    {qs : List Param} {e : Exp} {prems : List Prem} {v : Value}
    (h : RuleBody env D els [] [] op (.ruleD nm qs op' e prems) v) :
    ∃ ρ : VarEnv, ValsOnly ρ ∧ QuantsOk env ρ qs ∧ EvalExp env ρ e v ∧
      ∀ pr ∈ prems, PremW env D els ρ pr := by
  obtain ⟨-, ρ₀, σ, hps, hq, he, hp⟩ := h
  have hρ₀ : ρ₀ = VarEnv.empty := by simpa [bindParams] using hps.symm
  subst hρ₀
  exact ⟨_, ⟨rfl, rfl, rfl⟩, hq, he, hp⟩

/-- A quantifier's value. -/
theorem quant_val {env : Env} {ρ : VarEnv} {qs : List Param} (hq : QuantsOk env ρ qs)
    (x : IL.Id) {t : Typ} (hm : Param.expP x t ∈ qs) :
    ∃ w, ρ.findVal? x = some w ∧ HasTyp env ρ t w :=
  hq x t hm

/-- A premise `R (x₁, x₂, x₃)` on three variables. -/
theorem premW_rule3 {env : Env} {D : Interp} {els : Prop} {ρ : VarEnv} {R : IL.Id} {op : MixopS}
    {x₁ x₂ x₃ : IL.Id} {v₁ v₂ v₃ : Value} (h₁ : ρ.findVal? x₁ = some v₁)
    (h₂ : ρ.findVal? x₂ = some v₂) (h₃ : ρ.findVal? x₃ = some v₃)
    (h : PremW env D els ρ (.rulePr R [] op (.tupE [.varE x₁, .varE x₂, .varE x₃]))) :
    D R op [] (.tuple [v₁, v₂, v₃]) := by
  cases h with
  | rulePr ha he hd =>
    have hw := he.unique (evalExp_tuple (evalExps_three (evalExp_var h₁) (evalExp_var h₂)
      (evalExp_var h₃)))
    rw [evalArgs_nil_eq ha, hw] at hd
    exact hd

/-- A three-component tuple against a known three-component value. -/
theorem evalExp_tup3_iff {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ : Exp} {v₁ v₂ v₃ : Value} :
    EvalExp env ρ (.tupE [e₁, e₂, e₃]) (.tuple [v₁, v₂, v₃]) ↔
      EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ ∧ EvalExp env ρ e₃ v₃ := by
  constructor
  · intro h
    obtain ⟨vs, hvs, hv⟩ := evalExp_tupE_iff.1 h
    obtain ⟨w₁, ws₁, h₁, hws₁, rfl⟩ := evalExps_cons_iff.1 hvs
    obtain ⟨w₂, ws₂, h₂, hws₂, rfl⟩ := evalExps_cons_iff.1 hws₁
    obtain ⟨w₃, ws₃, h₃, hws₃, rfl⟩ := evalExps_cons_iff.1 hws₂
    obtain rfl := evalExps_nil_iff.1 hws₃
    have hv' : v₁ = w₁ ∧ v₂ = w₂ ∧ v₃ = w₃ := by simpa using hv
    obtain ⟨rfl, rfl, rfl⟩ := hv'
    exact ⟨h₁, h₂, h₃⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact evalExp_tuple (evalExps_three h₁ h₂ h₃)

/-- A one-field constructor whose value is not known yet. -/
theorem evalExp_con1_inv {env : Env} {ρ : VarEnv} {c : MixopS} {e : Exp} {v : Value}
    (h : EvalExp env ρ (.caseE c (.tupE [e])) v) : ∃ w, v = con c [w] ∧ EvalExp env ρ e w := by
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 hu
  obtain ⟨w, ws, hw, hws, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain rfl := evalExps_nil_iff.1 hws
  exact ⟨w, rfl, hw⟩

/-- A call of a defined function, read through its clauses (no builtins). -/
theorem callDef_iff_try {env : Env} {ρ : VarEnv} (hρ : ValsOnly ρ) {f : IL.Id}
    {ps : List Param} {t : Typ} {cs : List Clause} (hd : env.findDef? f = some (ps, t, cs))
    (hb : ∀ ws, env.builtins.call f ws = none) {args : List Arg} {ws : List ArgV}
    (ha : EvalArgs env ρ args ws) {v : Value} :
    CallDef env ρ f args v ↔ TryClauses env cs ws v := by
  have hfd : ρ.findDef? f = none := by simp [VarEnv.findDef?, hρ.2.1]
  refine ⟨fun h => ?_, callDef_of_tryClauses hfd hd ha⟩
  obtain ⟨ws', ps', t', cs', ha', hd', hc⟩ := Silmaril.SpecTec.Equiv.ExecNumeric.callDef_iff.1 h
  rw [hfd, Option.getD_none, hd] at hd'
  have e : cs = cs' := by simp only [Option.some.injEq, Prod.mk.injEq] at hd'; exact hd'.2.2
  subst e
  obtain rfl := Silmaril.SpecTec.Equiv.ExecNumeric.evalArgs_unique ha ha'
  rcases hc with hc | ⟨-, hbv⟩
  · exact hc
  · rw [hfd, Option.getD_none, hb] at hbv; cases hbv

/-! ## `UN-ctx` -/

theorem unCtx_inv {env : Env} {D : Interp} {els : Prop} {S o a x : Value}
    (h : RuleBody env D els [] [] "%|-%~>%" Rules.F.unCtx (.tuple [S, con "UN" [o, a], x])) :
    ∃ w, x = con "UN" [o, w] ∧ D "Step_exp" "%|-%~>%" [] (.tuple [S, a, w]) := by
  obtain ⟨ρ, -, hq, he, hp⟩ := ruleBody_inv h
  obtain ⟨vS, hS, -⟩ := quant_val hq "S" (t := .varT "S" []) (by simp)
  obtain ⟨vo, ho, -⟩ := quant_val hq "op" (t := .varT "unop" []) (by simp)
  obtain ⟨ve, hev, -⟩ := quant_val hq "e" (t := .varT "exp" []) (by simp)
  obtain ⟨ve', he', -⟩ := quant_val hq "e'" (t := .varT "exp" []) (by simp)
  have hc : EvalExp env ρ (.tupE [.varE "S", .caseE "UN" (.tupE [.varE "op", .varE "e"]),
      .caseE "UN" (.tupE [.varE "op", .varE "e'"])]) (.tuple [vS, con "UN" [vo, ve], con "UN" [vo, ve']]) :=
    evalExp_tuple (evalExps_three (evalExp_var hS)
      (evalExp_con (evalExps_two (evalExp_var ho) (evalExp_var hev)))
      (evalExp_con (evalExps_two (evalExp_var ho) (evalExp_var he'))))
  have hv := he.unique hc
  simp only [con, Value.tuple.injEq, List.cons.injEq, Value.case.injEq, true_and, and_true] at hv
  obtain ⟨rfl, ⟨rfl, rfl⟩, rfl⟩ := hv
  exact ⟨ve', rfl, premW_rule3 hS hev he' (hp _ (by simp))⟩

/-- `v` has type `t` in some scope that binds values only. -/
def TypedIn (env : Env) (t : Typ) (v : Value) : Prop := ∃ ρ, ValsOnly ρ ∧ HasTyp env ρ t v

/-! ## The congruence rules -/

/-- The shape of `BIN-ctx1` and `CMP-ctx1`. -/
theorem ctx1_inv {env : Env} {D : Interp} {els : Prop} {C : MixopS} {T : Typ} {nm : IL.Id}
    {S o a b x : Value}
    (h : RuleBody env D els [] [] "%|-%~>%" (.ruleD nm [.expP "S" (.varT "S" []), .expP "op" T,
      .expP "e_1" (.varT "exp" []), .expP "e_2" (.varT "exp" []), .expP "e_1'" (.varT "exp" [])]
      "%|-%~>%" (.tupE [.varE "S", .caseE C (.tupE [.varE "op", .varE "e_1", .varE "e_2"]),
        .caseE C (.tupE [.varE "op", .varE "e_1'", .varE "e_2"])])
      [.rulePr "Step_exp" [] "%|-%~>%" (.tupE [.varE "S", .varE "e_1", .varE "e_1'"])])
      (.tuple [S, con C [o, a, b], x])) :
    ∃ w, x = con C [o, w, b] ∧ D "Step_exp" "%|-%~>%" [] (.tuple [S, a, w]) := by
  obtain ⟨ρ, -, hq, he, hp⟩ := ruleBody_inv h
  obtain ⟨vS, hS, -⟩ := quant_val hq "S" (t := .varT "S" []) (by simp)
  obtain ⟨vo, ho, -⟩ := quant_val hq "op" (t := T) (by simp)
  obtain ⟨v₁, h₁, -⟩ := quant_val hq "e_1" (t := .varT "exp" []) (by simp)
  obtain ⟨v₂, h₂, -⟩ := quant_val hq "e_2" (t := .varT "exp" []) (by simp)
  obtain ⟨v₁', h₁', -⟩ := quant_val hq "e_1'" (t := .varT "exp" []) (by simp)
  have hv := he.unique (evalExp_tuple (evalExps_three (evalExp_var hS)
    (evalExp_con (evalExps_three (evalExp_var ho) (evalExp_var h₁) (evalExp_var h₂)))
    (evalExp_con (evalExps_three (evalExp_var ho) (evalExp_var h₁') (evalExp_var h₂)))))
  simp only [con, Value.tuple.injEq, List.cons.injEq, Value.case.injEq, true_and, and_true] at hv
  obtain ⟨rfl, ⟨rfl, rfl, rfl⟩, rfl⟩ := hv
  exact ⟨v₁', rfl, premW_rule3 hS h₁ h₁' (hp _ (by simp))⟩

/-- The shape of `BIN-ctx2` and `CMP-ctx2` after erratum M1. -/
theorem ctx2_inv {env : Env} {D : Interp} {els : Prop} {C : MixopS} {T : Typ} {nm : IL.Id}
    {S o a b x : Value}
    (h : RuleBody env D els [] [] "%|-%~>%" (.ruleD nm [.expP "S" (.varT "S" []), .expP "op" T,
      .expP "e_1" (.varT "exp" []), .expP "e_2" (.varT "exp" []), .expP "e_2'" (.varT "exp" [])]
      "%|-%~>%" (.tupE [.varE "S", .caseE C (.tupE [.varE "op", .varE "e_1", .varE "e_2"]),
        .caseE C (.tupE [.varE "op", .varE "e_1", .varE "e_2'"])])
      [.rulePr "Step_exp" [] "%|-%~>%" (.tupE [.varE "S", .varE "e_2", .varE "e_2'"])])
      (.tuple [S, con C [o, a, b], x])) :
    ∃ w, x = con C [o, a, w] ∧ D "Step_exp" "%|-%~>%" [] (.tuple [S, b, w]) := by
  obtain ⟨ρ, -, hq, he, hp⟩ := ruleBody_inv h
  obtain ⟨vS, hS, -⟩ := quant_val hq "S" (t := .varT "S" []) (by simp)
  obtain ⟨vo, ho, -⟩ := quant_val hq "op" (t := T) (by simp)
  obtain ⟨v₁, h₁, -⟩ := quant_val hq "e_1" (t := .varT "exp" []) (by simp)
  obtain ⟨v₂, h₂, -⟩ := quant_val hq "e_2" (t := .varT "exp" []) (by simp)
  obtain ⟨v₂', h₂', -⟩ := quant_val hq "e_2'" (t := .varT "exp" []) (by simp)
  have hv := he.unique (evalExp_tuple (evalExps_three (evalExp_var hS)
    (evalExp_con (evalExps_three (evalExp_var ho) (evalExp_var h₁) (evalExp_var h₂)))
    (evalExp_con (evalExps_three (evalExp_var ho) (evalExp_var h₁) (evalExp_var h₂')))))
  simp only [con, Value.tuple.injEq, List.cons.injEq, Value.case.injEq, true_and, and_true] at hv
  obtain ⟨rfl, ⟨rfl, rfl, rfl⟩, rfl⟩ := hv
  exact ⟨v₂', rfl, premW_rule3 hS h₂ h₂' (hp _ (by simp))⟩

/-! ## The computation rules -/

theorem evalArgs_vars2 {env : Env} {ρ : VarEnv} {x₁ x₂ : IL.Id} {v₁ v₂ : Value}
    (h₁ : ρ.findVal? x₁ = some v₁) (h₂ : ρ.findVal? x₂ = some v₂) :
    EvalArgs env ρ [.expA (.varE x₁), .expA (.varE x₂)] (args2 v₁ v₂) :=
  Equiv.evalArgs_cons (evalExp_var h₁) (Equiv.evalArgs_cons (evalExp_var h₂) Equiv.evalArgs_nil)

theorem evalArgs_vars3 {env : Env} {ρ : VarEnv} {x₁ x₂ x₃ : IL.Id} {v₁ v₂ v₃ : Value}
    (h₁ : ρ.findVal? x₁ = some v₁) (h₂ : ρ.findVal? x₂ = some v₂)
    (h₃ : ρ.findVal? x₃ = some v₃) :
    EvalArgs env ρ [.expA (.varE x₁), .expA (.varE x₂), .expA (.varE x₃)] (args3 v₁ v₂ v₃) :=
  Equiv.evalArgs_cons (evalExp_var h₁) (evalArgs_vars2 h₂ h₃)

theorem unBool_inv {env : Env} {D : Interp} {els : Prop} {ps : List Param} {t : Typ}
    {cs : List Clause} (hd : env.findDef? "boolun" = some (ps, t, cs))
    (hb : ∀ ws, env.builtins.call "boolun" ws = none) {S o a x : Value}
    (h : RuleBody env D els [] [] "%|-%~>%" Rules.F.unBool (.tuple [S, con "UN" [o, a], x])) :
    ∃ bv w, a = con "BOOL" [.bool bv] ∧ x = con "BOOL" [w] ∧
      TryClauses env cs (args2 o (.bool bv)) w := by
  obtain ⟨ρ, hρ, hq, he, -⟩ := ruleBody_inv h
  obtain ⟨vo, ho, -⟩ := quant_val hq "boolunop" (t := .varT "boolunop" []) (by simp)
  obtain ⟨vb, hvb, hbt⟩ := quant_val hq "b" (t := .boolT) (by simp)
  obtain ⟨bv, rfl⟩ := hasTyp_boolT_iff.1 hbt
  obtain ⟨-, h₂, h₃⟩ := evalExp_tup3_iff.1 he
  have hv := h₂.unique (evalExp_con (evalExps_two (evalExp_sub (evalExp_var ho))
    (evalExp_con (evalExps_cons (evalExp_var hvb) evalExps_nil))))
  simp only [con, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at hv
  obtain ⟨rfl, rfl⟩ := hv
  obtain ⟨w, rfl, hw⟩ := evalExp_con1_inv h₃
  exact ⟨bv, w, rfl, rfl, (callDef_iff_try hρ hd hb (evalArgs_vars2 ho hvb)).1
    (evalExp_callE_iff.1 hw)⟩

theorem unNum_inv {env : Env} {D : Interp} {els : Prop} {ps : List Param} {t : Typ}
    {cs : List Clause} (hd : env.findDef? "numun" = some (ps, t, cs))
    (hb : ∀ ws, env.builtins.call "numun" ws = none) {S o a x : Value}
    (h : RuleBody env D els [] [] "%|-%~>%" Rules.F.unNum (.tuple [S, con "UN" [o, a], x])) :
    TypedIn env (.varT "num" []) a ∧ TryClauses env cs (args2 o a) x := by
  obtain ⟨ρ, hρ, hq, he, -⟩ := ruleBody_inv h
  obtain ⟨vo, ho, -⟩ := quant_val hq "numunop" (t := .varT "numunop" []) (by simp)
  obtain ⟨vn, hn, hnt⟩ := quant_val hq "num" (t := .varT "num" []) (by simp)
  obtain ⟨-, h₂, h₃⟩ := evalExp_tup3_iff.1 he
  have hv := h₂.unique (evalExp_con (evalExps_two (evalExp_sub (evalExp_var ho))
    (evalExp_sub (evalExp_var hn))))
  simp only [con, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at hv
  obtain ⟨rfl, rfl⟩ := hv
  exact ⟨⟨ρ, hρ, hnt⟩, (callDef_iff_try hρ hd hb (evalArgs_vars2 ho hn)).1
    (evalExp_callE_iff.1 (evalExp_subE_iff.1 h₃))⟩

theorem binBool_inv {env : Env} {D : Interp} {els : Prop} {ps : List Param} {t : Typ}
    {cs : List Clause} (hd : env.findDef? "boolbin" = some (ps, t, cs))
    (hb : ∀ ws, env.builtins.call "boolbin" ws = none) {S o a b x : Value}
    (h : RuleBody env D els [] [] "%|-%~>%" Rules.F.binBool (.tuple [S, con "BIN" [o, a, b], x])) :
    ∃ b₁ b₂ w, a = con "BOOL" [.bool b₁] ∧ b = con "BOOL" [.bool b₂] ∧ x = con "BOOL" [w] ∧
      TryClauses env cs (args3 o (.bool b₁) (.bool b₂)) w := by
  obtain ⟨ρ, hρ, hq, he, -⟩ := ruleBody_inv h
  obtain ⟨vo, ho, -⟩ := quant_val hq "boolbinop" (t := .varT "boolbinop" []) (by simp)
  obtain ⟨v₁, hv₁, ht₁⟩ := quant_val hq "b_1" (t := .boolT) (by simp)
  obtain ⟨v₂, hv₂, ht₂⟩ := quant_val hq "b_2" (t := .boolT) (by simp)
  obtain ⟨b₁, rfl⟩ := hasTyp_boolT_iff.1 ht₁
  obtain ⟨b₂, rfl⟩ := hasTyp_boolT_iff.1 ht₂
  obtain ⟨-, h₂, h₃⟩ := evalExp_tup3_iff.1 he
  have hv := h₂.unique (evalExp_con (evalExps_three (evalExp_sub (evalExp_var ho))
    (evalExp_con (evalExps_cons (evalExp_var hv₁) evalExps_nil))
    (evalExp_con (evalExps_cons (evalExp_var hv₂) evalExps_nil))))
  simp only [con, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at hv
  obtain ⟨rfl, rfl, rfl⟩ := hv
  obtain ⟨w, rfl, hw⟩ := evalExp_con1_inv h₃
  exact ⟨b₁, b₂, w, rfl, rfl, rfl, (callDef_iff_try hρ hd hb (evalArgs_vars3 ho hv₁ hv₂)).1
    (evalExp_callE_iff.1 hw)⟩

theorem binNum_inv {env : Env} {D : Interp} {els : Prop} {ps : List Param} {t : Typ}
    {cs : List Clause} (hd : env.findDef? "numbin" = some (ps, t, cs))
    (hb : ∀ ws, env.builtins.call "numbin" ws = none) {S o a b x : Value}
    (h : RuleBody env D els [] [] "%|-%~>%" Rules.F.binNum (.tuple [S, con "BIN" [o, a, b], x])) :
    TypedIn env (.varT "num" []) a ∧ TypedIn env (.varT "num" []) b ∧
      TryClauses env cs (args3 o a b) x := by
  obtain ⟨ρ, hρ, hq, he, -⟩ := ruleBody_inv h
  obtain ⟨vo, ho, -⟩ := quant_val hq "numbinop" (t := .varT "numbinop" []) (by simp)
  obtain ⟨v₁, hv₁, ht₁⟩ := quant_val hq "num_1" (t := .varT "num" []) (by simp)
  obtain ⟨v₂, hv₂, ht₂⟩ := quant_val hq "num_2" (t := .varT "num" []) (by simp)
  obtain ⟨-, h₂, h₃⟩ := evalExp_tup3_iff.1 he
  have hv := h₂.unique (evalExp_con (evalExps_three (evalExp_sub (evalExp_var ho))
    (evalExp_sub (evalExp_var hv₁)) (evalExp_sub (evalExp_var hv₂))))
  simp only [con, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at hv
  obtain ⟨rfl, rfl, rfl⟩ := hv
  exact ⟨⟨ρ, hρ, ht₁⟩, ⟨ρ, hρ, ht₂⟩, (callDef_iff_try hρ hd hb (evalArgs_vars3 ho hv₁ hv₂)).1
    (evalExp_callE_iff.1 (evalExp_subE_iff.1 h₃))⟩

theorem cmpNum_inv {env : Env} {D : Interp} {els : Prop} {ps : List Param} {t : Typ}
    {cs : List Clause} (hd : env.findDef? "numcmp" = some (ps, t, cs))
    (hb : ∀ ws, env.builtins.call "numcmp" ws = none) {S o a b x : Value}
    (h : RuleBody env D els [] [] "%|-%~>%" Rules.F.cmpNum (.tuple [S, con "CMP" [o, a, b], x])) :
    TypedIn env (.varT "num" []) a ∧ TypedIn env (.varT "num" []) b ∧
      ∃ w, x = con "BOOL" [w] ∧ TryClauses env cs (args3 o a b) w := by
  obtain ⟨ρ, hρ, hq, he, -⟩ := ruleBody_inv h
  obtain ⟨vo, ho, -⟩ := quant_val hq "numcmpop" (t := .varT "numcmpop" []) (by simp)
  obtain ⟨v₁, hv₁, ht₁⟩ := quant_val hq "num_1" (t := .varT "num" []) (by simp)
  obtain ⟨v₂, hv₂, ht₂⟩ := quant_val hq "num_2" (t := .varT "num" []) (by simp)
  obtain ⟨-, h₂, h₃⟩ := evalExp_tup3_iff.1 he
  have hv := h₂.unique (evalExp_con (evalExps_three (evalExp_sub (evalExp_var ho))
    (evalExp_sub (evalExp_var hv₁)) (evalExp_sub (evalExp_var hv₂))))
  simp only [con, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at hv
  obtain ⟨rfl, rfl, rfl⟩ := hv
  obtain ⟨w, rfl, hw⟩ := evalExp_con1_inv h₃
  exact ⟨⟨ρ, hρ, ht₁⟩, ⟨ρ, hρ, ht₂⟩, w, rfl, (callDef_iff_try hρ hd hb
    (evalArgs_vars3 ho hv₁ hv₂)).1 (evalExp_callE_iff.1 hw)⟩

/-- The shape of the four comparison rules on values (after erratum M1): `CMP C val_1 val_2`
reduces to `BOOL r` when the test `val_1 ⋈ val_2` holds. -/
theorem cmpVal_inv {env : Env} {D : Interp} {els : Prop} {nm : IL.Id} {C : MixopS} {r : Bool}
    {k : CmpOp} {S o a b x : Value}
    (h : RuleBody env D els [] [] "%|-%~>%" (.ruleD nm [.expP "S" (.varT "S" []),
      .expP "val_1" (.varT "val" []), .expP "val_2" (.varT "val" [])] "%|-%~>%"
      (.tupE [.varE "S", .caseE "CMP" (.tupE [.caseE C (.tupE []),
        .subE (.varE "val_1") (.varT "val" []) (.varT "exp" []),
        .subE (.varE "val_2") (.varT "val" []) (.varT "exp" [])]),
        .caseE "BOOL" (.tupE [.boolE r])])
      [.ifPr (.cmpE k .boolT (.varE "val_1") (.varE "val_2"))])
      (.tuple [S, con "CMP" [o, a, b], x])) :
    o = con C [] ∧ x = con "BOOL" [.bool r] ∧ TypedIn env (.varT "val" []) a ∧
      TypedIn env (.varT "val" []) b ∧ cmpValues k a b = .ok (.bool true) := by
  obtain ⟨ρ, hρ, hq, he, hp⟩ := ruleBody_inv h
  obtain ⟨v₁, hv₁, ht₁⟩ := quant_val hq "val_1" (t := .varT "val" []) (by simp)
  obtain ⟨v₂, hv₂, ht₂⟩ := quant_val hq "val_2" (t := .varT "val" []) (by simp)
  obtain ⟨-, h₂, h₃⟩ := evalExp_tup3_iff.1 he
  have hv := h₂.unique (evalExp_con (evalExps_three (evalExp_con evalExps_nil)
    (evalExp_sub (evalExp_var hv₁)) (evalExp_sub (evalExp_var hv₂))))
  simp only [con, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at hv
  obtain ⟨rfl, rfl, rfl⟩ := hv
  have hx := h₃.unique (evalExp_con (evalExps_cons (evalExp_boolE_iff.2 rfl) evalExps_nil))
  have hk : EvalExp env ρ (.cmpE k .boolT (.varE "val_1") (.varE "val_2")) (.bool true) := by
    cases hp _ (List.mem_singleton_self _) with | ifPr h => exact h
  obtain ⟨u₁, u₂, k₁, k₂, hc⟩ := evalExp_cmpE_iff.1 hk
  obtain rfl := (evalExp_var hv₁).unique k₁
  obtain rfl := (evalExp_var hv₂).unique k₂
  exact ⟨rfl, hx, ⟨ρ, hρ, ht₁⟩, ⟨ρ, hρ, ht₂⟩, hc⟩

end Silmaril.Wasm.SpecTec.Meta
