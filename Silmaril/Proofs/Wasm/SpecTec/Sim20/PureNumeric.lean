module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureControl

/-!
# Numeric rules of wasm-2.0 `Step_pure`, rule by rule

Two layers.

* **IL level, unconditional.** For arbitrary IL values: `unop-val` (20), `binop-val` (22),
  `binop-trap` (23), `testop` (24) and `relop` (25) fire exactly when their premise about the
  script's numeric function holds, read through `ExecNumeric.Applies` (`*_inv` and `*_fires`).
  These five rules are byte-identical to wasm-3.0's (`Sim20.Census`).
* **V2 level, under two hypotheses.** With `NumAgree` (the script's `$unop_`, `$binop_`,
  `$testop_`, `$relop_` agree with V2's numerics) and `NumTyped` (the encodings of numbers and
  operators have their IL types), each rule is the V2 constructor that transcribes it:
  `intUnOp_iff`, `floatUnOp_iff`, `intBinOp_iff`, `floatBinOp_iff`, `intBinOpTrap_iff`,
  `testOp_iff`, `intRelOp_iff`, `floatRelOp_iff`. Both hypotheses are **assumed** here.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Pure

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef evalArgs_three evalArgs_four)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk TypedV ValsOnly evalExp_tup2 evalExp_tup3 evalExp_list1
  evalExp_case)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (FiresB ruleConcl)

variable (B : Builtins)

/-! ## Helpers -/

/-- `c ∈ l`, as the evaluator reads it. -/
theorem memValue_list_iff {c : Value} {vs : List Value} :
    memValue c (.list vs) = .ok (.bool true) ↔ c ∈ vs := by
  simp [memValue]

/-- `OP(x, y)` with two bound variables. -/
theorem evalExp_pair {env : Env} {ρ : VarEnv} {op : MixopS} {x y : IL.Id} {a b : Value}
    (ha : ρ.findVal? x = some a) (hb : ρ.findVal? y = some b) :
    EvalExp env ρ (.caseE op (.tupE [.varE x, .varE y])) (.case op (.tuple [a, b])) :=
  evalExp_case (evalExp_tup2 (evalExp_var ha) (evalExp_var hb))

/-- `numtype`. -/
abbrev numtypeT : Typ := .varT "numtype" []

/-- `T(nt)`. -/
abbrev atNt (T : IL.Id) : Typ := .varT T [.expA (.varE "nt")]

/-! ## `unop-val` -/

/-- The conclusion of `unop-val`, evaluated. -/
theorem eval_unopVal {env : Env} {ρ : VarEnv} {nt c₁ op c : Value}
    (fnt : ρ.findVal? "nt" = some nt) (f₁ : ρ.findVal? "c_1" = some c₁)
    (fop : ρ.findVal? "unop" = some op) (fc : ρ.findVal? "c" = some c) :
    EvalExp env ρ (ruleConcl unopValRule)
      (.tuple [.list [.case "CONST" (.tuple [nt, c₁]), .case "UNOP" (.tuple [nt, op])],
        .list [.case "CONST" (.tuple [nt, c])]]) :=
  evalExp_tup2 (evalExp_list2 (evalExp_pair fnt f₁) (evalExp_pair fnt fop))
    (evalExp_list1 (evalExp_pair fnt fc))

/-- `unop-val`, read back, for arbitrary IL values. -/
theorem unopVal_inv {nt c₁ op w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 20
      (.tuple [.list [.case "CONST" (.tuple [nt, c₁]), .case "UNOP" (.tuple [nt, op])], w])) :
    ∃ c v, w = .list [.case "CONST" (.tuple [nt, c])] ∧
      Applies (simEnv20 B) "unop_" [.val nt, .val op, .val c₁] v ∧
      memValue c v = .ok (.bool true) := by
  obtain ⟨σ, hq, he, hp⟩ := firesB20_inv (hasRuleAt_unopVal B) hf
  obtain ⟨vnt, fnt⟩ := quant_val (x := "nt") (t := numtypeT) hq (by simp)
  obtain ⟨v₁, f₁⟩ := quant_val (x := "c_1") (t := atNt "num_") hq (by simp)
  obtain ⟨vop, fop⟩ := quant_val (x := "unop") (t := atNt "unop_") hq (by simp)
  obtain ⟨vc, fc⟩ := quant_val (x := "c") (t := atNt "num_") hq (by simp)
  have hu := EvalExp.unique he (eval_unopVal fnt f₁ fop fc)
  simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true] at hu
  obtain ⟨⟨⟨rfl, rfl⟩, -, rfl⟩, rfl⟩ := hu
  obtain ⟨a, v, ha, hv, hm⟩ := evalExp_memE_iff.1 (ifPrem (hp _ (List.mem_singleton_self _)))
  have hac : a = vc := EvalExp.unique ha (evalExp_var fc)
  subst hac
  exact ⟨a, v, rfl, (applies_iff_callDef rfl (evalArgs_three fnt fop f₁)).2
    (evalExp_callE_iff.1 hv), hm⟩

/-- The scope of `unop-val`. -/
def scopeUn (nt c₁ op c : Value) : VarEnv :=
  VarEnv.empty.bindVals [("nt", nt), ("c_1", c₁), ("unop", op), ("c", c)]

/-- `unop-val`, fired, for arbitrary IL values. -/
theorem unopVal_fires {nt c₁ op c v : Value}
    (h₀ : HasTyp (simEnv20 B) (scopeUn nt c₁ op c) numtypeT nt)
    (h₁ : HasTyp (simEnv20 B) (scopeUn nt c₁ op c) (atNt "num_") c₁)
    (h₂ : HasTyp (simEnv20 B) (scopeUn nt c₁ op c) (atNt "unop_") op)
    (h₃ : HasTyp (simEnv20 B) (scopeUn nt c₁ op c) (atNt "num_") c)
    (happ : Applies (simEnv20 B) "unop_" [.val nt, .val op, .val c₁] v)
    (hm : memValue c v = .ok (.bool true)) :
    FiresB (simEnv20 B) "Step_pure" 20
      (.tuple [.list [.case "CONST" (.tuple [nt, c₁]), .case "UNOP" (.tuple [nt, op])],
        .list [.case "CONST" (.tuple [nt, c])]]) := by
  have hcall : EvalExp (simEnv20 B) (scopeUn nt c₁ op c)
      (.callE "unop_" [.expA (.varE "nt"), .expA (.varE "unop"), .expA (.varE "c_1")]) v :=
    evalExp_callE_iff.2 ((applies_iff_callDef rfl (evalArgs_three rfl rfl rfl)).1 happ)
  exact firesB20_of (hasRuleAt_unopVal B) _
    (QuantsOk.cons rfl h₀ (QuantsOk.cons rfl h₁ (QuantsOk.cons rfl h₂ (QuantsOk.cons rfl h₃
      QuantsOk.nil)))) (eval_unopVal rfl rfl rfl rfl)
    (prems_one (.ifPr (evalExp_memE_iff.2 ⟨c, v, evalExp_var rfl, hcall, hm⟩)))

/-! ## `binop-val`, `binop-trap` -/

/-- The left-hand side of the `binop` rules, evaluated. -/
theorem eval_binopLhs {env : Env} {ρ : VarEnv} {nt c₁ c₂ op : Value}
    (fnt : ρ.findVal? "nt" = some nt) (f₁ : ρ.findVal? "c_1" = some c₁)
    (f₂ : ρ.findVal? "c_2" = some c₂) (fop : ρ.findVal? "binop" = some op) :
    EvalExp env ρ (.listE [.caseE "CONST" (.tupE [.varE "nt", .varE "c_1"]),
        .caseE "CONST" (.tupE [.varE "nt", .varE "c_2"]),
        .caseE "BINOP" (.tupE [.varE "nt", .varE "binop"])])
      (.list [.case "CONST" (.tuple [nt, c₁]), .case "CONST" (.tuple [nt, c₂]),
        .case "BINOP" (.tuple [nt, op])]) :=
  evalExp_list3 (evalExp_pair fnt f₁) (evalExp_pair fnt f₂) (evalExp_pair fnt fop)

/-- `binop-val`, read back, for arbitrary IL values. -/
theorem binopVal_inv {nt c₁ c₂ op w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 22
      (.tuple [.list [.case "CONST" (.tuple [nt, c₁]), .case "CONST" (.tuple [nt, c₂]),
        .case "BINOP" (.tuple [nt, op])], w])) :
    ∃ c v, w = .list [.case "CONST" (.tuple [nt, c])] ∧
      Applies (simEnv20 B) "binop_" [.val nt, .val op, .val c₁, .val c₂] v ∧
      memValue c v = .ok (.bool true) := by
  obtain ⟨σ, hq, he, hp⟩ := firesB20_inv (hasRuleAt_binopVal B) hf
  obtain ⟨vnt, fnt⟩ := quant_val (x := "nt") (t := numtypeT) hq (by simp)
  obtain ⟨v₁, f₁⟩ := quant_val (x := "c_1") (t := atNt "num_") hq (by simp)
  obtain ⟨v₂, f₂⟩ := quant_val (x := "c_2") (t := atNt "num_") hq (by simp)
  obtain ⟨vop, fop⟩ := quant_val (x := "binop") (t := atNt "binop_") hq (by simp)
  obtain ⟨vc, fc⟩ := quant_val (x := "c") (t := atNt "num_") hq (by simp)
  have hu := EvalExp.unique he (evalExp_tup2 (eval_binopLhs fnt f₁ f₂ fop)
    (evalExp_list1 (evalExp_pair fnt fc)))
  simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true] at hu
  obtain ⟨⟨⟨rfl, rfl⟩, ⟨-, rfl⟩, -, rfl⟩, rfl⟩ := hu
  obtain ⟨a, v, ha, hv, hm⟩ := evalExp_memE_iff.1 (ifPrem (hp _ (List.mem_singleton_self _)))
  have hac : a = vc := EvalExp.unique ha (evalExp_var fc)
  subst hac
  exact ⟨a, v, rfl, (applies_iff_callDef rfl (evalArgs_four fnt fop f₁ f₂)).2
    (evalExp_callE_iff.1 hv), hm⟩

/-- The scope of `binop-val`. -/
def scopeBin (nt c₁ c₂ op c : Value) : VarEnv :=
  VarEnv.empty.bindVals [("nt", nt), ("c_1", c₁), ("c_2", c₂), ("binop", op), ("c", c)]

/-- `binop-val`, fired, for arbitrary IL values. -/
theorem binopVal_fires {nt c₁ c₂ op c v : Value}
    (h₀ : HasTyp (simEnv20 B) (scopeBin nt c₁ c₂ op c) numtypeT nt)
    (h₁ : HasTyp (simEnv20 B) (scopeBin nt c₁ c₂ op c) (atNt "num_") c₁)
    (h₂ : HasTyp (simEnv20 B) (scopeBin nt c₁ c₂ op c) (atNt "num_") c₂)
    (h₃ : HasTyp (simEnv20 B) (scopeBin nt c₁ c₂ op c) (atNt "binop_") op)
    (h₄ : HasTyp (simEnv20 B) (scopeBin nt c₁ c₂ op c) (atNt "num_") c)
    (happ : Applies (simEnv20 B) "binop_" [.val nt, .val op, .val c₁, .val c₂] v)
    (hm : memValue c v = .ok (.bool true)) :
    FiresB (simEnv20 B) "Step_pure" 22
      (.tuple [.list [.case "CONST" (.tuple [nt, c₁]), .case "CONST" (.tuple [nt, c₂]),
        .case "BINOP" (.tuple [nt, op])], .list [.case "CONST" (.tuple [nt, c])]]) := by
  have hcall : EvalExp (simEnv20 B) (scopeBin nt c₁ c₂ op c)
      (.callE "binop_" [.expA (.varE "nt"), .expA (.varE "binop"), .expA (.varE "c_1"),
        .expA (.varE "c_2")]) v :=
    evalExp_callE_iff.2 ((applies_iff_callDef rfl (evalArgs_four rfl rfl rfl rfl)).1 happ)
  exact firesB20_of (hasRuleAt_binopVal B) _
    (QuantsOk.cons rfl h₀ (QuantsOk.cons rfl h₁ (QuantsOk.cons rfl h₂ (QuantsOk.cons rfl h₃
      (QuantsOk.cons rfl h₄ QuantsOk.nil)))))
    (evalExp_tup2 (eval_binopLhs rfl rfl rfl rfl) (evalExp_list1 (evalExp_pair rfl rfl)))
    (prems_one (.ifPr (evalExp_memE_iff.2 ⟨c, v, evalExp_var rfl, hcall, hm⟩)))

/-- `$f(…) = eps`, read back. -/
theorem applies_nil_of_eval {env : Env} {ρ : VarEnv} {f : IL.Id} {args : List Arg}
    {ws : List ArgV} (hd : ρ.findDef? f = none) (ha : EvalArgs env ρ args ws)
    (h : EvalExp env ρ (.cmpE .eqOp .boolT (.callE f args) (.listE [])) (.bool true)) :
    Applies env f ws (.list []) := by
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_cmpE_iff.1 h
  have e₂ : v₂ = .list [] := EvalExp.unique h₂ evalExp_list0
  subst e₂
  have e₁ : v₁ = .list [] := by
    cases v₁ <;> simp_all [cmpValues]
  subst e₁
  exact (applies_iff_callDef hd ha).2 (evalExp_callE_iff.1 h₁)

/-- `binop-trap`, read back, for arbitrary IL values. -/
theorem binopTrap_inv {nt c₁ c₂ op w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 23
      (.tuple [.list [.case "CONST" (.tuple [nt, c₁]), .case "CONST" (.tuple [nt, c₂]),
        .case "BINOP" (.tuple [nt, op])], w])) :
    w = .list [caseNilV "TRAP"] ∧
      Applies (simEnv20 B) "binop_" [.val nt, .val op, .val c₁, .val c₂] (.list []) := by
  obtain ⟨σ, hq, he, hp⟩ := firesB20_inv (hasRuleAt_binopTrap B) hf
  obtain ⟨vnt, fnt⟩ := quant_val (x := "nt") (t := numtypeT) hq (by simp)
  obtain ⟨v₁, f₁⟩ := quant_val (x := "c_1") (t := atNt "num_") hq (by simp)
  obtain ⟨v₂, f₂⟩ := quant_val (x := "c_2") (t := atNt "num_") hq (by simp)
  obtain ⟨vop, fop⟩ := quant_val (x := "binop") (t := atNt "binop_") hq (by simp)
  have hu := EvalExp.unique he (evalExp_tup2 (eval_binopLhs fnt f₁ f₂ fop)
    (evalExp_list1 evalExp_caseNil))
  simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true] at hu
  obtain ⟨⟨⟨rfl, rfl⟩, ⟨-, rfl⟩, -, rfl⟩, rfl⟩ := hu
  exact ⟨rfl, applies_nil_of_eval rfl (evalArgs_four fnt fop f₁ f₂)
    (ifPrem (hp _ (List.mem_singleton_self _)))⟩

/-- The scope of `binop-trap`. -/
def scopeBinT (nt c₁ c₂ op : Value) : VarEnv :=
  VarEnv.empty.bindVals [("nt", nt), ("c_1", c₁), ("c_2", c₂), ("binop", op)]

/-- `binop-trap`, fired, for arbitrary IL values. -/
theorem binopTrap_fires {nt c₁ c₂ op : Value}
    (h₀ : HasTyp (simEnv20 B) (scopeBinT nt c₁ c₂ op) numtypeT nt)
    (h₁ : HasTyp (simEnv20 B) (scopeBinT nt c₁ c₂ op) (atNt "num_") c₁)
    (h₂ : HasTyp (simEnv20 B) (scopeBinT nt c₁ c₂ op) (atNt "num_") c₂)
    (h₃ : HasTyp (simEnv20 B) (scopeBinT nt c₁ c₂ op) (atNt "binop_") op)
    (happ : Applies (simEnv20 B) "binop_" [.val nt, .val op, .val c₁, .val c₂] (.list [])) :
    FiresB (simEnv20 B) "Step_pure" 23
      (.tuple [.list [.case "CONST" (.tuple [nt, c₁]), .case "CONST" (.tuple [nt, c₂]),
        .case "BINOP" (.tuple [nt, op])], .list [caseNilV "TRAP"]]) := by
  have hcall : EvalExp (simEnv20 B) (scopeBinT nt c₁ c₂ op)
      (.callE "binop_" [.expA (.varE "nt"), .expA (.varE "binop"), .expA (.varE "c_1"),
        .expA (.varE "c_2")]) (.list []) :=
    evalExp_callE_iff.2 ((applies_iff_callDef rfl (evalArgs_four rfl rfl rfl rfl)).1 happ)
  have hif : EvalExp (simEnv20 B) (scopeBinT nt c₁ c₂ op)
      (.cmpE .eqOp .boolT (.callE "binop_" [.expA (.varE "nt"), .expA (.varE "binop"),
        .expA (.varE "c_1"), .expA (.varE "c_2")]) (.listE [])) (.bool true) :=
    evalExp_cmpE_iff.2 ⟨_, _, hcall, evalExp_list0, by simp [cmpValues]⟩
  exact firesB20_of (hasRuleAt_binopTrap B) _
    (QuantsOk.cons rfl h₀ (QuantsOk.cons rfl h₁ (QuantsOk.cons rfl h₂ (QuantsOk.cons rfl h₃
      QuantsOk.nil))))
    (evalExp_tup2 (eval_binopLhs rfl rfl rfl rfl) (evalExp_list1 evalExp_caseNil))
    (prems_one (.ifPr hif))


/-! ## `testop`, `relop` -/

/-- `x = $f(…)`, read back. -/
theorem applies_of_eqPrem {env : Env} {ρ : VarEnv} {f : IL.Id} {args : List Arg}
    {ws : List ArgV} {c : Value} (hd : ρ.findDef? f = none) (ha : EvalArgs env ρ args ws)
    (fc : ρ.findVal? "c" = some c)
    (h : EvalExp env ρ (.cmpE .eqOp .boolT (.varE "c") (.callE f args)) (.bool true)) :
    Applies env f ws c := by
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_cmpE_iff.1 h
  have e₁ : v₁ = c := EvalExp.unique h₁ (evalExp_var fc)
  have e₂ : v₁ = v₂ := by simpa [cmpValues] using hc
  subst e₁ e₂
  exact (applies_iff_callDef hd ha).2 (evalExp_callE_iff.1 h₂)

/-- `x = $f(…)`, evaluated. -/
theorem eqPrem_of_applies {env : Env} {ρ : VarEnv} {f : IL.Id} {args : List Arg}
    {ws : List ArgV} {c : Value} (hd : ρ.findDef? f = none) (ha : EvalArgs env ρ args ws)
    (fc : ρ.findVal? "c" = some c) (happ : Applies env f ws c) :
    EvalExp env ρ (.cmpE .eqOp .boolT (.varE "c") (.callE f args)) (.bool true) :=
  evalExp_cmpE_iff.2 ⟨_, _, evalExp_var fc,
    evalExp_callE_iff.2 ((applies_iff_callDef hd ha).1 happ), by simp [cmpValues]⟩

/-- `testop`, read back, for arbitrary IL values. -/
theorem testop_inv {nt c₁ op w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 24
      (.tuple [.list [.case "CONST" (.tuple [nt, c₁]), .case "TESTOP" (.tuple [nt, op])], w])) :
    ∃ c, w = .list [.case "CONST" (.tuple [caseNilV "I32", c])] ∧
      Applies (simEnv20 B) "testop_" [.val nt, .val op, .val c₁] c := by
  obtain ⟨σ, hq, he, hp⟩ := firesB20_inv (hasRuleAt_testop B) hf
  obtain ⟨vnt, fnt⟩ := quant_val (x := "nt") (t := numtypeT) hq (by simp)
  obtain ⟨v₁, f₁⟩ := quant_val (x := "c_1") (t := atNt "num_") hq (by simp)
  obtain ⟨vop, fop⟩ := quant_val (x := "testop") (t := atNt "testop_") hq (by simp)
  obtain ⟨vc, fc⟩ := quant_val (x := "c") (t := i32T) hq (by simp)
  have hu := EvalExp.unique he (evalExp_tup2 (evalExp_list2 (evalExp_pair fnt f₁)
    (evalExp_pair fnt fop)) (evalExp_list1 (evalExp_case (evalExp_tup2 evalExp_caseNil
      (evalExp_var fc)))))
  simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true] at hu
  obtain ⟨⟨⟨rfl, rfl⟩, -, rfl⟩, rfl⟩ := hu
  exact ⟨vc, rfl, applies_of_eqPrem rfl (evalArgs_three fnt fop f₁) fc
    (ifPrem (hp _ (List.mem_singleton_self _)))⟩

/-- The scope of `testop`. -/
def scopeTest (nt c₁ op c : Value) : VarEnv :=
  VarEnv.empty.bindVals [("nt", nt), ("c_1", c₁), ("testop", op), ("c", c)]

/-- `testop`, fired, for arbitrary IL values. -/
theorem testop_fires {nt c₁ op c : Value}
    (h₀ : HasTyp (simEnv20 B) (scopeTest nt c₁ op c) numtypeT nt)
    (h₁ : HasTyp (simEnv20 B) (scopeTest nt c₁ op c) (atNt "num_") c₁)
    (h₂ : HasTyp (simEnv20 B) (scopeTest nt c₁ op c) (atNt "testop_") op)
    (h₃ : HasTyp (simEnv20 B) (scopeTest nt c₁ op c) i32T c)
    (happ : Applies (simEnv20 B) "testop_" [.val nt, .val op, .val c₁] c) :
    FiresB (simEnv20 B) "Step_pure" 24
      (.tuple [.list [.case "CONST" (.tuple [nt, c₁]), .case "TESTOP" (.tuple [nt, op])],
        .list [.case "CONST" (.tuple [caseNilV "I32", c])]]) :=
  firesB20_of (hasRuleAt_testop B) _
    (QuantsOk.cons rfl h₀ (QuantsOk.cons rfl h₁ (QuantsOk.cons rfl h₂ (QuantsOk.cons rfl h₃
      QuantsOk.nil))))
    (evalExp_tup2 (evalExp_list2 (evalExp_pair rfl rfl) (evalExp_pair rfl rfl))
      (evalExp_list1 (evalExp_case (evalExp_tup2 evalExp_caseNil (evalExp_var rfl)))))
    (prems_one (.ifPr (eqPrem_of_applies rfl (evalArgs_three rfl rfl rfl) rfl happ)))

/-- `relop`, read back, for arbitrary IL values. -/
theorem relop_inv {nt c₁ c₂ op w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 25
      (.tuple [.list [.case "CONST" (.tuple [nt, c₁]), .case "CONST" (.tuple [nt, c₂]),
        .case "RELOP" (.tuple [nt, op])], w])) :
    ∃ c, w = .list [.case "CONST" (.tuple [caseNilV "I32", c])] ∧
      Applies (simEnv20 B) "relop_" [.val nt, .val op, .val c₁, .val c₂] c := by
  obtain ⟨σ, hq, he, hp⟩ := firesB20_inv (hasRuleAt_relop B) hf
  obtain ⟨vnt, fnt⟩ := quant_val (x := "nt") (t := numtypeT) hq (by simp)
  obtain ⟨v₁, f₁⟩ := quant_val (x := "c_1") (t := atNt "num_") hq (by simp)
  obtain ⟨v₂, f₂⟩ := quant_val (x := "c_2") (t := atNt "num_") hq (by simp)
  obtain ⟨vop, fop⟩ := quant_val (x := "relop") (t := atNt "relop_") hq (by simp)
  obtain ⟨vc, fc⟩ := quant_val (x := "c") (t := i32T) hq (by simp)
  have hu := EvalExp.unique he (evalExp_tup2 (evalExp_list3 (evalExp_pair fnt f₁)
    (evalExp_pair fnt f₂) (evalExp_pair fnt fop)) (evalExp_list1 (evalExp_case
      (evalExp_tup2 evalExp_caseNil (evalExp_var fc)))))
  simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true] at hu
  obtain ⟨⟨⟨rfl, rfl⟩, ⟨-, rfl⟩, -, rfl⟩, rfl⟩ := hu
  exact ⟨vc, rfl, applies_of_eqPrem rfl (evalArgs_four fnt fop f₁ f₂) fc
    (ifPrem (hp _ (List.mem_singleton_self _)))⟩

/-- The scope of `relop`. -/
def scopeRel (nt c₁ c₂ op c : Value) : VarEnv :=
  VarEnv.empty.bindVals [("nt", nt), ("c_1", c₁), ("c_2", c₂), ("relop", op), ("c", c)]

/-- `relop`, fired, for arbitrary IL values. -/
theorem relop_fires {nt c₁ c₂ op c : Value}
    (h₀ : HasTyp (simEnv20 B) (scopeRel nt c₁ c₂ op c) numtypeT nt)
    (h₁ : HasTyp (simEnv20 B) (scopeRel nt c₁ c₂ op c) (atNt "num_") c₁)
    (h₂ : HasTyp (simEnv20 B) (scopeRel nt c₁ c₂ op c) (atNt "num_") c₂)
    (h₃ : HasTyp (simEnv20 B) (scopeRel nt c₁ c₂ op c) (atNt "relop_") op)
    (h₄ : HasTyp (simEnv20 B) (scopeRel nt c₁ c₂ op c) i32T c)
    (happ : Applies (simEnv20 B) "relop_" [.val nt, .val op, .val c₁, .val c₂] c) :
    FiresB (simEnv20 B) "Step_pure" 25
      (.tuple [.list [.case "CONST" (.tuple [nt, c₁]), .case "CONST" (.tuple [nt, c₂]),
        .case "RELOP" (.tuple [nt, op])], .list [.case "CONST" (.tuple [caseNilV "I32", c])]]) :=
  firesB20_of (hasRuleAt_relop B) _
    (QuantsOk.cons rfl h₀ (QuantsOk.cons rfl h₁ (QuantsOk.cons rfl h₂ (QuantsOk.cons rfl h₃
      (QuantsOk.cons rfl h₄ QuantsOk.nil)))))
    (evalExp_tup2 (evalExp_list3 (evalExp_pair rfl rfl) (evalExp_pair rfl rfl)
      (evalExp_pair rfl rfl))
      (evalExp_list1 (evalExp_case (evalExp_tup2 evalExp_caseNil (evalExp_var rfl)))))
    (prems_one (.ifPr (eqPrem_of_applies rfl (evalArgs_four rfl rfl rfl rfl) rfl happ)))

end Silmaril.Wasm.SpecTec.Sim20.Pure
