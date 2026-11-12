module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.NumAgree
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.PureCtrl
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureNumeric
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeLiveNum

/-!
# The numeric rules of 1.0 `Step_pure`, backwards

Rules 20–27 of 1.0's `Step_pure` (`unop-val`, `unop-trap`, `binop-val`, `binop-trap`, `testop`,
`relop`, `cvtop-val`, `cvtop-trap`) are 2.0's with 1.0's types: the number type is a `valtype`
variable `t` and the operands are `val_(t)` (2.0: `nt`, `num_(nt)`). They are transcribed here
(`unopValRule10` …) with their provenance in `simEnv10 B` by kernel `rfl`.

**Backwards**, under `NumAgree10 (simEnv10 B) (Profile.spec nd r)`, each firing at the image of V1
code is the image of a V1 `PureStep`:

* `unop-val`, `binop-val`, `testop`, `relop`, `cvtop-val` are V1's `intUnary`, `floatUnary`,
  `intBinary`, `floatBinary`, `intTest`, `intRel`, `floatRel` and `convert`. The shared `t` of a
  rule forces the operands and the operator to one number type, so ill-typed code never fires.
* `binop-trap` is V1's `intBinaryTrap`, and `cvtop-trap` its `convertTrap`: the dispatcher's list
  is empty exactly when V1 traps.
* `unop-trap` never fires, and `binop-trap` never fires at a float type: the integer `$unop_` has
  one result, and the profile always allows Core's own float result (`floatUnOpRel_self`,
  `floatBinOpRel_self`).

At the spec profile the profile's relations are V1's
(`floatUnOpP (Profile.spec nd r) = floatUnOpRel` by `rfl`, and likewise for binary operators
and conversions).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.V1.Execution (Admin PureStep value)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef evalArgs_three evalArgs_four)
open Silmaril.Wasm.SpecTec.Sim (Fires evalExp_case evalExp_tup2 evalExp_tup3 evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim20 (numTypeV)
open Silmaril.Wasm.SpecTec.Sim20.Pure (quant_val ifPrem fires_inv evalExp_pair evalExp_list2
  evalExp_list3 evalExp_caseNil memValue_list_iff applies_nil_of_eval applies_of_eqPrem)

variable {B : Builtins}

set_option maxRecDepth 100000

/-! ## The rules, transcribed -/

/-- `valtype`. -/
abbrev valtypeT10 : Typ := .varT "valtype" []

/-- `T(x)`. -/
abbrev atT (T x : IL.Id) : Typ := .varT T [.expA (.varE x)]

/-- `CONST x y`. -/
abbrev cE (x y : IL.Id) : Exp := .caseE "CONST" (.tupE [.varE x, .varE y])

/-- `OP x y`. -/
abbrev oE (o : MixopS) (x y : IL.Id) : Exp := .caseE o (.tupE [.varE x, .varE y])

/-- `$f(x₁, …)` on variables. -/
abbrev callV (f : IL.Id) (xs : List IL.Id) : Exp := .callE f (xs.map fun x => .expA (.varE x))

/-- `[TRAP]`. -/
abbrev trapE : Exp := .listE [.caseE "TRAP" (.tupE [])]

/-- `CONST I32 c`. -/
abbrev cI32E : Exp := .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "c"])

/-- `val_(I32)`. -/
abbrev valI32T10 : Typ := .varT "val_" [.expA (.caseE "I32" (.tupE []))]

def unopValRule10 : Rule :=
  .ruleD "unop-val" [.expP "t" valtypeT10, .expP "c_1" (atT "val_" "t"),
      .expP "unop" (atT "unop_" "t"), .expP "c" (atT "val_" "t")] "%~>%"
    (.tupE [.listE [cE "t" "c_1", oE "UNOP" "t" "unop"], .listE [cE "t" "c"]])
    [.ifPr (.memE (.varE "c") (callV "unop_" ["t", "unop", "c_1"]))]

def unopTrapRule10 : Rule :=
  .ruleD "unop-trap" [.expP "t" valtypeT10, .expP "c_1" (atT "val_" "t"),
      .expP "unop" (atT "unop_" "t")] "%~>%"
    (.tupE [.listE [cE "t" "c_1", oE "UNOP" "t" "unop"], trapE])
    [.ifPr (.cmpE .eqOp .boolT (callV "unop_" ["t", "unop", "c_1"]) (.listE []))]

def binopValRule10 : Rule :=
  .ruleD "binop-val" [.expP "t" valtypeT10, .expP "c_1" (atT "val_" "t"),
      .expP "c_2" (atT "val_" "t"), .expP "binop" (atT "binop_" "t"),
      .expP "c" (atT "val_" "t")] "%~>%"
    (.tupE [.listE [cE "t" "c_1", cE "t" "c_2", oE "BINOP" "t" "binop"], .listE [cE "t" "c"]])
    [.ifPr (.memE (.varE "c") (callV "binop_" ["t", "binop", "c_1", "c_2"]))]

def binopTrapRule10 : Rule :=
  .ruleD "binop-trap" [.expP "t" valtypeT10, .expP "c_1" (atT "val_" "t"),
      .expP "c_2" (atT "val_" "t"), .expP "binop" (atT "binop_" "t")] "%~>%"
    (.tupE [.listE [cE "t" "c_1", cE "t" "c_2", oE "BINOP" "t" "binop"], trapE])
    [.ifPr (.cmpE .eqOp .boolT (callV "binop_" ["t", "binop", "c_1", "c_2"]) (.listE []))]

def testopRule10 : Rule :=
  .ruleD "testop" [.expP "t" valtypeT10, .expP "c_1" (atT "val_" "t"),
      .expP "testop" (atT "testop_" "t"), .expP "c" valI32T10] "%~>%"
    (.tupE [.listE [cE "t" "c_1", oE "TESTOP" "t" "testop"], .listE [cI32E]])
    [.ifPr (.cmpE .eqOp .boolT (.varE "c") (callV "testop_" ["t", "testop", "c_1"]))]

def relopRule10 : Rule :=
  .ruleD "relop" [.expP "t" valtypeT10, .expP "c_1" (atT "val_" "t"),
      .expP "c_2" (atT "val_" "t"), .expP "relop" (atT "relop_" "t"), .expP "c" valI32T10] "%~>%"
    (.tupE [.listE [cE "t" "c_1", cE "t" "c_2", oE "RELOP" "t" "relop"], .listE [cI32E]])
    [.ifPr (.cmpE .eqOp .boolT (.varE "c") (callV "relop_" ["t", "relop", "c_1", "c_2"]))]

/-- `CVTOP t_2 t_1 cvtop`. -/
abbrev cvtE : Exp := .caseE "CVTOP" (.tupE [.varE "t_2", .varE "t_1", .varE "cvtop"])

def cvtopValRule10 : Rule :=
  .ruleD "cvtop-val" [.expP "t_1" valtypeT10, .expP "c_1" (atT "val_" "t_1"),
      .expP "t_2" valtypeT10, .expP "cvtop" (.varT "cvtop" []), .expP "c" (atT "val_" "t_2")]
    "%~>%" (.tupE [.listE [cE "t_1" "c_1", cvtE], .listE [cE "t_2" "c"]])
    [.ifPr (.memE (.varE "c") (callV "cvtop__" ["t_1", "t_2", "cvtop", "c_1"]))]

def cvtopTrapRule10 : Rule :=
  .ruleD "cvtop-trap" [.expP "t_1" valtypeT10, .expP "c_1" (atT "val_" "t_1"),
      .expP "t_2" valtypeT10, .expP "cvtop" (.varT "cvtop" [])] "%~>%"
    (.tupE [.listE [cE "t_1" "c_1", cvtE], trapE])
    [.ifPr (.cmpE .eqOp .boolT (callV "cvtop__" ["t_1", "t_2", "cvtop", "c_1"]) (.listE []))]

variable (B) in
theorem hasRuleAt10_unopVal : HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 20 unopValRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩
variable (B) in
theorem hasRuleAt10_unopTrap : HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 21 unopTrapRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩
variable (B) in
theorem hasRuleAt10_binopVal : HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 22 binopValRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩
variable (B) in
theorem hasRuleAt10_binopTrap : HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 23 binopTrapRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩
variable (B) in
theorem hasRuleAt10_testop : HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 24 testopRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩
variable (B) in
theorem hasRuleAt10_relop : HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 25 relopRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩
variable (B) in
theorem hasRuleAt10_cvtopVal : HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 26 cvtopValRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩
variable (B) in
theorem hasRuleAt10_cvtopTrap : HasRuleAt (simEnv10 B) "Step_pure" "%~>%" 27 cvtopTrapRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## The rules at IL values, inverted -/

/-- The premise `c <- $f(…)`, read as an application. -/
theorem mem_of_prem {env : Env} {ρ : VarEnv} {f : IL.Id} {args : List Arg} {ws : List ArgV}
    {c : Value} (hd : ρ.findDef? f = none) (ha : EvalArgs env ρ args ws)
    (fc : ρ.findVal? "c" = some c)
    (h : EvalExp env ρ (.memE (.varE "c") (.callE f args)) (.bool true)) :
    ∃ v, Applies env f ws v ∧ memValue c v = .ok (.bool true) := by
  obtain ⟨a, v, ha', hv, hm⟩ := evalExp_memE_iff.1 h
  have e : a = c := EvalExp.unique ha' (Sim.evalExp_var fc)
  subst e
  exact ⟨v, (applies_iff_callDef hd ha).2 (evalExp_callE_iff.1 hv), hm⟩

theorem unopVal10_inv {n₁ n₂ c₁ op w : Value}
    (hf : Fires (simEnv10 B) "Step_pure" 20
      (.tuple [.list [.case "CONST" (.tuple [n₁, c₁]), .case "UNOP" (.tuple [n₂, op])], w])) :
    n₂ = n₁ ∧ ∃ c v, w = .list [.case "CONST" (.tuple [n₁, c])] ∧
      Applies (simEnv10 B) "unop_" [.val n₁, .val op, .val c₁] v ∧
      memValue c v = .ok (.bool true) := by
  obtain ⟨σ, hq, he, hp⟩ := fires_inv (hasRuleAt10_unopVal B) hf
  obtain ⟨vt, ft⟩ := quant_val (x := "t") (t := valtypeT10) hq (by simp)
  obtain ⟨v₁, f₁⟩ := quant_val (x := "c_1") (t := atT "val_" "t") hq (by simp)
  obtain ⟨vo, fo⟩ := quant_val (x := "unop") (t := atT "unop_" "t") hq (by simp)
  obtain ⟨vc, fc⟩ := quant_val (x := "c") (t := atT "val_" "t") hq (by simp)
  have hu := EvalExp.unique he (evalExp_tup2 (evalExp_list2 (evalExp_pair ft f₁)
    (evalExp_pair ft fo)) (evalExp_list1 (evalExp_pair ft fc)))
  simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true] at hu
  obtain ⟨⟨⟨rfl, rfl⟩, rfl, rfl⟩, rfl⟩ := hu
  obtain ⟨v, hv, hm⟩ := mem_of_prem rfl (evalArgs_three ft fo f₁) fc
    (ifPrem (hp _ (List.mem_singleton_self _)))
  exact ⟨rfl, vc, v, rfl, hv, hm⟩

theorem unopTrap10_inv {n₁ n₂ c₁ op w : Value}
    (hf : Fires (simEnv10 B) "Step_pure" 21
      (.tuple [.list [.case "CONST" (.tuple [n₁, c₁]), .case "UNOP" (.tuple [n₂, op])], w])) :
    n₂ = n₁ ∧ Applies (simEnv10 B) "unop_" [.val n₁, .val op, .val c₁] (.list []) := by
  obtain ⟨σ, hq, he, hp⟩ := fires_inv (hasRuleAt10_unopTrap B) hf
  obtain ⟨vt, ft⟩ := quant_val (x := "t") (t := valtypeT10) hq (by simp)
  obtain ⟨v₁, f₁⟩ := quant_val (x := "c_1") (t := atT "val_" "t") hq (by simp)
  obtain ⟨vo, fo⟩ := quant_val (x := "unop") (t := atT "unop_" "t") hq (by simp)
  have hu := EvalExp.unique he (evalExp_tup2 (evalExp_list2 (evalExp_pair ft f₁)
    (evalExp_pair ft fo)) (evalExp_list1 evalExp_caseNil))
  simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true] at hu
  obtain ⟨⟨⟨rfl, rfl⟩, rfl, rfl⟩, -⟩ := hu
  exact ⟨rfl, applies_nil_of_eval rfl (evalArgs_three ft fo f₁)
    (ifPrem (hp _ (List.mem_singleton_self _)))⟩

/-- The left-hand side of the two-operand rules. -/
abbrev lhs3V (o : MixopS) (n₁ n₂ n₃ c₁ c₂ op : Value) : Value :=
  .list [.case "CONST" (.tuple [n₁, c₁]), .case "CONST" (.tuple [n₂, c₂]),
    .case o (.tuple [n₃, op])]

theorem binopVal10_inv {n₁ n₂ n₃ c₁ c₂ op w : Value}
    (hf : Fires (simEnv10 B) "Step_pure" 22 (.tuple [lhs3V "BINOP" n₁ n₂ n₃ c₁ c₂ op, w])) :
    n₂ = n₁ ∧ n₃ = n₁ ∧ ∃ c v, w = .list [.case "CONST" (.tuple [n₁, c])] ∧
      Applies (simEnv10 B) "binop_" [.val n₁, .val op, .val c₁, .val c₂] v ∧
      memValue c v = .ok (.bool true) := by
  obtain ⟨σ, hq, he, hp⟩ := fires_inv (hasRuleAt10_binopVal B) hf
  obtain ⟨vt, ft⟩ := quant_val (x := "t") (t := valtypeT10) hq (by simp)
  obtain ⟨v₁, f₁⟩ := quant_val (x := "c_1") (t := atT "val_" "t") hq (by simp)
  obtain ⟨v₂, f₂⟩ := quant_val (x := "c_2") (t := atT "val_" "t") hq (by simp)
  obtain ⟨vo, fo⟩ := quant_val (x := "binop") (t := atT "binop_" "t") hq (by simp)
  obtain ⟨vc, fc⟩ := quant_val (x := "c") (t := atT "val_" "t") hq (by simp)
  have hu := EvalExp.unique he (evalExp_tup2 (evalExp_list3 (evalExp_pair ft f₁)
    (evalExp_pair ft f₂) (evalExp_pair ft fo)) (evalExp_list1 (evalExp_pair ft fc)))
  simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true] at hu
  obtain ⟨⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl⟩, rfl⟩ := hu
  obtain ⟨v, hv, hm⟩ := mem_of_prem rfl (evalArgs_four ft fo f₁ f₂) fc
    (ifPrem (hp _ (List.mem_singleton_self _)))
  exact ⟨rfl, rfl, vc, v, rfl, hv, hm⟩

theorem binopTrap10_inv {n₁ n₂ n₃ c₁ c₂ op w : Value}
    (hf : Fires (simEnv10 B) "Step_pure" 23 (.tuple [lhs3V "BINOP" n₁ n₂ n₃ c₁ c₂ op, w])) :
    n₂ = n₁ ∧ n₃ = n₁ ∧ w = .list [caseNilV "TRAP"] ∧
      Applies (simEnv10 B) "binop_" [.val n₁, .val op, .val c₁, .val c₂] (.list []) := by
  obtain ⟨σ, hq, he, hp⟩ := fires_inv (hasRuleAt10_binopTrap B) hf
  obtain ⟨vt, ft⟩ := quant_val (x := "t") (t := valtypeT10) hq (by simp)
  obtain ⟨v₁, f₁⟩ := quant_val (x := "c_1") (t := atT "val_" "t") hq (by simp)
  obtain ⟨v₂, f₂⟩ := quant_val (x := "c_2") (t := atT "val_" "t") hq (by simp)
  obtain ⟨vo, fo⟩ := quant_val (x := "binop") (t := atT "binop_" "t") hq (by simp)
  have hu := EvalExp.unique he (evalExp_tup2 (evalExp_list3 (evalExp_pair ft f₁)
    (evalExp_pair ft f₂) (evalExp_pair ft fo)) (evalExp_list1 evalExp_caseNil))
  simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true] at hu
  obtain ⟨⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl⟩, rfl⟩ := hu
  exact ⟨rfl, rfl, rfl, applies_nil_of_eval rfl (evalArgs_four ft fo f₁ f₂)
    (ifPrem (hp _ (List.mem_singleton_self _)))⟩

theorem testop10_inv {n₁ n₂ c₁ op w : Value}
    (hf : Fires (simEnv10 B) "Step_pure" 24
      (.tuple [.list [.case "CONST" (.tuple [n₁, c₁]), .case "TESTOP" (.tuple [n₂, op])], w])) :
    n₂ = n₁ ∧ ∃ c, w = .list [.case "CONST" (.tuple [caseNilV "I32", c])] ∧
      Applies (simEnv10 B) "testop_" [.val n₁, .val op, .val c₁] c := by
  obtain ⟨σ, hq, he, hp⟩ := fires_inv (hasRuleAt10_testop B) hf
  obtain ⟨vt, ft⟩ := quant_val (x := "t") (t := valtypeT10) hq (by simp)
  obtain ⟨v₁, f₁⟩ := quant_val (x := "c_1") (t := atT "val_" "t") hq (by simp)
  obtain ⟨vo, fo⟩ := quant_val (x := "testop") (t := atT "testop_" "t") hq (by simp)
  obtain ⟨vc, fc⟩ := quant_val (x := "c") (t := valI32T10) hq (by simp)
  have hu := EvalExp.unique he (evalExp_tup2 (evalExp_list2 (evalExp_pair ft f₁)
    (evalExp_pair ft fo)) (evalExp_list1 (evalExp_case (evalExp_tup2 evalExp_caseNil
      (Sim.evalExp_var fc)))))
  simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true] at hu
  obtain ⟨⟨⟨rfl, rfl⟩, rfl, rfl⟩, rfl⟩ := hu
  exact ⟨rfl, vc, rfl, applies_of_eqPrem rfl (evalArgs_three ft fo f₁) fc
    (ifPrem (hp _ (List.mem_singleton_self _)))⟩

theorem relop10_inv {n₁ n₂ n₃ c₁ c₂ op w : Value}
    (hf : Fires (simEnv10 B) "Step_pure" 25 (.tuple [lhs3V "RELOP" n₁ n₂ n₃ c₁ c₂ op, w])) :
    n₂ = n₁ ∧ n₃ = n₁ ∧ ∃ c, w = .list [.case "CONST" (.tuple [caseNilV "I32", c])] ∧
      Applies (simEnv10 B) "relop_" [.val n₁, .val op, .val c₁, .val c₂] c := by
  obtain ⟨σ, hq, he, hp⟩ := fires_inv (hasRuleAt10_relop B) hf
  obtain ⟨vt, ft⟩ := quant_val (x := "t") (t := valtypeT10) hq (by simp)
  obtain ⟨v₁, f₁⟩ := quant_val (x := "c_1") (t := atT "val_" "t") hq (by simp)
  obtain ⟨v₂, f₂⟩ := quant_val (x := "c_2") (t := atT "val_" "t") hq (by simp)
  obtain ⟨vo, fo⟩ := quant_val (x := "relop") (t := atT "relop_" "t") hq (by simp)
  obtain ⟨vc, fc⟩ := quant_val (x := "c") (t := valI32T10) hq (by simp)
  have hu := EvalExp.unique he (evalExp_tup2 (evalExp_list3 (evalExp_pair ft f₁)
    (evalExp_pair ft f₂) (evalExp_pair ft fo)) (evalExp_list1 (evalExp_case
      (evalExp_tup2 evalExp_caseNil (Sim.evalExp_var fc)))))
  simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true] at hu
  obtain ⟨⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl⟩, rfl⟩ := hu
  exact ⟨rfl, rfl, vc, rfl, applies_of_eqPrem rfl (evalArgs_four ft fo f₁ f₂) fc
    (ifPrem (hp _ (List.mem_singleton_self _)))⟩

/-- The left-hand side of the conversion rules. -/
abbrev lhsCvtV (n₁ c₁ m₂ m₁ op : Value) : Value :=
  .list [.case "CONST" (.tuple [n₁, c₁]), .case "CVTOP" (.tuple [m₂, m₁, op])]

theorem cvtopVal10_inv {n₁ c₁ m₂ m₁ op w : Value}
    (hf : Fires (simEnv10 B) "Step_pure" 26 (.tuple [lhsCvtV n₁ c₁ m₂ m₁ op, w])) :
    m₁ = n₁ ∧ ∃ c v, w = .list [.case "CONST" (.tuple [m₂, c])] ∧
      Applies (simEnv10 B) "cvtop__" [.val n₁, .val m₂, .val op, .val c₁] v ∧
      memValue c v = .ok (.bool true) := by
  obtain ⟨σ, hq, he, hp⟩ := fires_inv (hasRuleAt10_cvtopVal B) hf
  obtain ⟨vt₁, ft₁⟩ := quant_val (x := "t_1") (t := valtypeT10) hq (by simp)
  obtain ⟨v₁, f₁⟩ := quant_val (x := "c_1") (t := atT "val_" "t_1") hq (by simp)
  obtain ⟨vt₂, ft₂⟩ := quant_val (x := "t_2") (t := valtypeT10) hq (by simp)
  obtain ⟨vo, fo⟩ := quant_val (x := "cvtop") (t := .varT "cvtop" []) hq (by simp)
  obtain ⟨vc, fc⟩ := quant_val (x := "c") (t := atT "val_" "t_2") hq (by simp)
  have hu := EvalExp.unique he (evalExp_tup2 (evalExp_list2 (evalExp_pair ft₁ f₁)
    (evalExp_case (evalExp_tup3 (Sim.evalExp_var ft₂) (Sim.evalExp_var ft₁) (Sim.evalExp_var fo))))
    (evalExp_list1 (evalExp_pair ft₂ fc)))
  simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true] at hu
  obtain ⟨⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩, rfl⟩ := hu
  obtain ⟨v, hv, hm⟩ := mem_of_prem rfl (evalArgs_four ft₁ ft₂ fo f₁) fc
    (ifPrem (hp _ (List.mem_singleton_self _)))
  exact ⟨rfl, vc, v, rfl, hv, hm⟩

theorem cvtopTrap10_inv {n₁ c₁ m₂ m₁ op w : Value}
    (hf : Fires (simEnv10 B) "Step_pure" 27 (.tuple [lhsCvtV n₁ c₁ m₂ m₁ op, w])) :
    m₁ = n₁ ∧ w = .list [caseNilV "TRAP"] ∧
      Applies (simEnv10 B) "cvtop__" [.val n₁, .val m₂, .val op, .val c₁] (.list []) := by
  obtain ⟨σ, hq, he, hp⟩ := fires_inv (hasRuleAt10_cvtopTrap B) hf
  obtain ⟨vt₁, ft₁⟩ := quant_val (x := "t_1") (t := valtypeT10) hq (by simp)
  obtain ⟨v₁, f₁⟩ := quant_val (x := "c_1") (t := atT "val_" "t_1") hq (by simp)
  obtain ⟨vt₂, ft₂⟩ := quant_val (x := "t_2") (t := valtypeT10) hq (by simp)
  obtain ⟨vo, fo⟩ := quant_val (x := "cvtop") (t := .varT "cvtop" []) hq (by simp)
  have hu := EvalExp.unique he (evalExp_tup2 (evalExp_list2 (evalExp_pair ft₁ f₁)
    (evalExp_case (evalExp_tup3 (Sim.evalExp_var ft₂) (Sim.evalExp_var ft₁) (Sim.evalExp_var fo))))
    (evalExp_list1 evalExp_caseNil))
  simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true] at hu
  obtain ⟨⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩, rfl⟩ := hu
  exact ⟨rfl, rfl, applies_nil_of_eval rfl (evalArgs_four ft₁ ft₂ fo f₁)
    (ifPrem (hp _ (List.mem_singleton_self _)))⟩

end Silmaril.Wasm.SpecTec.Sim10.Whole
