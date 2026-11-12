module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureNumericV2

/-!
# `unop-trap`, `cvtop-val` and `cvtop-trap` of wasm-2.0 `Step_pure`

The three numeric rules pass 2 left open, in the two layers of `PureNumeric`:

* **IL level, unconditional**, for arbitrary IL values: `unopTrap_inv`/`_fires` (rule 21),
  `cvtopVal_inv`/`_fires` (26), `cvtopTrap_inv`/`_fires` (27).
* **V2 level.** `unop-trap` under the existing `NumAgree`/`NumTyped`: `intUnOpTrap_iff` and
  `floatUnOpTrap_iff`, both of whose right-hand sides are `False` (V2's integer `$unop_` is a
  singleton, its float result set is nonempty), so `unop-trap` never fires at a V2 image
  (`intUnOpTrap_never`, `floatUnOpTrap_never`). `cvtop-val`/`-trap` under a new hypothesis
  `CvtAgree` of the same kind as `NumAgree` (the script's `$cvtop__` returns exactly V2's
  conversion results, and is empty exactly when V2 traps), stated for the operand/operator
  combinations validation admits (`CvtOp.toShared` defined): `cvtOp_iff`, `cvtOpTrap_iff`.
  `CvtAgree` is **assumed**, like `NumAgree`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Pure

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef evalArgs_three)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk TypedV ValsOnly evalExp_tup2 evalExp_tup3 evalExp_list1
  evalExp_case)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (FiresB ruleConcl)

variable (B : Builtins)

/-! ## `unop-trap` (21), IL level -/

/-- The left-hand side of the `unop` rules, evaluated. -/
theorem eval_unopLhs {env : Env} {ρ : VarEnv} {nt c₁ op : Value}
    (fnt : ρ.findVal? "nt" = some nt) (f₁ : ρ.findVal? "c_1" = some c₁)
    (fop : ρ.findVal? "unop" = some op) :
    EvalExp env ρ (.listE [.caseE "CONST" (.tupE [.varE "nt", .varE "c_1"]),
        .caseE "UNOP" (.tupE [.varE "nt", .varE "unop"])])
      (.list [.case "CONST" (.tuple [nt, c₁]), .case "UNOP" (.tuple [nt, op])]) :=
  evalExp_list2 (evalExp_pair fnt f₁) (evalExp_pair fnt fop)

/-- `unop-trap`, read back, for arbitrary IL values. -/
theorem unopTrap_inv {nt c₁ op w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 21
      (.tuple [.list [.case "CONST" (.tuple [nt, c₁]), .case "UNOP" (.tuple [nt, op])], w])) :
    w = .list [caseNilV "TRAP"] ∧
      Applies (simEnv20 B) "unop_" [.val nt, .val op, .val c₁] (.list []) := by
  obtain ⟨σ, hq, he, hp⟩ := firesB20_inv (hasRuleAt_unopTrap B) hf
  obtain ⟨vnt, fnt⟩ := quant_val (x := "nt") (t := numtypeT) hq (by simp)
  obtain ⟨v₁, f₁⟩ := quant_val (x := "c_1") (t := atNt "num_") hq (by simp)
  obtain ⟨vop, fop⟩ := quant_val (x := "unop") (t := atNt "unop_") hq (by simp)
  have hu := EvalExp.unique he (evalExp_tup2 (eval_unopLhs fnt f₁ fop)
    (evalExp_list1 evalExp_caseNil))
  simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true] at hu
  obtain ⟨⟨⟨rfl, rfl⟩, -, rfl⟩, rfl⟩ := hu
  exact ⟨rfl, applies_nil_of_eval rfl (evalArgs_three fnt fop f₁)
    (ifPrem (hp _ (List.mem_singleton_self _)))⟩

/-- The scope of `unop-trap`. -/
def scopeUnT (nt c₁ op : Value) : VarEnv :=
  VarEnv.empty.bindVals [("nt", nt), ("c_1", c₁), ("unop", op)]

/-- `unop-trap`, fired, for arbitrary IL values. -/
theorem unopTrap_fires {nt c₁ op : Value}
    (h₀ : HasTyp (simEnv20 B) (scopeUnT nt c₁ op) numtypeT nt)
    (h₁ : HasTyp (simEnv20 B) (scopeUnT nt c₁ op) (atNt "num_") c₁)
    (h₂ : HasTyp (simEnv20 B) (scopeUnT nt c₁ op) (atNt "unop_") op)
    (happ : Applies (simEnv20 B) "unop_" [.val nt, .val op, .val c₁] (.list [])) :
    FiresB (simEnv20 B) "Step_pure" 21
      (.tuple [.list [.case "CONST" (.tuple [nt, c₁]), .case "UNOP" (.tuple [nt, op])],
        .list [caseNilV "TRAP"]]) := by
  have hcall : EvalExp (simEnv20 B) (scopeUnT nt c₁ op)
      (.callE "unop_" [.expA (.varE "nt"), .expA (.varE "unop"), .expA (.varE "c_1")]) (.list []) :=
    evalExp_callE_iff.2 ((applies_iff_callDef rfl (evalArgs_three rfl rfl rfl)).1 happ)
  have hif : EvalExp (simEnv20 B) (scopeUnT nt c₁ op)
      (.cmpE .eqOp .boolT (.callE "unop_" [.expA (.varE "nt"), .expA (.varE "unop"),
        .expA (.varE "c_1")]) (.listE [])) (.bool true) :=
    evalExp_cmpE_iff.2 ⟨_, _, hcall, evalExp_list0, by simp [cmpValues]⟩
  exact firesB20_of (hasRuleAt_unopTrap B) _
    (QuantsOk.cons rfl h₀ (QuantsOk.cons rfl h₁ (QuantsOk.cons rfl h₂ QuantsOk.nil)))
    (evalExp_tup2 (eval_unopLhs rfl rfl rfl) (evalExp_list1 evalExp_caseNil))
    (prems_one (.ifPr hif))

/-! ## `unop-trap`, V2 level -/

variable {P : Profile}

/-- **`Step_pure/unop-trap` is `PureStep.intUnOpTrap`**: both sides are `False`. -/
theorem intUnOpTrap_iff (A : NumAgree (simEnv20 B) P) (T : NumTyped (simEnv20 B)) {t : IntType}
    {op : IntUnOp} {x : BitVec t.width} (hop : op.valid t) {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 21
        (.tuple [.list (adminsToV [.plain (.intConst t x), .plain (.intUnOp t op)]), w]) ↔
      (∀ z, ¬ IntUnOpResult t op x z) ∧ w = .list (adminsToV [.trap]) := by
  obtain ⟨vs, happ, hvs⟩ := A.intUnOp t op x hop
  have hnil : vs = [] ↔ ∀ z, ¬ IntUnOpResult t op x z := by
    rw [List.eq_nil_iff_forall_not_mem]
    exact ⟨fun h z hz => h _ ((hvs _).2 ⟨z, hz, rfl⟩), fun h c hc =>
      let ⟨z, hz, _⟩ := (hvs c).1 hc; h z hz⟩
  constructor
  · intro hf
    obtain ⟨rfl, happ'⟩ := unopTrap_inv B hf
    have hv : Value.list [] = .list vs := Applies.unique happ' happ
    exact ⟨hnil.1 (by simpa using hv.symm), rfl⟩
  · rintro ⟨htr, rfl⟩
    exact unopTrap_fires B (T.numtype _ _ ⟨rfl, rfl, rfl⟩) (T.num (.int t) x "nt" _ ⟨rfl, rfl, rfl⟩ rfl)
      (T.intUnOp t op hop _ ⟨rfl, rfl, rfl⟩ rfl) (hnil.2 htr ▸ happ)

/-- **`unop-trap` never fires at an integer V2 image**: `$unop_(Inn, …)` is a singleton. -/
theorem intUnOpTrap_never (A : NumAgree (simEnv20 B) P) (T : NumTyped (simEnv20 B))
    {t : IntType} {op : IntUnOp} {x : BitVec t.width} (hop : op.valid t) {w : Value} :
    ¬ FiresB (simEnv20 B) "Step_pure" 21
      (.tuple [.list (adminsToV [.plain (.intConst t x), .plain (.intUnOp t op)]), w]) :=
  fun hf =>
    let ⟨z, hz⟩ := IntUnOpResult_nonempty t op x
    ((intUnOpTrap_iff B A T hop).1 hf).1 z hz

/-- **`Step_pure/unop-trap` is `PureStep.floatUnOpTrap`**: both sides are `False`. -/
theorem floatUnOpTrap_iff (A : NumAgree (simEnv20 B) P) (T : NumTyped (simEnv20 B))
    {t : FloatType} {op : FloatUnOp} {x : BitVec t.width} {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 21
        (.tuple [.list (adminsToV [.plain (.floatConst t x), .plain (.floatUnOp t op)]), w]) ↔
      (∀ z, ¬ FloatUnOpResult P t op x z) ∧ w = .list (adminsToV [.trap]) := by
  obtain ⟨vs, happ, hvs⟩ := A.floatUnOp t op x
  have hnil : vs = [] ↔ ∀ z, ¬ FloatUnOpResult P t op x z := by
    rw [List.eq_nil_iff_forall_not_mem]
    exact ⟨fun h z hz => h _ ((hvs _).2 ⟨z, hz, rfl⟩), fun h c hc =>
      let ⟨z, hz, _⟩ := (hvs c).1 hc; h z hz⟩
  constructor
  · intro hf
    obtain ⟨rfl, happ'⟩ := unopTrap_inv B hf
    have hv : Value.list [] = .list vs := Applies.unique happ' happ
    exact ⟨hnil.1 (by simpa using hv.symm), rfl⟩
  · rintro ⟨htr, rfl⟩
    exact unopTrap_fires B (T.numtype _ _ ⟨rfl, rfl, rfl⟩)
      (T.num (.float t) x "nt" _ ⟨rfl, rfl, rfl⟩ rfl) (T.floatUnOp t op _ ⟨rfl, rfl, rfl⟩ rfl)
      (hnil.2 htr ▸ happ)

/-- **`unop-trap` never fires at a float V2 image**: the result set is nonempty. -/
theorem floatUnOpTrap_never (A : NumAgree (simEnv20 B) P) (T : NumTyped (simEnv20 B))
    {t : FloatType} {op : FloatUnOp} {x : BitVec t.width} {w : Value} :
    ¬ FiresB (simEnv20 B) "Step_pure" 21
      (.tuple [.list (adminsToV [.plain (.floatConst t x), .plain (.floatUnOp t op)]), w]) :=
  fun hf =>
    let ⟨z, hz⟩ := FloatUnOpResult_nonempty P t op x
    ((floatUnOpTrap_iff B A T).1 hf).1 z hz

/-! ## `cvtop-val` (26) and `cvtop-trap` (27), IL level -/

/-- The left-hand side of the `cvtop` rules, evaluated. -/
theorem eval_cvtopLhs {env : Env} {ρ : VarEnv} {nt₁ c₁ nt₂ op : Value}
    (f₁ : ρ.findVal? "nt_1" = some nt₁) (fc : ρ.findVal? "c_1" = some c₁)
    (f₂ : ρ.findVal? "nt_2" = some nt₂) (fop : ρ.findVal? "cvtop" = some op) :
    EvalExp env ρ (.listE [.caseE "CONST" (.tupE [.varE "nt_1", .varE "c_1"]),
        .caseE "CVTOP" (.tupE [.varE "nt_2", .varE "nt_1", .varE "cvtop"])])
      (.list [.case "CONST" (.tuple [nt₁, c₁]), .case "CVTOP" (.tuple [nt₂, nt₁, op])]) :=
  evalExp_list2 (evalExp_pair f₁ fc)
    (evalExp_case (evalExp_tup3 (evalExp_var f₂) (evalExp_var f₁) (evalExp_var fop)))

/-- The four arguments of `$cvtop__(nt_1, nt_2, cvtop, c_1)`. -/
theorem evalArgs_cvtop {env : Env} {ρ : VarEnv} {nt₁ c₁ nt₂ op : Value}
    (f₁ : ρ.findVal? "nt_1" = some nt₁) (fc : ρ.findVal? "c_1" = some c₁)
    (f₂ : ρ.findVal? "nt_2" = some nt₂) (fop : ρ.findVal? "cvtop" = some op) :
    EvalArgs env ρ [.expA (.varE "nt_1"), .expA (.varE "nt_2"), .expA (.varE "cvtop"),
      .expA (.varE "c_1")] [.val nt₁, .val nt₂, .val op, .val c₁] :=
  Silmaril.SpecTec.Equiv.ExecNumeric.evalArgs_four f₁ f₂ fop fc

/-- `cvtop-val`, read back, for arbitrary IL values. -/
theorem cvtopVal_inv {nt₁ c₁ nt₂ op w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 26
      (.tuple [.list [.case "CONST" (.tuple [nt₁, c₁]), .case "CVTOP" (.tuple [nt₂, nt₁, op])],
        w])) :
    ∃ c v, w = .list [.case "CONST" (.tuple [nt₂, c])] ∧
      Applies (simEnv20 B) "cvtop__" [.val nt₁, .val nt₂, .val op, .val c₁] v ∧
      memValue c v = .ok (.bool true) := by
  obtain ⟨σ, hq, he, hp⟩ := firesB20_inv (hasRuleAt_cvtopVal B) hf
  obtain ⟨v₁, f₁⟩ := quant_val (x := "nt_1") (t := numtypeT) hq (by simp)
  obtain ⟨vc₁, fc₁⟩ := quant_val (x := "c_1") (t := .varT "num_" [.expA (.varE "nt_1")]) hq
    (by simp)
  obtain ⟨v₂, f₂⟩ := quant_val (x := "nt_2") (t := numtypeT) hq (by simp)
  obtain ⟨vop, fop⟩ := quant_val (x := "cvtop") (t := .varT "cvtop" []) hq (by simp)
  obtain ⟨vc, fc⟩ := quant_val (x := "c") (t := .varT "num_" [.expA (.varE "nt_2")]) hq
    (by simp)
  have hu := EvalExp.unique he (evalExp_tup2 (eval_cvtopLhs f₁ fc₁ f₂ fop)
    (evalExp_list1 (evalExp_pair f₂ fc)))
  simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true] at hu
  obtain ⟨⟨⟨rfl, rfl⟩, rfl, -, rfl⟩, rfl⟩ := hu
  obtain ⟨a, v, ha, hv, hm⟩ := evalExp_memE_iff.1 (ifPrem (hp _ (List.mem_singleton_self _)))
  have hac : a = vc := EvalExp.unique ha (evalExp_var fc)
  subst hac
  exact ⟨a, v, rfl, (applies_iff_callDef rfl (evalArgs_cvtop f₁ fc₁ f₂ fop)).2
    (evalExp_callE_iff.1 hv), hm⟩

/-- The scope of `cvtop-val`. -/
def scopeCvt (nt₁ c₁ nt₂ op c : Value) : VarEnv :=
  VarEnv.empty.bindVals [("nt_1", nt₁), ("c_1", c₁), ("nt_2", nt₂), ("cvtop", op), ("c", c)]

/-- `cvtop-val`, fired, for arbitrary IL values. -/
theorem cvtopVal_fires {nt₁ c₁ nt₂ op c v : Value}
    (h₀ : HasTyp (simEnv20 B) (scopeCvt nt₁ c₁ nt₂ op c) numtypeT nt₁)
    (h₁ : HasTyp (simEnv20 B) (scopeCvt nt₁ c₁ nt₂ op c) (.varT "num_" [.expA (.varE "nt_1")]) c₁)
    (h₂ : HasTyp (simEnv20 B) (scopeCvt nt₁ c₁ nt₂ op c) numtypeT nt₂)
    (h₃ : HasTyp (simEnv20 B) (scopeCvt nt₁ c₁ nt₂ op c) (.varT "cvtop" []) op)
    (h₄ : HasTyp (simEnv20 B) (scopeCvt nt₁ c₁ nt₂ op c) (.varT "num_" [.expA (.varE "nt_2")]) c)
    (happ : Applies (simEnv20 B) "cvtop__" [.val nt₁, .val nt₂, .val op, .val c₁] v)
    (hm : memValue c v = .ok (.bool true)) :
    FiresB (simEnv20 B) "Step_pure" 26
      (.tuple [.list [.case "CONST" (.tuple [nt₁, c₁]), .case "CVTOP" (.tuple [nt₂, nt₁, op])],
        .list [.case "CONST" (.tuple [nt₂, c])]]) := by
  have hcall : EvalExp (simEnv20 B) (scopeCvt nt₁ c₁ nt₂ op c)
      (.callE "cvtop__" [.expA (.varE "nt_1"), .expA (.varE "nt_2"), .expA (.varE "cvtop"),
        .expA (.varE "c_1")]) v :=
    evalExp_callE_iff.2 ((applies_iff_callDef rfl (evalArgs_cvtop rfl rfl rfl rfl)).1 happ)
  exact firesB20_of (hasRuleAt_cvtopVal B) _
    (QuantsOk.cons rfl h₀ (QuantsOk.cons rfl h₁ (QuantsOk.cons rfl h₂ (QuantsOk.cons rfl h₃
      (QuantsOk.cons rfl h₄ QuantsOk.nil)))))
    (evalExp_tup2 (eval_cvtopLhs rfl rfl rfl rfl) (evalExp_list1 (evalExp_pair rfl rfl)))
    (prems_one (.ifPr (evalExp_memE_iff.2 ⟨c, v, evalExp_var rfl, hcall, hm⟩)))

/-- `cvtop-trap`, read back, for arbitrary IL values. -/
theorem cvtopTrap_inv {nt₁ c₁ nt₂ op w : Value}
    (hf : FiresB (simEnv20 B) "Step_pure" 27
      (.tuple [.list [.case "CONST" (.tuple [nt₁, c₁]), .case "CVTOP" (.tuple [nt₂, nt₁, op])],
        w])) :
    w = .list [caseNilV "TRAP"] ∧
      Applies (simEnv20 B) "cvtop__" [.val nt₁, .val nt₂, .val op, .val c₁] (.list []) := by
  obtain ⟨σ, hq, he, hp⟩ := firesB20_inv (hasRuleAt_cvtopTrap B) hf
  obtain ⟨v₁, f₁⟩ := quant_val (x := "nt_1") (t := numtypeT) hq (by simp)
  obtain ⟨vc₁, fc₁⟩ := quant_val (x := "c_1") (t := .varT "num_" [.expA (.varE "nt_1")]) hq
    (by simp)
  obtain ⟨v₂, f₂⟩ := quant_val (x := "nt_2") (t := numtypeT) hq (by simp)
  obtain ⟨vop, fop⟩ := quant_val (x := "cvtop") (t := .varT "cvtop" []) hq (by simp)
  have hu := EvalExp.unique he (evalExp_tup2 (eval_cvtopLhs f₁ fc₁ f₂ fop)
    (evalExp_list1 evalExp_caseNil))
  simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true] at hu
  obtain ⟨⟨⟨rfl, rfl⟩, rfl, -, rfl⟩, rfl⟩ := hu
  exact ⟨rfl, applies_nil_of_eval rfl (evalArgs_cvtop f₁ fc₁ f₂ fop)
    (ifPrem (hp _ (List.mem_singleton_self _)))⟩

/-- The scope of `cvtop-trap`. -/
def scopeCvtT (nt₁ c₁ nt₂ op : Value) : VarEnv :=
  VarEnv.empty.bindVals [("nt_1", nt₁), ("c_1", c₁), ("nt_2", nt₂), ("cvtop", op)]

/-- `cvtop-trap`, fired, for arbitrary IL values. -/
theorem cvtopTrap_fires {nt₁ c₁ nt₂ op : Value}
    (h₀ : HasTyp (simEnv20 B) (scopeCvtT nt₁ c₁ nt₂ op) numtypeT nt₁)
    (h₁ : HasTyp (simEnv20 B) (scopeCvtT nt₁ c₁ nt₂ op) (.varT "num_" [.expA (.varE "nt_1")]) c₁)
    (h₂ : HasTyp (simEnv20 B) (scopeCvtT nt₁ c₁ nt₂ op) numtypeT nt₂)
    (h₃ : HasTyp (simEnv20 B) (scopeCvtT nt₁ c₁ nt₂ op) (.varT "cvtop" []) op)
    (happ : Applies (simEnv20 B) "cvtop__" [.val nt₁, .val nt₂, .val op, .val c₁] (.list [])) :
    FiresB (simEnv20 B) "Step_pure" 27
      (.tuple [.list [.case "CONST" (.tuple [nt₁, c₁]), .case "CVTOP" (.tuple [nt₂, nt₁, op])],
        .list [caseNilV "TRAP"]]) := by
  have hcall : EvalExp (simEnv20 B) (scopeCvtT nt₁ c₁ nt₂ op)
      (.callE "cvtop__" [.expA (.varE "nt_1"), .expA (.varE "nt_2"), .expA (.varE "cvtop"),
        .expA (.varE "c_1")]) (.list []) :=
    evalExp_callE_iff.2 ((applies_iff_callDef rfl (evalArgs_cvtop rfl rfl rfl rfl)).1 happ)
  have hif : EvalExp (simEnv20 B) (scopeCvtT nt₁ c₁ nt₂ op)
      (.cmpE .eqOp .boolT (.callE "cvtop__" [.expA (.varE "nt_1"), .expA (.varE "nt_2"),
        .expA (.varE "cvtop"), .expA (.varE "c_1")]) (.listE [])) (.bool true) :=
    evalExp_cmpE_iff.2 ⟨_, _, hcall, evalExp_list0, by simp [cmpValues]⟩
  exact firesB20_of (hasRuleAt_cvtopTrap B) _
    (QuantsOk.cons rfl h₀ (QuantsOk.cons rfl h₁ (QuantsOk.cons rfl h₂ (QuantsOk.cons rfl h₃
      QuantsOk.nil))))
    (evalExp_tup2 (eval_cvtopLhs rfl rfl rfl rfl) (evalExp_list1 evalExp_caseNil))
    (prems_one (.ifPr hif))

/-! ## `cvtop`, V2 level -/

/-- **The conversion agreement hypothesis** at a profile `P`: at every operand/operator
combination validation admits (`CvtOp.toShared` defined), the script's `$cvtop__`
returns exactly V2's conversion results, and is empty exactly when V2 traps. Like `NumAgree`, a
statement about the wasm-2.0 script's `3-numerics` and the builtins; **assumed**, not proved. -/
structure CvtAgree (env : Env) (P : Profile) : Prop where
  /-- `$cvtop__(nt_1, nt_2, cvtop, c_1)`. -/
  cvt : ∀ (target source : NumType) (op : V2.CvtOp) (x : BitVec source.width),
    (V2.CvtOp.toShared target source op).isSome →
    ∃ vs, Applies env "cvtop__" [.val (numTypeV source), .val (numTypeV target), .val (cvtOpV op),
      .val (numV ⟨source, x⟩)] (.list vs) ∧
      (∀ c, c ∈ vs ↔ ∃ z, CvtOpResult P target source op x z ∧ c = numV ⟨target, z⟩) ∧
      (vs = [] ↔ CvtOpTraps P target source op x)

/-- **The conversion operator typing hypothesis**: the encodings of V2 conversion operators have
the IL type `cvtop`, and numbers have `num_(nt)` at the variable names the `cvtop` rules use.
`NumTyped.num` covers the latter at every variable name already. -/
def CvtTyped (env : Env) : Prop :=
  ∀ op : V2.CvtOp, TypedV env (.varT "cvtop" []) (cvtOpV op)

/-- A V2 value as an IL `CONST`. -/
theorem adminToV_num (n : NumVal) :
    adminToV (Val.num n).toAdmin = .case "CONST" (.tuple [numTypeV n.type, numV n]) := by
  rcases n with ⟨⟨_ | _⟩, _⟩ <;> rfl

/-- The encoded left-hand side of the `cvtop` rules. -/
theorem adminsToV_cvt (target source : NumType) (op : V2.CvtOp) (x : BitVec source.width) :
    adminsToV [(Val.num ⟨source, x⟩).toAdmin, .plain (.cvtOp target source op)] =
      [.case "CONST" (.tuple [numTypeV source, numV ⟨source, x⟩]),
        .case "CVTOP" (.tuple [numTypeV target, numTypeV source, cvtOpV op])] := by
  show [adminToV (Val.num ⟨source, x⟩).toAdmin, instrToV (.cvtOp target source op)] = _
  rw [adminToV_num]
  rfl

/-- **`Step_pure/cvtop-val` is `PureStep.cvtOp`.** -/
theorem cvtOp_iff (A : CvtAgree (simEnv20 B) P) (T : NumTyped (simEnv20 B))
    (Tc : CvtTyped (simEnv20 B)) {target source : NumType} {op : V2.CvtOp}
    {x : BitVec source.width} (hop : (V2.CvtOp.toShared target source op).isSome) {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 26
        (.tuple [.list (adminsToV [(Val.num ⟨source, x⟩).toAdmin,
          .plain (.cvtOp target source op)]), w]) ↔
      ∃ z, CvtOpResult P target source op x z ∧
        w = .list (adminsToV [(Val.num ⟨target, z⟩).toAdmin]) := by
  obtain ⟨vs, happ, hvs, -⟩ := A.cvt target source op x hop
  have hw : ∀ z : BitVec target.width, Value.list [.case "CONST" (.tuple [numTypeV target,
      numV ⟨target, z⟩])] = .list (adminsToV [(Val.num ⟨target, z⟩).toAdmin]) := fun z => by
    show _ = Value.list [adminToV _]
    rw [adminToV_num]
  rw [adminsToV_cvt]
  constructor
  · intro hf
    obtain ⟨c, v, rfl, happ', hm⟩ := cvtopVal_inv B hf
    have hv : v = .list vs := Applies.unique happ' happ
    obtain ⟨z, hz, rfl⟩ := (hvs c).1 (memValue_list_iff.1 (hv ▸ hm))
    exact ⟨z, hz, hw z⟩
  · rintro ⟨z, hz, rfl⟩
    rw [← hw z]
    exact cvtopVal_fires B (T.numtype _ _ ⟨rfl, rfl, rfl⟩)
      (T.num source x "nt_1" _ ⟨rfl, rfl, rfl⟩ rfl) (T.numtype _ _ ⟨rfl, rfl, rfl⟩)
      (Tc op _ ⟨rfl, rfl, rfl⟩) (T.num target z "nt_2" _ ⟨rfl, rfl, rfl⟩ rfl) happ
      (memValue_list_iff.2 ((hvs _).2 ⟨z, hz, rfl⟩))

/-- **`Step_pure/cvtop-trap` is `PureStep.cvtOpTrap`.** -/
theorem cvtOpTrap_iff (A : CvtAgree (simEnv20 B) P) (T : NumTyped (simEnv20 B))
    (Tc : CvtTyped (simEnv20 B)) {target source : NumType} {op : V2.CvtOp}
    {x : BitVec source.width} (hop : (V2.CvtOp.toShared target source op).isSome) {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 27
        (.tuple [.list (adminsToV [(Val.num ⟨source, x⟩).toAdmin,
          .plain (.cvtOp target source op)]), w]) ↔
      CvtOpTraps P target source op x ∧ w = .list (adminsToV [.trap]) := by
  obtain ⟨vs, happ, -, hnil⟩ := A.cvt target source op x hop
  rw [adminsToV_cvt]
  constructor
  · intro hf
    obtain ⟨rfl, happ'⟩ := cvtopTrap_inv B hf
    have hv : Value.list [] = .list vs := Applies.unique happ' happ
    exact ⟨hnil.1 (by simpa using hv.symm), rfl⟩
  · rintro ⟨htr, rfl⟩
    exact cvtopTrap_fires B (T.numtype _ _ ⟨rfl, rfl, rfl⟩)
      (T.num source x "nt_1" _ ⟨rfl, rfl, rfl⟩ rfl) (T.numtype _ _ ⟨rfl, rfl, rfl⟩)
      (Tc op _ ⟨rfl, rfl, rfl⟩) (hnil.2 htr ▸ happ)

end Silmaril.Wasm.SpecTec.Sim20.Pure
