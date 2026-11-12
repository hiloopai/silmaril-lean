module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Lift
public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Env

/-!
# Integer numerics: the `Step_pure` rules, constructed under the declarative reading

For arbitrary values, each lemma builds a `Step_pure` derivation of one rule from its quantifier
typings (in the rule's own scope `VarEnv.empty.bindVals σ`) and its premise. These are the rules
of the family: `unreachable`, `nop`, `drop` (0–2), `unop-val`, `binop-val`, `binop-trap`,
`testop`, `relop` (46, 48–51). Nothing here is specific to integers; the instantiation is in
`Forward.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.IntNumeric

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef evalArgs_three evalArgs_four)

/-- `CONST x y` with `x`, `y` variables. -/
theorem evalExp_constVars {env : Env} {ρ : VarEnv} {x y : IL.Id} {a b : Value}
    (ha : ρ.findVal? x = some a) (hb : ρ.findVal? y = some b) :
    EvalExp env ρ (.caseE "CONST" (.tupE [.varE x, .varE y])) (.case "CONST" (.tuple [a, b])) :=
  evalExp_case (evalExp_tup2 (evalExp_var ha) (evalExp_var hb))

/-- `OP x y` with `x`, `y` variables. -/
theorem evalExp_opVars {env : Env} {ρ : VarEnv} {op : MixopS} {x y : IL.Id} {a b : Value}
    (ha : ρ.findVal? x = some a) (hb : ρ.findVal? y = some b) :
    EvalExp env ρ (.caseE op (.tupE [.varE x, .varE y])) (.case op (.tuple [a, b])) :=
  evalExp_case (evalExp_tup2 (evalExp_var ha) (evalExp_var hb))

/-- A list of two evaluated expressions. -/
theorem evalExp_list2 {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v₁ v₂ : Value}
    (h₁ : EvalExp env ρ e₁ v₁) (h₂ : EvalExp env ρ e₂ v₂) :
    EvalExp env ρ (.listE [e₁, e₂]) (.list [v₁, v₂]) :=
  evalExp_listE_iff.2 ⟨_, evalExps_cons h₁ (evalExps_cons h₂ evalExps_nil), rfl⟩

/-- A list of three evaluated expressions. -/
theorem evalExp_list3 {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ : Exp} {v₁ v₂ v₃ : Value}
    (h₁ : EvalExp env ρ e₁ v₁) (h₂ : EvalExp env ρ e₂ v₂) (h₃ : EvalExp env ρ e₃ v₃) :
    EvalExp env ρ (.listE [e₁, e₂, e₃]) (.list [v₁, v₂, v₃]) :=
  evalExp_listE_iff.2 ⟨_, evalExps_cons h₁ (evalExps_cons h₂ (evalExps_cons h₃ evalExps_nil)),
    rfl⟩

/-- The empty list. -/
theorem evalExp_list0 {env : Env} {ρ : VarEnv} : EvalExp env ρ (.listE []) (.list []) :=
  evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩

/-- A nullary case `OP`. -/
theorem evalExp_nullary {env : Env} {ρ : VarEnv} {op : MixopS} :
    EvalExp env ρ (.caseE op (.tupE [])) (.case op (.tuple [])) :=
  evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)

/-! ## `unreachable`, `nop`, `drop` -/

/-- `Step_pure/unreachable`. -/
theorem spure_unreachable {env : Env}
    (h : HasRuleAt env "Step_pure" "%~>%" 0 Equiv.Execution.unreachableRule) :
    SPure env [.case "UNREACHABLE" (.tuple [])] [.case "TRAP" (.tuple [])] :=
  dderives_of_ruleAt h [] QuantsOk.nil
    (evalExp_tup2 (evalExp_list1 evalExp_nullary) (evalExp_list1 evalExp_nullary))
    (fun _ hp => by cases hp)

/-- `Step_pure/nop`. -/
theorem spure_nopRule {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 1 Equiv.Execution.nopRule) :
    SPure env [.case "NOP" (.tuple [])] [] :=
  dderives_of_ruleAt h [] QuantsOk.nil (evalExp_tup2 (evalExp_list1 evalExp_nullary) evalExp_list0)
    (fun _ hp => by cases hp)

/-- `Step_pure/drop`, for a value of type `val`. -/
theorem spure_drop {env : Env} (h : HasRuleAt env "Step_pure" "%~>%" 2 Equiv.Execution.dropRule)
    {v : Value} (hv : HasTyp env (VarEnv.empty.bindVals [("val", v)]) (.varT "val" []) v) :
    SPure env [v, .case "DROP" (.tuple [])] [] := by
  have fv : (VarEnv.empty.bindVals [("val", v)]).findVal? "val" = some v := rfl
  exact dderives_of_ruleAt h [("val", v)] (QuantsOk.cons fv hv QuantsOk.nil)
    (evalExp_tup2 (evalExp_list2 (evalExp_subE_iff.2 (evalExp_var fv)) evalExp_nullary)
      evalExp_list0)
    (fun _ hp => by cases hp)

/-! ## The scalar numeric rules -/

/-- The scope of `binop-val`. -/
def scopeBin (nt c₁ c₂ op c : Value) : VarEnv :=
  VarEnv.empty.bindVals [("nt", nt), ("c_1", c₁), ("c_2", c₂), ("binop", op), ("c", c)]

/-- `Step_pure/binop-val`: `c ∈ $binop_(nt, binop, c_1, c_2)`. -/
theorem spure_binopVal {env : Env}
    (h : HasRuleAt env "Step_pure" "%~>%" 48 Equiv.ExecNumeric.binopValRule)
    {nt c₁ c₂ op c w : Value}
    (h₀ : HasTyp env (scopeBin nt c₁ c₂ op c) (.varT "numtype" []) nt)
    (h₁ : HasTyp env (scopeBin nt c₁ c₂ op c) (.varT "num_" [.expA (.varE "nt")]) c₁)
    (h₂ : HasTyp env (scopeBin nt c₁ c₂ op c) (.varT "num_" [.expA (.varE "nt")]) c₂)
    (h₃ : HasTyp env (scopeBin nt c₁ c₂ op c) (.varT "binop_" [.expA (.varE "nt")]) op)
    (h₄ : HasTyp env (scopeBin nt c₁ c₂ op c) (.varT "num_" [.expA (.varE "nt")]) c)
    (happ : Applies env "binop_" [.val nt, .val op, .val c₁, .val c₂] w)
    (hmem : memValue c w = .ok (.bool true)) :
    SPure env [.case "CONST" (.tuple [nt, c₁]), .case "CONST" (.tuple [nt, c₂]),
      .case "BINOP" (.tuple [nt, op])] [.case "CONST" (.tuple [nt, c])] := by
  have fnt : (scopeBin nt c₁ c₂ op c).findVal? "nt" = some nt := rfl
  have f1 : (scopeBin nt c₁ c₂ op c).findVal? "c_1" = some c₁ := rfl
  have f2 : (scopeBin nt c₁ c₂ op c).findVal? "c_2" = some c₂ := rfl
  have fop : (scopeBin nt c₁ c₂ op c).findVal? "binop" = some op := rfl
  have fc : (scopeBin nt c₁ c₂ op c).findVal? "c" = some c := rfl
  have hcall : EvalExp env (scopeBin nt c₁ c₂ op c)
      (.callE "binop_" [.expA (.varE "nt"), .expA (.varE "binop"), .expA (.varE "c_1"),
        .expA (.varE "c_2")]) w :=
    evalExp_callE_iff.2 ((applies_iff_callDef rfl (evalArgs_four fnt fop f1 f2)).1 happ)
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fnt h₀ (QuantsOk.cons f1 h₁ (QuantsOk.cons f2 h₂ (QuantsOk.cons fop h₃
      (QuantsOk.cons fc h₄ QuantsOk.nil)))))
    (evalExp_tup2 (evalExp_list3 (evalExp_constVars fnt f1) (evalExp_constVars fnt f2)
      (evalExp_opVars fnt fop)) (evalExp_list1 (evalExp_constVars fnt fc)))
    (prems_one (.ifPr (evalExp_memE_iff.2 ⟨c, w, evalExp_var fc, hcall, hmem⟩)))

/-- The scope of `binop-trap`. -/
def scopeBinT (nt c₁ c₂ op : Value) : VarEnv :=
  VarEnv.empty.bindVals [("nt", nt), ("c_1", c₁), ("c_2", c₂), ("binop", op)]

/-- `Step_pure/binop-trap`: `$binop_(nt, binop, c_1, c_2) = eps`. -/
theorem spure_binopTrap {env : Env}
    (h : HasRuleAt env "Step_pure" "%~>%" 49 Equiv.ExecNumeric.binopTrapRule)
    {nt c₁ c₂ op : Value}
    (h₀ : HasTyp env (scopeBinT nt c₁ c₂ op) (.varT "numtype" []) nt)
    (h₁ : HasTyp env (scopeBinT nt c₁ c₂ op) (.varT "num_" [.expA (.varE "nt")]) c₁)
    (h₂ : HasTyp env (scopeBinT nt c₁ c₂ op) (.varT "num_" [.expA (.varE "nt")]) c₂)
    (h₃ : HasTyp env (scopeBinT nt c₁ c₂ op) (.varT "binop_" [.expA (.varE "nt")]) op)
    (happ : Applies env "binop_" [.val nt, .val op, .val c₁, .val c₂] (.list [])) :
    SPure env [.case "CONST" (.tuple [nt, c₁]), .case "CONST" (.tuple [nt, c₂]),
      .case "BINOP" (.tuple [nt, op])] [.case "TRAP" (.tuple [])] := by
  have fnt : (scopeBinT nt c₁ c₂ op).findVal? "nt" = some nt := rfl
  have f1 : (scopeBinT nt c₁ c₂ op).findVal? "c_1" = some c₁ := rfl
  have f2 : (scopeBinT nt c₁ c₂ op).findVal? "c_2" = some c₂ := rfl
  have fop : (scopeBinT nt c₁ c₂ op).findVal? "binop" = some op := rfl
  have hcall : EvalExp env (scopeBinT nt c₁ c₂ op)
      (.callE "binop_" [.expA (.varE "nt"), .expA (.varE "binop"), .expA (.varE "c_1"),
        .expA (.varE "c_2")]) (.list []) :=
    evalExp_callE_iff.2 ((applies_iff_callDef rfl (evalArgs_four fnt fop f1 f2)).1 happ)
  have hif : EvalExp env (scopeBinT nt c₁ c₂ op)
      (.cmpE .eqOp .boolT (.callE "binop_" [.expA (.varE "nt"), .expA (.varE "binop"),
        .expA (.varE "c_1"), .expA (.varE "c_2")]) (.listE [])) (.bool true) := by
    have he := evalExp_eq (t := .boolT) hcall (evalExp_list0 (env := env))
    simpa using he
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fnt h₀ (QuantsOk.cons f1 h₁ (QuantsOk.cons f2 h₂ (QuantsOk.cons fop h₃
      QuantsOk.nil))))
    (evalExp_tup2 (evalExp_list3 (evalExp_constVars fnt f1) (evalExp_constVars fnt f2)
      (evalExp_opVars fnt fop)) (evalExp_list1 evalExp_nullary))
    (prems_one (.ifPr hif))

/-- The scope of `unop-val`. -/
def scopeUn (nt c₁ op c : Value) : VarEnv :=
  VarEnv.empty.bindVals [("nt", nt), ("c_1", c₁), ("unop", op), ("c", c)]

/-- `Step_pure/unop-val`: `c ∈ $unop_(nt, unop, c_1)`. -/
theorem spure_unopVal {env : Env}
    (h : HasRuleAt env "Step_pure" "%~>%" 46 Equiv.ExecNumeric.unopValRule)
    {nt c₁ op c w : Value}
    (h₀ : HasTyp env (scopeUn nt c₁ op c) (.varT "numtype" []) nt)
    (h₁ : HasTyp env (scopeUn nt c₁ op c) (.varT "num_" [.expA (.varE "nt")]) c₁)
    (h₂ : HasTyp env (scopeUn nt c₁ op c) (.varT "unop_" [.expA (.varE "nt")]) op)
    (h₃ : HasTyp env (scopeUn nt c₁ op c) (.varT "num_" [.expA (.varE "nt")]) c)
    (happ : Applies env "unop_" [.val nt, .val op, .val c₁] w)
    (hmem : memValue c w = .ok (.bool true)) :
    SPure env [.case "CONST" (.tuple [nt, c₁]), .case "UNOP" (.tuple [nt, op])]
      [.case "CONST" (.tuple [nt, c])] := by
  have fnt : (scopeUn nt c₁ op c).findVal? "nt" = some nt := rfl
  have f1 : (scopeUn nt c₁ op c).findVal? "c_1" = some c₁ := rfl
  have fop : (scopeUn nt c₁ op c).findVal? "unop" = some op := rfl
  have fc : (scopeUn nt c₁ op c).findVal? "c" = some c := rfl
  have hcall : EvalExp env (scopeUn nt c₁ op c)
      (.callE "unop_" [.expA (.varE "nt"), .expA (.varE "unop"), .expA (.varE "c_1")]) w :=
    evalExp_callE_iff.2 ((applies_iff_callDef rfl (evalArgs_three fnt fop f1)).1 happ)
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fnt h₀ (QuantsOk.cons f1 h₁ (QuantsOk.cons fop h₂ (QuantsOk.cons fc h₃
      QuantsOk.nil))))
    (evalExp_tup2 (evalExp_list2 (evalExp_constVars fnt f1) (evalExp_opVars fnt fop))
      (evalExp_list1 (evalExp_constVars fnt fc)))
    (prems_one (.ifPr (evalExp_memE_iff.2 ⟨c, w, evalExp_var fc, hcall, hmem⟩)))

/-- The scope of `testop`. -/
def scopeTest (nt c₁ op c : Value) : VarEnv :=
  VarEnv.empty.bindVals [("nt", nt), ("c_1", c₁), ("testop", op), ("c", c)]

/-- `I32`, as the rules write it. -/
theorem evalExp_i32 {env : Env} {ρ : VarEnv} :
    EvalExp env ρ (.caseE "I32" (.tupE [])) (.case "I32" (.tuple [])) := evalExp_nullary

/-- `Step_pure/testop`: `c = $testop_(nt, testop, c_1)`. -/
theorem spure_testop {env : Env}
    (h : HasRuleAt env "Step_pure" "%~>%" 50 Equiv.ExecNumeric.testopRule)
    {nt c₁ op c : Value}
    (h₀ : HasTyp env (scopeTest nt c₁ op c) (.varT "numtype" []) nt)
    (h₁ : HasTyp env (scopeTest nt c₁ op c) (.varT "num_" [.expA (.varE "nt")]) c₁)
    (h₂ : HasTyp env (scopeTest nt c₁ op c) (.varT "testop_" [.expA (.varE "nt")]) op)
    (h₃ : HasTyp env (scopeTest nt c₁ op c)
      (.varT "num_" [.expA (.caseE "I32" (.tupE []))]) c)
    (happ : Applies env "testop_" [.val nt, .val op, .val c₁] c) :
    SPure env [.case "CONST" (.tuple [nt, c₁]), .case "TESTOP" (.tuple [nt, op])]
      [.case "CONST" (.tuple [.case "I32" (.tuple []), c])] := by
  have fnt : (scopeTest nt c₁ op c).findVal? "nt" = some nt := rfl
  have f1 : (scopeTest nt c₁ op c).findVal? "c_1" = some c₁ := rfl
  have fop : (scopeTest nt c₁ op c).findVal? "testop" = some op := rfl
  have fc : (scopeTest nt c₁ op c).findVal? "c" = some c := rfl
  have hcall : EvalExp env (scopeTest nt c₁ op c)
      (.callE "testop_" [.expA (.varE "nt"), .expA (.varE "testop"), .expA (.varE "c_1")]) c :=
    evalExp_callE_iff.2 ((applies_iff_callDef rfl (evalArgs_three fnt fop f1)).1 happ)
  have hif : EvalExp env (scopeTest nt c₁ op c)
      (.cmpE .eqOp .boolT (.varE "c") (.callE "testop_" [.expA (.varE "nt"),
        .expA (.varE "testop"), .expA (.varE "c_1")])) (.bool true) := by
    have he := evalExp_eq (t := .boolT) (evalExp_var fc) hcall
    simpa using he
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fnt h₀ (QuantsOk.cons f1 h₁ (QuantsOk.cons fop h₂ (QuantsOk.cons fc h₃
      QuantsOk.nil))))
    (evalExp_tup2 (evalExp_list2 (evalExp_constVars fnt f1) (evalExp_opVars fnt fop))
      (evalExp_list1 (evalExp_case (evalExp_tup2 evalExp_i32 (evalExp_var fc)))))
    (prems_one (.ifPr hif))

/-- The scope of `relop`. -/
def scopeRel (nt c₁ c₂ op c : Value) : VarEnv :=
  VarEnv.empty.bindVals [("nt", nt), ("c_1", c₁), ("c_2", c₂), ("relop", op), ("c", c)]

/-- `Step_pure/relop`: `c = $relop_(nt, relop, c_1, c_2)`. -/
theorem spure_relop {env : Env}
    (h : HasRuleAt env "Step_pure" "%~>%" 51 Equiv.ExecNumeric.relopRule)
    {nt c₁ c₂ op c : Value}
    (h₀ : HasTyp env (scopeRel nt c₁ c₂ op c) (.varT "numtype" []) nt)
    (h₁ : HasTyp env (scopeRel nt c₁ c₂ op c) (.varT "num_" [.expA (.varE "nt")]) c₁)
    (h₂ : HasTyp env (scopeRel nt c₁ c₂ op c) (.varT "num_" [.expA (.varE "nt")]) c₂)
    (h₃ : HasTyp env (scopeRel nt c₁ c₂ op c) (.varT "relop_" [.expA (.varE "nt")]) op)
    (h₄ : HasTyp env (scopeRel nt c₁ c₂ op c)
      (.varT "num_" [.expA (.caseE "I32" (.tupE []))]) c)
    (happ : Applies env "relop_" [.val nt, .val op, .val c₁, .val c₂] c) :
    SPure env [.case "CONST" (.tuple [nt, c₁]), .case "CONST" (.tuple [nt, c₂]),
      .case "RELOP" (.tuple [nt, op])] [.case "CONST" (.tuple [.case "I32" (.tuple []), c])] := by
  have fnt : (scopeRel nt c₁ c₂ op c).findVal? "nt" = some nt := rfl
  have f1 : (scopeRel nt c₁ c₂ op c).findVal? "c_1" = some c₁ := rfl
  have f2 : (scopeRel nt c₁ c₂ op c).findVal? "c_2" = some c₂ := rfl
  have fop : (scopeRel nt c₁ c₂ op c).findVal? "relop" = some op := rfl
  have fc : (scopeRel nt c₁ c₂ op c).findVal? "c" = some c := rfl
  have hcall : EvalExp env (scopeRel nt c₁ c₂ op c)
      (.callE "relop_" [.expA (.varE "nt"), .expA (.varE "relop"), .expA (.varE "c_1"),
        .expA (.varE "c_2")]) c :=
    evalExp_callE_iff.2 ((applies_iff_callDef rfl (evalArgs_four fnt fop f1 f2)).1 happ)
  have hif : EvalExp env (scopeRel nt c₁ c₂ op c)
      (.cmpE .eqOp .boolT (.varE "c") (.callE "relop_" [.expA (.varE "nt"),
        .expA (.varE "relop"), .expA (.varE "c_1"), .expA (.varE "c_2")])) (.bool true) := by
    have he := evalExp_eq (t := .boolT) (evalExp_var fc) hcall
    simpa using he
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fnt h₀ (QuantsOk.cons f1 h₁ (QuantsOk.cons f2 h₂ (QuantsOk.cons fop h₃
      (QuantsOk.cons fc h₄ QuantsOk.nil)))))
    (evalExp_tup2 (evalExp_list3 (evalExp_constVars fnt f1) (evalExp_constVars fnt f2)
      (evalExp_opVars fnt fop))
      (evalExp_list1 (evalExp_case (evalExp_tup2 evalExp_i32 (evalExp_var fc)))))
    (prems_one (.ifPr hif))

end Silmaril.Wasm.SpecTec.Sim.IntNumeric
