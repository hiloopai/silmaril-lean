module

public import Silmaril.Wasm.SpecTec.Institution.Instr30.Thms

/-!
# Instruction typing of the wasm-3.0 script, extended: the numeric rules

The five numeric rules of `Instr_ok` without premises, located in `simEnv B` by a kernel `rfl`
(copied from `Raw/…/Scripts/Wasm30/Original/Part2.lean`, rules 82 to 86):

* `Instr_ok/const`: `C ⊢ CONST nt c_nt : [] -> [nt]`;
* `Instr_ok/unop`, `binop`, `testop`, `relop`: `C ⊢ OP nt op_nt : [nt]^k -> [t]`, with `t` the
  numeric type `nt` or `I32`.

All five share one shape, `opRule`, and are fired under `DDerivesB` by one lemma, `dd_opRule`, in
any typed context and under every reading of `otherwise`. `dd_intConst`, `dd_intUnOp`,
`dd_intBinOp`, `dd_intTestOp` and `dd_intRelOp` instantiate it at the images of Core's integer
instructions.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30X

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV)
open Silmaril.Wasm
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub (ctxP CtxT)
open Silmaril.Wasm.SpecTec.Institution.Instr30 (itV evalExp_nil)

variable {B : Builtins}

/-! ## The rules -/

/-- `nt`, read as a value type. -/
def ntSubE : Exp := .subE (.varE "nt") (.varT "numtype" []) (.varT "valtype" [])

/-- `I32`. -/
def i32E : Exp := .caseE "I32" (.tupE [])

/-- `%(es)`. -/
def resLE (es : List Exp) : Exp := .caseE "%" (.tupE [.listE es])

/-- `%(ps) ->_[] %(rs)`. -/
def itLE (ps rs : List Exp) : Exp := .caseE "%->_%%" (.tupE [resLE ps, .listE [], resLE rs])

/-- The shape of the five numeric rules: `C ⊢ head(nt, y) : %(ps) ->_[] %(rs)`, with `y` of sort
`X(nt)`, and no premises. -/
def opRule (nm y X head : IL.Id) (ps rs : List Exp) : Rule :=
  .ruleD nm [ctxP, .expP "nt" (.varT "numtype" []), .expP y (.varT X [.expA (.varE "nt")])] "%|-%:%"
    (.tupE [.varE "C", .caseE head (.tupE [.varE "nt", .varE y]), itLE ps rs]) []

set_option maxRecDepth 100000 in
/-- `Instr_ok/const`. -/
theorem ruleAt_const : HasRuleAt (simEnv B) "Instr_ok" "%|-%:%" 82
    (opRule "const" "c_nt" "num_" "CONST" [] [ntSubE]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Instr_ok/unop`. -/
theorem ruleAt_unop : HasRuleAt (simEnv B) "Instr_ok" "%|-%:%" 83
    (opRule "unop" "unop_nt" "unop_" "UNOP" [ntSubE] [ntSubE]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Instr_ok/binop`. -/
theorem ruleAt_binop : HasRuleAt (simEnv B) "Instr_ok" "%|-%:%" 84
    (opRule "binop" "binop_nt" "binop_" "BINOP" [ntSubE, ntSubE] [ntSubE]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Instr_ok/testop`. -/
theorem ruleAt_testop : HasRuleAt (simEnv B) "Instr_ok" "%|-%:%" 85
    (opRule "testop" "testop_nt" "testop_" "TESTOP" [ntSubE] [i32E]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Instr_ok/relop`. -/
theorem ruleAt_relop : HasRuleAt (simEnv B) "Instr_ok" "%|-%:%" 86
    (opRule "relop" "relop_nt" "relop_" "RELOP" [ntSubE, ntSubE] [i32E]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## Firing them -/

/-- The scope of an `opRule`. -/
def opσ (y : IL.Id) (c nv ov : Value) : List (IL.Id × Value) := [(y, ov), ("nt", nv), ("C", c)]

/-- `%(es)` evaluates to `%(vs)` when `es` evaluates to `vs`. -/
theorem evalExp_resLE {env : Env} {ρ : VarEnv} {es : List Exp} {vs : List Value}
    (h : EvalExps env ρ es vs) : EvalExp env ρ (resLE es) (.case "%" (.tuple [.list vs])) :=
  evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_listE_iff.2 ⟨vs, h, rfl⟩)
    evalExps_nil, rfl⟩)

/-- **An `opRule` fires**, from typed values for its three variables and evaluated types. -/
theorem dd_opRule {k : Nat} {nm y X head : IL.Id} {ps rs : List Exp}
    (hr : HasRuleAt (simEnv B) "Instr_ok" "%|-%:%" k (opRule nm y X head ps rs)) (O : ElseI)
    {c nv ov : Value} {pv rv : List Value} (hc : CtxT B c)
    (hnt : (VarEnv.empty.bindVals (opσ y c nv ov)).findVal? "nt" = some nv)
    (hy : (VarEnv.empty.bindVals (opσ y c nv ov)).findVal? y = some ov)
    (hn : HasTyp (simEnv B) (VarEnv.empty.bindVals (opσ y c nv ov)) (.varT "numtype" []) nv)
    (ho : HasTyp (simEnv B) (VarEnv.empty.bindVals (opσ y c nv ov))
      (.varT X [.expA (.varE "nt")]) ov)
    (hp : EvalExps (simEnv B) (VarEnv.empty.bindVals (opσ y c nv ov)) ps pv)
    (hrs : EvalExps (simEnv B) (VarEnv.empty.bindVals (opσ y c nv ov)) rs rv) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [c, .case head (.tuple [nv, ov]), itV pv [] rv]) :=
  dderivesB_of_ruleAt hr (self_mem_conclAlts _) (opσ y c nv ov)
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons hnt hn
      (QuantsOk.cons hy ho QuantsOk.nil)))
    (evalExp_tup3 (Sim.evalExp_var rfl)
      (evalExp_case (evalExp_tup2 (Sim.evalExp_var hnt) (Sim.evalExp_var hy)))
      (evalExp_case (evalExp_tup3 (evalExp_resLE hp) evalExp_nil (evalExp_resLE hrs))))
    (fun _ h => absurd h List.not_mem_nil)

/-! ## At Core's integer instructions -/

/-- The scope of an `opRule` binds only values. -/
theorem valsOnly_opσ (y : IL.Id) (c nv ov : Value) :
    ValsOnly (VarEnv.empty.bindVals (opσ y c nv ov)) := valsOnly_bind _

/-- `nt` evaluates to its value in the scope of an `opRule`. -/
theorem evalExp_nt {y : IL.Id} {c nv ov : Value}
    (h : (VarEnv.empty.bindVals (opσ y c nv ov)).findVal? "nt" = some nv) :
    EvalExp (simEnv B) (VarEnv.empty.bindVals (opσ y c nv ov)) (.varE "nt") nv :=
  Sim.evalExp_var h

/-- `nt`, read as a value type, evaluates to its value. -/
theorem evalExp_ntSub {y : IL.Id} {c nv ov : Value}
    (h : (VarEnv.empty.bindVals (opσ y c nv ov)).findVal? "nt" = some nv) :
    EvalExp (simEnv B) (VarEnv.empty.bindVals (opσ y c nv ov)) ntSubE nv :=
  evalExp_subE_iff.2 (evalExp_nt h)

/-- `I32` evaluates to the image of `i32`. -/
theorem evalExp_i32 {env : Env} {ρ : VarEnv} : EvalExp env ρ i32E (tyV .i32) :=
  Round6.AgreeSub.evalExp_atomE "I32"

/-- The image of an integer value type is `ntV`. -/
theorem tyV_int (t : IntType) : tyV (.num (.int t)) = IntNumeric.ntV t := by cases t <;> rfl

/-- A list of one expression evaluates. -/
theorem evalExps_one {env : Env} {ρ : VarEnv} {e : Exp} {v : Value} (h : EvalExp env ρ e v) :
    EvalExps env ρ [e] [v] := evalExps_cons h evalExps_nil

/-- A list of two expressions evaluates. -/
theorem evalExps_two {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v₁ v₂ : Value}
    (h₁ : EvalExp env ρ e₁ v₁) (h₂ : EvalExp env ρ e₂ v₂) : EvalExps env ρ [e₁, e₂] [v₁, v₂] :=
  evalExps_cons h₁ (evalExps_one h₂)

/-- **`Instr_ok/const`** at an integer constant. -/
theorem dd_intConst (O : ElseI) {c : Value} (hc : CtxT B c) (t : IntType) (b : BitVec t.width) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [c, instrToV (.intConst t b), itV [] [] [tyV (.num (.int t))]]) := by
  rw [tyV_int]
  exact dd_opRule ruleAt_const O hc rfl rfl (IntNumeric.hasTyp_numtype (valsOnly_opσ _ _ _ _) t)
    (IntNumeric.hasTyp_num b (evalExp_nt rfl)) evalExps_nil (evalExps_one (evalExp_ntSub rfl))

/-- **`Instr_ok/unop`** at a valid integer unary operator. -/
theorem dd_intUnOp (O : ElseI) {c : Value} (hc : CtxT B c) {t : IntType} {op : IntUnOp}
    (hv : op.valid t = true) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [c, instrToV (.intUnOp t op), itV [tyV (.num (.int t))] [] [tyV (.num (.int t))]]) := by
  rw [tyV_int, IntNumeric.instrToV_intUnOp t op hv]
  exact dd_opRule ruleAt_unop O hc rfl rfl (IntNumeric.hasTyp_numtype (valsOnly_opσ _ _ _ _) t)
    (IntNumeric.hasTyp_unop (evalExp_nt rfl) op hv) (evalExps_one (evalExp_ntSub rfl))
    (evalExps_one (evalExp_ntSub rfl))

/-- **`Instr_ok/binop`** at an integer binary operator. -/
theorem dd_intBinOp (O : ElseI) {c : Value} (hc : CtxT B c) (t : IntType) (op : IntBinOp) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [c, instrToV (.intBinOp t op),
        itV [tyV (.num (.int t)), tyV (.num (.int t))] [] [tyV (.num (.int t))]]) := by
  rw [tyV_int, IntNumeric.instrToV_intBinOp]
  exact dd_opRule ruleAt_binop O hc rfl rfl (IntNumeric.hasTyp_numtype (valsOnly_opσ _ _ _ _) t)
    (IntNumeric.hasTyp_binop (evalExp_nt rfl) op) (evalExps_two (evalExp_ntSub rfl) (evalExp_ntSub rfl))
    (evalExps_one (evalExp_ntSub rfl))

/-- **`Instr_ok/testop`** at an integer test operator. -/
theorem dd_intTestOp (O : ElseI) {c : Value} (hc : CtxT B c) (t : IntType) (op : IntTestOp) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [c, instrToV (.intTestOp t op), itV [tyV (.num (.int t))] [] [tyV .i32]]) := by
  rw [tyV_int, IntNumeric.instrToV_intTestOp]
  exact dd_opRule ruleAt_testop O hc rfl rfl (IntNumeric.hasTyp_numtype (valsOnly_opσ _ _ _ _) t)
    (IntNumeric.hasTyp_testop (evalExp_nt rfl) op) (evalExps_one (evalExp_ntSub rfl)) (evalExps_one evalExp_i32)

/-- **`Instr_ok/relop`** at an integer comparison. -/
theorem dd_intRelOp (O : ElseI) {c : Value} (hc : CtxT B c) (t : IntType) (op : IntRelOp) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [c, instrToV (.intRelOp t op),
        itV [tyV (.num (.int t)), tyV (.num (.int t))] [] [tyV .i32]]) := by
  rw [tyV_int, IntNumeric.instrToV_intRelOp]
  exact dd_opRule ruleAt_relop O hc rfl rfl (IntNumeric.hasTyp_numtype (valsOnly_opσ _ _ _ _) t)
    (IntNumeric.hasTyp_relop (evalExp_nt rfl) op) (evalExps_two (evalExp_ntSub rfl) (evalExp_ntSub rfl))
    (evalExps_one evalExp_i32)

end Silmaril.Wasm.SpecTec.Institution.Instr30X
