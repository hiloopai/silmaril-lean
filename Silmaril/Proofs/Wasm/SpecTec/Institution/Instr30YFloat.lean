module

public import Silmaril.Wasm.SpecTec.Institution.Instr30X.Thms

/-!
# Instruction typing of the wasm-3.0 script, the float numeric rules

`Instr30X` fired `Instr_ok/const`, `unop`, `binop`, `testop`, `relop` (rules 82–86, one shape
`opRule`, fired by `dd_opRule`) at Core's integer instructions. The same rules type Core's float
instructions, with the operator sorts `unop_(Fnn)`, `binop_(Fnn)`, `relop_(Fnn)` and the value sort
`num_(Fnn)`:

* `dd_floatConst`, `dd_floatUnOp`, `dd_floatBinOp`, `dd_floatRelOp`: in any typed context and
  under every reading of `otherwise`, at the images of Core's typings
  (`NumericInstrOk.floatConst`, `floatUnOp`, `floatBinOp`, `floatRelOp`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30Y

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV)
open Silmaril.Wasm
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub (ctxP CtxT)
open Silmaril.Wasm.SpecTec.Institution.Instr30 (itV evalExp_nil)
open Silmaril.Wasm.SpecTec.Institution.Instr30X (opσ dd_opRule ruleAt_const ruleAt_unop ruleAt_binop
  ruleAt_relop valsOnly_opσ evalExp_nt evalExp_ntSub evalExp_i32 evalExps_one evalExps_two)

variable {B : Builtins}

/-- The image of a float value type is `numTypeV`. -/
theorem tyV_float (t : FloatType) : tyV (.num (.float t)) = Vec.numTypeV (.float t) := by
  cases t <;> rfl

/-- **`Instr_ok/const`** at a float constant. -/
theorem dd_floatConst (O : ElseI) {c : Value} (hc : CtxT B c) (t : FloatType) (b : BitVec t.width) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [c, instrToV (.floatConst t b), itV [] [] [tyV (.num (.float t))]]) := by
  rw [tyV_float, Vec.instrToV_floatConst]
  exact dd_opRule ruleAt_const O hc rfl rfl (Typing.hasTyp_numtype (valsOnly_opσ _ _ _ _) _)
    (Typing.hasTyp_num_float t b (evalExp_nt rfl)) evalExps_nil (evalExps_one (evalExp_ntSub rfl))

/-- **`Instr_ok/unop`** at a float unary operator. -/
theorem dd_floatUnOp (O : ElseI) {c : Value} (hc : CtxT B c) (t : FloatType) (op : FloatUnOp) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [c, instrToV (.floatUnOp t op),
        itV [tyV (.num (.float t))] [] [tyV (.num (.float t))]]) := by
  rw [tyV_float, Vec.instrToV_floatUnOp]
  exact dd_opRule ruleAt_unop O hc rfl rfl (Typing.hasTyp_numtype (valsOnly_opσ _ _ _ _) _)
    (Floats.typedDep_unop t op _ (valsOnly_opσ _ _ _ _) rfl) (evalExps_one (evalExp_ntSub rfl))
    (evalExps_one (evalExp_ntSub rfl))

/-- **`Instr_ok/binop`** at a float binary operator. -/
theorem dd_floatBinOp (O : ElseI) {c : Value} (hc : CtxT B c) (t : FloatType) (op : FloatBinOp) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [c, instrToV (.floatBinOp t op),
        itV [tyV (.num (.float t)), tyV (.num (.float t))] [] [tyV (.num (.float t))]]) := by
  rw [tyV_float, Vec.instrToV_floatBinOp]
  exact dd_opRule ruleAt_binop O hc rfl rfl (Typing.hasTyp_numtype (valsOnly_opσ _ _ _ _) _)
    (Floats.typedDep_binop t op _ (valsOnly_opσ _ _ _ _) rfl)
    (evalExps_two (evalExp_ntSub rfl) (evalExp_ntSub rfl)) (evalExps_one (evalExp_ntSub rfl))

/-- **`Instr_ok/relop`** at a float comparison. -/
theorem dd_floatRelOp (O : ElseI) {c : Value} (hc : CtxT B c) (t : FloatType) (op : FloatRelOp) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [c, instrToV (.floatRelOp t op),
        itV [tyV (.num (.float t)), tyV (.num (.float t))] [] [tyV .i32]]) := by
  rw [tyV_float, Vec.instrToV_floatRelOp]
  exact dd_opRule ruleAt_relop O hc rfl rfl (Typing.hasTyp_numtype (valsOnly_opσ _ _ _ _) _)
    (Floats.typedDep_relop t op _ (valsOnly_opσ _ _ _ _) rfl)
    (evalExps_two (evalExp_ntSub rfl) (evalExp_ntSub rfl)) (evalExps_one evalExp_i32)

end Silmaril.Wasm.SpecTec.Institution.Instr30Y
