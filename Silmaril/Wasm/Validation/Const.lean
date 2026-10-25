module

public import Silmaril.Wasm.Validation.Instructions

@[expose] public section

/-! # Constant expressions (§2.3 "Constant expressions")

`Instr_const` (all 14 rules), `Expr_const`, `Expr_ok_const`. Core 3.0 allows
`global.get` of any immutable global visible in the context (module validation
passes the globals defined so far), and the extended-constant integer
`add`/`sub`/`mul`.
-/

namespace Silmaril.Wasm.Validation

/-- `Instr_const: C ⊢ instr CONST`. -/
inductive InstrConst (C : Context) : Instr → Prop where
  /-- `Instr_const/const` (integers). -/
  | intConst (t : IntType) (b : BitVec t.width) : InstrConst C (.intConst t b)
  /-- `Instr_const/const` (floats). -/
  | floatConst (t : FloatType) (b : BitVec t.width) : InstrConst C (.floatConst t b)
  /-- `Instr_const/vconst`. -/
  | vecConst (b : BitVec 128) : InstrConst C (.vecConst b)
  /-- `Instr_const/ref.null`. -/
  | refNull (ht : HeapType) : InstrConst C (.refNull ht)
  /-- `Instr_const/ref.i31`. -/
  | refI31 : InstrConst C .refI31
  /-- `Instr_const/ref.func`. -/
  | refFunc (x : FuncIdx) : InstrConst C (.refFunc x)
  /-- `Instr_const/struct.new`. -/
  | structNew (x : TypeIdx) : InstrConst C (.structNew x)
  /-- `Instr_const/struct.new_default`. -/
  | structNewDefault (x : TypeIdx) : InstrConst C (.structNewDefault x)
  /-- `Instr_const/array.new`. -/
  | arrayNew (x : TypeIdx) : InstrConst C (.arrayNew x)
  /-- `Instr_const/array.new_default`. -/
  | arrayNewDefault (x : TypeIdx) : InstrConst C (.arrayNewDefault x)
  /-- `Instr_const/array.new_fixed`. -/
  | arrayNewFixed (x : TypeIdx) (n : Fin (2 ^ 32)) : InstrConst C (.arrayNewFixed x n)
  /-- `Instr_const/any.convert_extern`. -/
  | anyConvertExtern : InstrConst C .anyConvertExtern
  /-- `Instr_const/extern.convert_any`. -/
  | externConvertAny : InstrConst C .externConvertAny
  /-- `Instr_const/global.get`: immutable globals only. -/
  | globalGet {x : GlobalIdx} {t : CValType} (h : C.globals[x.toNat]? = some ⟨.const, t⟩) :
      InstrConst C (.globalGet x)
  /-- `Instr_const/binop`: `i32`/`i64` `add`, `sub`, `mul`. -/
  | binop {t : IntType} {op : IntBinOp} (hop : op = .add ∨ op = .sub ∨ op = .mul) :
      InstrConst C (.intBinOp t op)

/-- `Expr_const`. -/
def ExprConst (C : Context) (e : Expr) : Prop := ∀ i ∈ e, InstrConst C i

/-- `Expr_ok_const: C ⊢ expr : t CONST`. -/
structure ExprOkConst (C : Context) (e : Expr) (t : CValType) : Prop where
  typed : ExprOk C e [t]
  const : ExprConst C e

end Silmaril.Wasm.Validation
