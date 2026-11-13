module

public import Silmaril.Compiler.Native.Lower.Defs
public import Silmaril.Compiler.Native.Types.Registered.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Lower.Registered
open Silmaril.Cerberus Silmaril.Cerberus.Ail Silmaril.Compile

/-- Actual literal lowering emits exactly the previous literal action when no
implementation enum registrations are available. This compares the full state
transformer, including normalization, instructions and any rejection. -/
theorem literal_without_enums (ctx : Lower.Ctx) (constant : IntegerConstant) (type : C.CType)
    (empty : ctx.tags.enums = ∅) :
    (Lower.constant (.integer constant) type).run ctx =
      (show Lower.M Mir.Reg from do
        let (bytes, signed) := type.intShape
        Lower.norm (← Lower.constReg (← Lower.liftE (Types.integerConstantValue constant)))
          bytes signed).run ctx := by
  let code (value : Except String Int) : Lower.M Mir.Reg := do
    let (bytes, signed) := type.intShape
    Lower.norm (← Lower.constReg (← Lower.liftE value)) bytes signed
  change (code (Types.Registered.integerConstantValue ctx.tags constant)).run ctx =
    (code (Types.integerConstantValue constant)).run ctx
  rw [Types.Registered.integerConstantValue_without_enums ctx.tags constant empty]

/-- The actual arithmetic emitter receives exactly the previous type triple
under an empty registry, including compound promoted/usual integer types. This
is an arithmetic emission context equality, not a full recursive lowering claim. -/
theorem arithmetic_without_enums (ctx : Lower.Ctx) (operator : ArithmeticOperator)
    (expression left right : TypedExpression) (leftReg rightReg : Mir.Reg)
    (empty : ctx.tags.enums = ∅) :
    (Lower.arithValues operator (Types.Registered.typeOf ctx.tags expression)
      (Types.Registered.typeOf ctx.tags left) (Types.Registered.typeOf ctx.tags right)
      leftReg rightReg).run ctx =
    (Lower.arithValues operator (Types.typeOf expression) (Types.typeOf left) (Types.typeOf right)
      leftReg rightReg).run ctx := by
  rw [Types.Registered.typeOf_without_enums ctx.tags expression empty,
    Types.Registered.typeOf_without_enums ctx.tags left empty,
    Types.Registered.typeOf_without_enums ctx.tags right empty]

end Silmaril.Compiler.Native.Lower.Registered
