module

public import Silmaril.Wasm.Binaryen.Intrinsic.Defs
public import Silmaril.Wasm.Binaryen.Typing
public import Silmaril.Wasm.Validation.Intrinsic.Thms
import Silmaril.Proofs.Wasm.Binaryen.Intrinsic.Lower

public section

namespace Silmaril.Wasm.Binaryen.Intrinsic

open Validation

/-- Intrinsic Core translation followed by erasure agrees with existing layer-D lowering. -/
theorem Expr.lower_erase {context result} (expr : Expr context result) :
    expr.erase.lower = expr.toCore.erase := Proofs.Wasm.Binaryen.Intrinsic.lower_expr expr

theorem Operands.lower_erase {context types} (args : Operands context types) :
    BExpr.lowerList args.erase = args.toCore.erase := Proofs.Wasm.Binaryen.Intrinsic.lower_operands args

/-- The erased tree satisfies the existing Binaryen typing judgment, not a new validator. -/
theorem Expr.sound {context result} (expr : Expr context result) :
    SeqOk context [expr.erase] (.plain [] result.toList) := by
  simpa [SeqOk, expr.lower_erase] using expr.toCore.sound

/-- Plug into any function position, keeping all other declarations fixed. -/
theorem Expr.lower_in_slot {context result} (expr : Expr context result) (slot : FunctionSlot) :
    (slot.folded expr.erase).lower = slot.core expr.toCore.erase := by
  simp [FunctionSlot.folded, FunctionSlot.core, BModule.lower, Declaration.Func.mapBody, expr.lower_erase]

end Silmaril.Wasm.Binaryen.Intrinsic
