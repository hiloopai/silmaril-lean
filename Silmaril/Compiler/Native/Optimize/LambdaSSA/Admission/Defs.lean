module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.Folding.Defs
/-! Independent arithmetic-instruction syntax selected by the actual native
oldOp adapter, before any operand-scope, shape or semantic admission proof. -/
@[expose] public section

namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.Admission
open Silmaril.Isotope.LambdaSSA
open Silmaril.Machine.RTL (Opcode)
open Silmaril.Machine.RTL.SSA (Scope)
open Folding

/-- The actual old-RTL arithmetic instruction vocabulary selected by oldOp. -/
def ArithmeticOp : Old.Op → Prop
  | .const _ _ | .move _ _ | .unary _ _ _ => True
  | .binary opcode _ _ _ => (newBinary opcode).isSome = true
  | _ => False

/-- A return, trap or fixed jump cannot introduce the test opcode. -/
def NoTestTerm : Silmaril.Machine.RTL.SSA.Term Nat → Prop
  | .cond .. => False
  | _ => True


end Silmaril.Compiler.Native.Optimize.LambdaSSA.Admission
