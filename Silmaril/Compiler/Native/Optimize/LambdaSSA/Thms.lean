module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.Defs
@[expose] public section

namespace Silmaril.Compiler.Native.Optimize.LambdaSSA

open Silmaril.Machine

/-- Crossing the older RTL namespace does not change unary arithmetic. -/
theorem oldUnary_eval (op : Lir.Unop) (x : Lir.Word) :
    (oldUnary op).eval x = op.eval x := by
  cases op <;> rfl

/-- Unary operators round trip through the explicit enum adapter exactly. -/
theorem unary_roundTrip (op : Lir.Unop) : newUnary (oldUnary op) = op := by
  cases op <;> rfl

/-- Every admitted binary operator has identical arithmetic in both IR copies. -/
theorem oldBinary_eval (op : Lir.Binop) (old : Old.Binop)
    (h : oldBinary op = some old) (x y : Lir.Word) : old.eval x y = op.eval x y := by
  cases op <;> simp only [oldBinary, reduceCtorEq, Option.some.injEq] at h
  all_goals (cases h; rfl)

def abstractWords : Abstract → Option (List Lir.Word)
  | .unit => some []
  | .pair (.word x) rest => (abstractWords rest).map (x :: ·)
  | _ => none

/-- Each successful primitive fold is an actual transition of the imported
lambda-SSA opcode semantics, with unchanged memory, for any call oracle. This
proves the arithmetic rewrite's local semantic premise; it does not yet prove
the environment analysis, whole-region traversal, flattening or validator. -/
theorem constantOp_sound (oracle : Silmaril.Machine.RTL.CallOracle)
    (memory : Silmaril.Machine.Lir.Memory) {opcode : Old.Opcode} {arg : Abstract}
    {result : Lir.Word} (h : constantOp opcode arg = some result) :
    ∀ values, abstractWords arg = some values →
      Silmaril.Machine.RTL.Opcode.step oracle opcode
        (Silmaril.Machine.RTL.packValues values) memory
        (Silmaril.Machine.RTL.packValues [result]) memory := by
  unfold constantOp at h
  split at h
  · cases h
    intro values hv
    simp only [abstractWords, Option.map_some, Option.some.injEq] at hv
    subst values
    exact .move
  · cases h
    intro values hv
    simp only [abstractWords, Option.map_some, Option.some.injEq] at hv
    subst values
    exact .unary
  · intro values hv
    simp only [abstractWords, Option.map_some, Option.some.injEq] at hv
    subst values
    exact .binary h
  · cases h

end Silmaril.Compiler.Native.Optimize.LambdaSSA
