module

import Silmaril.Wasm.Binary.Core.Decode
import Silmaril.Wasm.Binaryen.Intrinsic.Thms
import Silmaril.Wasm.Validation.Check.Validate
meta import Silmaril.Wasm.Binary.Core.Decode
meta import Silmaril.Wasm.Binaryen.Intrinsic.Defs
meta import Silmaril.Wasm.Validation.Check.Validate

namespace BinaryenIntrinsicRegression

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Binaryen.Intrinsic

private def signature (params results : List ValType) : RecType :=
  ⟨[⟨true, [], .func ⟨params, results⟩⟩]⟩

private def chooseSig := signature [.i32, .i64] [.i32]
private def branchSig := signature [.i32] []
private def closed : DefType := (Context.rollGroup {} chooseSig)[0]'(by decide +kernel)
private def chooseCtx : Context := ({ funcs := [closed] } : Context).funcBody [.i32, .i64] [.i32] []
private def branchCtx : Context := ({} : Context).funcBody [.i32] [] []
private def params : Ty (.list .val) := .cons .i32 (.cons .i64 .nil)

private def choose : Expr chooseCtx (some .i32) :=
  .if_ (.value .i32) (.value (TyOk.check_sound (by decide +kernel))) (.localGet ⟨⟨0⟩, rfl⟩)
    (.call (params := params) ⟨closed, ⟨⟨0⟩, rfl⟩, Expand.iff.mpr rfl⟩
      (.cons (TyOk.check_sound (by decide +kernel)) (.localGet ⟨⟨0⟩, rfl⟩)
        (.cons (TyOk.check_sound (by decide +kernel)) (.localGet ⟨⟨1⟩, rfl⟩) .nil)))
    (.intConst .i32 7)

private def branch : Expr branchCtx none :=
  .block .empty .empty (.brIf ⟨⟨0⟩, rfl⟩ (.localGet ⟨⟨0⟩, rfl⟩))

private def loopDrop : Expr ({} : Context) none :=
  .loop .empty .empty (.drop (TyOk.check_sound (by decide +kernel)) (.intConst .i64 9))

private def base : Module := {
  types := [chooseSig, branchSig]
  imports := [⟨"host", "transform", .func ⟨0⟩⟩]
  exports := [⟨"choose", .func ⟨1⟩⟩, ⟨"branch", .func ⟨2⟩⟩] }

private def slot : FunctionSlot := ⟨base, [], [⟨⟨1⟩, [], [branch.erase]⟩], ⟨0⟩, []⟩

private def raw : Module := { base with funcs := [
  ⟨⟨0⟩, [], [.localGet ⟨0⟩, .if_ (.value .i32)
    [.localGet ⟨0⟩, .localGet ⟨1⟩, .call ⟨0⟩] [.intConst .i32 7]]⟩,
  ⟨⟨1⟩, [], [.block .empty [.localGet ⟨0⟩, .brIf ⟨0⟩]]⟩] }

example : (slot.folded choose.erase).lower = raw := rfl
example : slot.core choose.toCore.erase = raw := (choose.lower_in_slot slot).symm.trans rfl
example : (validate? raw).isSome = true := by decide +kernel

example : SeqOk chooseCtx [choose.erase] (.plain [] [.i32]) := choose.sound
example : SeqOk branchCtx [branch.erase] (.plain [] []) := branch.sound
example : SeqOk {} [loopDrop.erase] (.plain [] []) := loopDrop.sound

example : True := by
  fail_if_success
    let _bad : Expr ({} : Context) (some .i32) := .localGet ⟨⟨0⟩, rfl⟩
  fail_if_success
    let _bad : Expr ({} : Context) none := .brIf ⟨⟨0⟩, rfl⟩ (.intConst .i32 1)
  fail_if_success
    let _bad : Operands chooseCtx params.toList :=
      .cons (TyOk.check_sound (by decide +kernel)) (.intConst .i64 9) .nil
  trivial

private def wrongArg : Module := { raw with funcs :=
  ⟨⟨0⟩, [], [.localGet ⟨0⟩, .if_ (.value .i32)
    [.localGet ⟨1⟩, .localGet ⟨0⟩, .call ⟨0⟩] [.intConst .i32 7]]⟩ :: raw.funcs.drop 1 }

example : (validate? wrongArg).isSome = false := by decide +kernel

private def multi : Module := {
  types := [signature [] [.i32, .i64]]
  funcs := [⟨⟨0⟩, [], [.intConst .i32 1, .intConst .i64 2]⟩] }

example : (validate? multi).isSome = true := by decide +kernel
example (result : Option CValType) : result.toList ≠ [.i32, .i64] := by cases result <;> simp

private def foldedCondition : List BExpr → Bool
  | [.if_ _ [_] _ _] => true
  | _ => false

example : BExpr.lowerList [choose.erase] = BExpr.lowerList (liftInstrs choose.erase.lower) := by
  rw [BExpr.lowerList_singleton, lowerList_liftInstrs]

example : [choose.erase] ≠ liftInstrs choose.erase.lower := by
  intro eq
  have impossible : true = false := congrArg foldedCondition eq
  cases impossible

#print axioms Expr.lower_erase
#print axioms Operands.lower_erase
#print axioms Expr.sound
#print axioms Expr.lower_in_slot

def checkNative (path : System.FilePath) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  let .ok decoded := Binary.Core.Decode.decodeModule bytes
    | throw (IO.userError "Core decoder rejected the Binaryen fixture")
  unless (validate? decoded).isSome do
    throw (IO.userError "Core validator rejected the Binaryen fixture")
  unless reprStr decoded.types == reprStr raw.types &&
      reprStr decoded.funcs == reprStr (slot.core choose.toCore.erase).funcs &&
      reprStr decoded.imports == reprStr raw.imports && reprStr decoded.exports == reprStr raw.exports do
    throw (IO.userError s!"Unexpected function/import/export shape from Binaryen: {reprStr decoded}")
  IO.println "Binaryen binary decodes, validates and matches the typed translation's fixture"

end BinaryenIntrinsicRegression

public def main (args : List String) : IO Unit :=
  match args with
  | [path] => BinaryenIntrinsicRegression.checkNative path
  | _ => throw (IO.userError "expected a Binaryen-generated .wasm file")
