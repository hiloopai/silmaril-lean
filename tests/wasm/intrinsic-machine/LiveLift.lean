module

import Silmaril.Wasm.Execution.Core.Intrinsic.LiveLift.Thms

open Silmaril.Wasm Silmaril.Wasm.Execution.Core.Intrinsic

private def getSecond : Code [.i32, .i64] [.i64] [.i64] :=
  .seq (.localGet (.there .here) (by decide)) (.seq (.intBin .add) .done)

private def rawCode : List Instr := [.localGet ⟨1⟩, .intBinOp .i64 .add]

example : getSecond.erase = rawCode := rfl

private theorem getSecond_live : .unreachable ∉ getSecond.erase := by
  simp [getSecond, Code.erase, Op.erase]

example : Code.reify? [.i32, .i64] [.i64] rawCode = some ⟨[.i64], getSecond, rfl, getSecond_live⟩ :=
  Code.reify_erase getSecond getSecond_live

example : (Code.reify? [.i32, .i64] [.i32] rawCode).isSome = false := rfl
example : (Code.reify? [.i32, .i64] [] [.localGet ⟨2⟩]).isSome = false := rfl
example : (Code.reify? [] [] [.unreachable]).isSome = false := rfl
example : (Code.reify? [] [] [.drop]).isSome = false := rfl
example : (Code.reify? [] [] [.intConst .i32 0]).isSome = false := rfl

#print axioms Code.liveEquiv
#print axioms Code.reify_erase
#print axioms Code.Lifted.sound
