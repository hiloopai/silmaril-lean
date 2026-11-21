module

import Silmaril.Wasm.Game.IOAccept.HostRound.Thms
import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun

/-! A validated Core module with one export and one i32 host import. Kernel evaluation
checks that the false arm returns without a call, and the true arm stops at the expected
callout and returns after that call is answered. -/

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
open Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Exec Silmaril.Wasm.Validation
open Silmaril.Accept.IO

private def gateModule : Module where
  types := [⟨[⟨true, [], .func ⟨[.i32], [.i32]⟩⟩]⟩]
  imports := [⟨"env", "echo", .func ⟨0⟩⟩]
  funcs := [⟨⟨0⟩, [], [.localGet ⟨0⟩, .if_ (.value .i32)
    [.localGet ⟨0⟩, .call ⟨0⟩] [.intConst .i32 7]]⟩]
  exports := [⟨"gate", .func ⟨1⟩⟩]

private def gateType := (validate? gateModule).getD ⟨[], []⟩
private def gateInput := importStore (CExternType.funcs gateType.imports)
private def preparation := prepare? evalConst? gateInput gateModule (importAddrs gateType)
private def ready := (preparation.getD (⟨{}, {}, []⟩, none)).1

example : (validate? gateModule).isSome = true := by decide +kernel
example : preparation.isSome = true := by decide +kernel

private def stopAt (input : BitVec 32) : Config Nat :=
  (runI neverFail 32 (Execution.Core.invoke ready.store 1 [Val.i32 input])).1

example : (stopAt 0).outcome? = some (.values [Val.i32 7]) := by decide +kernel
example : (decompose? (stopAt 0).store (stopAt 0).code).isNone = true := by decide +kernel

private def waiting := stopAt 1
private def callout := decompose? waiting.store waiting.code

example : callout.map (fun (_, addr, key, args) => (addr, key, args)) =
    some (0, 0, [Val.i32 1]) := by decide +kernel

private def replied : Option (Config Nat) := callout.map fun (ctx, _, _, args) =>
  ⟨waiting.store, waiting.frame, ctx.fill (Result.values args).toAdmin⟩

example : (replied.bind fun c => (runI neverFail 32 c).1.outcome?) =
    some (.values [Val.i32 1]) := by decide +kernel

private def roles : Roles Unit (List Val) (String × String) (List Val) where
  callOut call := some call.imp
  answerIn _ reply := match reply.result with | .values vs => some vs | _ => none
  result vs _ := some vs

example : answerEventTags gateModule none roles
    ⟨(0, waiting.store, [Val.i32 1]), (waiting.store, .values [Val.i32 1])⟩ =
    [.out ("env", "echo"), .inp [Val.i32 1]] := rfl
