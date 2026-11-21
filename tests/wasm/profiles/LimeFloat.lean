module

import Silmaril.Wasm.Lime1.Execution.Callout
import Silmaril.Wasm.Lime1.Execution.Instantiation
import Silmaril.Wasm.Lime1.ToCore

open Silmaril.Wasm
open Silmaril.Wasm.Lime1.Validation
open Silmaril.Wasm.Execution.Runtime (Result Value)

namespace Silmaril.Tests.LimeFloat

private def signature (width : FloatType) : Lime1.FuncType :=
  ⟨[], [.float width, .i32, .i32]⟩

private def body (width : FloatType) (left right : BitVec width.width) : Lime1.Expr :=
  [.floatConst width left, .floatConst width right, .floatBinOp width .add,
   .floatConst width left, .floatConst width right, .floatRelOp width .eq,
   .floatConst width left, .convert (.truncSat width .i32 .signed)]

private def probe (width : FloatType) (left right : BitVec width.width) : Lime1.Module where
  types := [signature width]
  funcs := [⟨⟨0⟩, [], body width left right⟩]
  exports := [⟨"probe", .func ⟨0⟩⟩]

private theorem body_valid (context : Context) (width : FloatType) (left right : BitVec width.width) :
    ExprType context (body width left right) [] (signature width).results :=
  .cons (.floatConst width left) <|
  .cons (.frame [.float width] (.floatConst width right)) <|
  .cons (.floatBinOp width .add) <|
  .cons (.frame [.float width] (.floatConst width left)) <|
  .cons (.frame [.float width, .float width] (.floatConst width right)) <|
  .cons (.frame [.float width] (.floatRelOp width .eq)) <|
  .cons (.frame [.float width, .i32] (.floatConst width left)) <|
  .cons (.frame [.float width, .i32] (.convert (.truncSat width .i32 .signed))) <|
  .nil _

example (width : FloatType) (left right : BitVec width.width) : ModuleValid (probe width left right) where
  types := fun _ _ => trivial
  imports := by simp [probe]
  functions := by
    intro fn member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨signature width, rfl, trivial, body_valid _ width left right⟩
  tables := by simp [probe]
  memories := by simp [probe]
  globals := by simp [probe]
  elements := by simp [probe]
  data := by simp [probe]
  start := by simp [probe, StartValid]
  exports := by
    intro entry member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨.func (signature width), rfl⟩
  uniqueExports := by simp [probe]
  singleTable := Nat.zero_le _
  singleMemory := Nat.zero_le _

example (width : FloatType) (left right : BitVec width.width) :
    (probe width left right).toCore.funcs.map (fun fn => fn.body) =
      [[.floatConst width left, .floatConst width right, .floatBinOp width .add,
        .floatConst width left, .floatConst width right, .floatRelOp width .eq,
        .floatConst width left, .convert (.truncSat width .i32 .signed)]] := rfl

private def runProbe (width : FloatType) (left right : BitVec width.width) : Option Result := do
  let prepared ← Lime1.Execution.prepare? ({} : Lime1.Execution.Store Unit) (probe width left right) []
  let exported ← prepared.module.exports.find? (fun entry => entry.name == "probe")
  let .func address := exported.value | none
  match (Lime1.Execution.run 16 ⟨prepared.store, { module := prepared.module }, [.invoke address]⟩).2 with
  | .returned result => some result
  | _ => none

private def returned (width : FloatType) (sum : BitVec width.width) (equal truncated : BitVec 32) : Option Result :=
  some (.values [Value.float width sum, Value.int .i32 equal, Value.int .i32 truncated])

example : runProbe .f32 0x3fc00000 0x40200000 = returned .f32 0x40800000 0 1 := by decide +kernel
example : runProbe .f64 0x3ff8000000000000 0x4004000000000000 = returned .f64 0x4010000000000000 0 1 := by
  decide +kernel
example : runProbe .f32 0x80000000 0x80000000 = returned .f32 0x80000000 1 0 := by decide +kernel
example : runProbe .f64 0x8000000000000000 0x8000000000000000 = returned .f64 0x8000000000000000 1 0 := by
  decide +kernel
example : runProbe .f32 0x80000000 0 = returned .f32 0 1 0 := by decide +kernel
example : runProbe .f64 0x8000000000000000 0 = returned .f64 0 1 0 := by decide +kernel
example : runProbe .f32 0x7fc00001 0x3f800000 = returned .f32 0x7fc00000 0 0 := by decide +kernel
example : runProbe .f64 0x7ff8000000000001 0x3ff0000000000000 = returned .f64 0x7ff8000000000000 0 0 := by
  decide +kernel

private def addRedex (width : FloatType) (left right : BitVec width.width) : List Lime1.Execution.Admin :=
  [.source (.floatConst width left), .source (.floatConst width right), .source (.floatBinOp width .add)]

example : Lime1.Execution.PureStep [] (addRedex .f32 0x7fc00001 0x3f800000)
      [.source (.floatConst .f32 0x7fc00000)] ∧
    Lime1.Execution.PureStep [] (addRedex .f32 0x7fc00001 0x3f800000)
      [.source (.floatConst .f32 0x7fc00002)] :=
  ⟨.floatBinary .f32 .add _ _ _ (by decide), .floatBinary .f32 .add _ _ _ (by decide)⟩

example : Lime1.Execution.PureStep [] (addRedex .f64 0x7ff8000000000001 0x3ff0000000000000)
      [.source (.floatConst .f64 0x7ff8000000000000)] ∧
    Lime1.Execution.PureStep [] (addRedex .f64 0x7ff8000000000001 0x3ff0000000000000)
      [.source (.floatConst .f64 0x7ff8000000000002)] :=
  ⟨.floatBinary .f64 .add _ _ _ (by decide), .floatBinary .f64 .add _ _ _ (by decide)⟩

end Silmaril.Tests.LimeFloat
