module

public import Silmaril.Wasm.Logic.Core.Thms

/-!
# `i32` instructions as `BitVec 32` operations

Equations by `rfl` used by the generated (`tactic+script`, `all-in`) solutions
and available to hand-written ones: tests and comparisons as `bool32` of a
`Bool` written with `BitVec`'s own operations (`==`, `slt`, `sle`, `ult`, `ule`),
and the signed shift. Stated at `BitVec 32` (not `BitVec IntType.i32.width`),
so that `cases h : (x == 0)` and the like find their occurrences. A Silmaril
addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.Ops

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Logic.Core

variable (x y : BitVec 32)

theorem eqz32 : intTestOp .i32 .eqz x = bool32 (x == 0) := rfl
theorem eq32 : intRelOp .i32 .eq x y = bool32 (x == y) := rfl
theorem ne32 : intRelOp .i32 .ne x y = bool32 (x != y) := rfl
theorem ltS32 : intRelOp .i32 (.lt .signed) x y = bool32 (x.slt y) := rfl
theorem gtS32 : intRelOp .i32 (.gt .signed) x y = bool32 (y.slt x) := rfl
theorem leS32 : intRelOp .i32 (.le .signed) x y = bool32 (x.sle y) := rfl
theorem geS32 : intRelOp .i32 (.ge .signed) x y = bool32 (y.sle x) := rfl
theorem ltU32 : intRelOp .i32 (.lt .unsigned) x y = bool32 (x.ult y) := rfl
theorem gtU32 : intRelOp .i32 (.gt .unsigned) x y = bool32 (y.ult x) := rfl
theorem leU32 : intRelOp .i32 (.le .unsigned) x y = bool32 (x.ule y) := rfl
theorem geU32 : intRelOp .i32 (.ge .unsigned) x y = bool32 (y.ule x) := rfl
theorem shrS32 : intBinOp .i32 (.shr .signed) x y =
    Except.ok (x.sshiftRight (y.toNat % 32)) := rfl

end Silmaril.WasmSpec.Ops
