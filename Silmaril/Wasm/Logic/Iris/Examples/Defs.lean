module

public import Silmaril.Wasm.Execution.Core.Step

/-!
# Worked examples for the Iris logic of Wasm Core 3.0: programs

Small Wasm 3.0 programs, as administrative code, used by
`Silmaril.Wasm.Logic.Iris.Examples.Thms`:

* `storeLoad x p c`: `i64.const p; i32.const c; i32.store x; i64.const p; i32.load x`
  on a memory64 memory `x`;
* `twoMems x₁ x₂ p c₁ c₂`: stores `c₁` into memory `x₁` and `c₂` into memory `x₂`
  at the same address (multiple memories), then loads from `x₁`;
* `bump x`: `global.get x; i32.const 1; i32.add; global.set x`;
* `arrLen x v`: `array.new_fixed x 2` on two copies of `v`, then `array.len`;
* `structRead x v`: `struct.new x` on one field `v`, then `struct.get x 0`;
* `throwCode x`: `throw x` (a tag without parameters);
* `grow x n`: `i64.const n; memory.grow x` on a memory64 memory.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.IrisWasm.Examples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- An `i64` address. -/
abbrev addr64 (p : BitVec 64) : Val := .num ⟨.int .i64, p⟩

/-- `i64.const p; i32.const c; i32.store x; i64.const p; i32.load x`. -/
def storeLoad (x : MemIdx) (p : BitVec 64) (c : BitVec 32) : List Admin :=
  vals [addr64 p, .i32 c] ++ (.plain (.intStore .i32 none x memarg0) ::
    (vals [addr64 p] ++ [.plain (.intLoad .i32 none x memarg0)]))

/-- Two stores at the same address of two memories, then a load from the first. -/
def twoMems (x₁ x₂ : MemIdx) (p : BitVec 64) (c₁ c₂ : BitVec 32) : List Admin :=
  vals [addr64 p, .i32 c₁] ++ (.plain (.intStore .i32 none x₁ memarg0) ::
    (vals [addr64 p, .i32 c₂] ++ (.plain (.intStore .i32 none x₂ memarg0) ::
    (vals [addr64 p] ++ [.plain (.intLoad .i32 none x₁ memarg0)]))))

/-- `global.get x; i32.const 1; i32.add; global.set x`. -/
def bump (x : GlobalIdx) : List Admin :=
  .plain (.globalGet x) :: .plain (.intConst .i32 1) :: .plain (.intBinOp .i32 .add) ::
    [.plain (.globalSet x)]

/-- A two-element array of `v`, then its length. -/
def arrLen (x : TypeIdx) (v : Val) : List Admin :=
  vals [v, v] ++ (.plain (.arrayNewFixed x ⟨2, by decide⟩) :: [.plain .arrayLen])

/-- A structure with the one field `v`, then that field. -/
def structRead (x : TypeIdx) (v : Val) : List Admin :=
  vals [v] ++ (.plain (.structNew x) :: [.plain (.structGet none x ⟨0, by decide⟩)])

/-- `throw x`. -/
def throwCode (x : TagIdx) : List Admin := [.plain (.throw x)]

/-- `i64.const n; memory.grow x`. -/
def grow (x : MemIdx) (n : BitVec 64) : List Admin :=
  vals [addr64 n] ++ [.plain (.memoryGrow x)]

end Silmaril.Wasm.Logic.IrisWasm.Examples
