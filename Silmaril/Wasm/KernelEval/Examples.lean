module

public import Silmaril.Wasm.KernelEval.Defs

@[expose] public section

/-!
# Kernel evaluation of a small Wasm subset: example programs

Loops in the shape compilers emit (a `block`/`loop` pair with a `br_if` exit), used by the
tests (`Silmaril.Wasm.KernelEval.Tests`) and the benchmarks (`benchmarks/wasm-kernel-eval`).
Each is the body of a function; locals `0 …` are as listed.

A Silmaril addition.
-/

namespace Silmaril.Wasm.KernelEval.Examples

open Instr BinOp

/-- `for (i = 0; i < n; i++) acc += i; return acc` with locals `n, i, acc`. -/
def sumTo : List Instr :=
  [ block 0 [ loop [
      localGet 1, localGet 0, bin ltU, eqz, brIf 1,
      localGet 2, localGet 1, bin add, localSet 2,
      localGet 1, const 1, bin add, localSet 1,
      br 0 ] ],
    localGet 2 ]

/-- Locals of `sumTo n`. -/
def sumToLocals (n : Nat) : List (BitVec 32) := [BitVec.ofNat 32 n, 0, 0]

/-- `for (i = 0; i < n; i++) mem32[i] = n - i;` then insertion-sort `mem32[0 … n)` and return
`mem32[0] + mem32[n-1]`. Locals `n, i, j, key, t`. -/
def fillSort : List Instr :=
  [ -- fill
    block 0 [ loop [
      localGet 1, localGet 0, bin ltU, eqz, brIf 1,
      localGet 1, const 4, bin mul, localGet 0, localGet 1, bin sub, store 0,
      localGet 1, const 1, bin add, localSet 1, br 0 ] ],
    -- for (i = 1; i < n; i++)
    const 1, localSet 1,
    block 0 [ loop [
      localGet 1, localGet 0, bin ltU, eqz, brIf 1,
      -- key = mem[i]; j = i
      localGet 1, const 4, bin mul, load 0, localSet 3,
      localGet 1, localSet 2,
      -- while (j > 0 && mem[j-1] > key) { mem[j] = mem[j-1]; j-- }
      block 0 [ loop [
        localGet 2, eqz, brIf 1,
        localGet 3, localGet 2, const 1, bin sub, const 4, bin mul, load 0, localTee 4,
        bin ltU, eqz, brIf 1,
        localGet 2, const 4, bin mul, localGet 4, store 0,
        localGet 2, const 1, bin sub, localSet 2, br 0 ] ],
      localGet 2, const 4, bin mul, localGet 3, store 0,
      localGet 1, const 1, bin add, localSet 1, br 0 ] ],
    const 0, load 0, localGet 0, const 1, bin sub, const 4, bin mul, load 0, bin add ]

/-- Locals of `fillSort n`. -/
def fillSortLocals (n : Nat) : List (BitVec 32) := [BitVec.ofNat 32 n, 0, 0, 0, 0]

/-- A zeroed list memory of `n` bytes. -/
def listZeros (n : Nat) : ListMem := ⟨List.replicate n 0⟩

end Silmaril.Wasm.KernelEval.Examples
