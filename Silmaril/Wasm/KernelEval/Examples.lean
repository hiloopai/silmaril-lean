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

/-- `for (i = 0; i < n; i++) mem32[i * stride] = i;` then return the sum of the same words.
Locals `n, stride, i, acc`: scattered accesses over a large memory. -/
def scatter : List Instr :=
  [ block 0 [ loop [
      localGet 2, localGet 0, bin ltU, eqz, brIf 1,
      localGet 2, localGet 1, bin mul, localGet 2, store 0,
      localGet 2, const 1, bin add, localSet 2, br 0 ] ],
    const 0, localSet 2,
    block 0 [ loop [
      localGet 2, localGet 0, bin ltU, eqz, brIf 1,
      localGet 3, localGet 2, localGet 1, bin mul, load 0, bin add, localSet 3,
      localGet 2, const 1, bin add, localSet 2, br 0 ] ],
    localGet 3 ]

/-- Locals of `scatter n stride`. -/
def scatterLocals (n stride : Nat) : List (BitVec 32) :=
  [BitVec.ofNat 32 n, BitVec.ofNat 32 stride, 0, 0]

section Sharing

variable {M : Type} [MemOps M]

/-- Store the words `1 … n` at `0, 4, …` (no-op where out of bounds). -/
def fillWords (m : M) : Nat → M
  | 0 => m
  | n + 1 => let m := fillWords m n; (MemOps.store m (4 * n) 4 (n + 1)).getD m

/-- **Many slightly different memories**: from one `base`, one variant per address in
`addrs`, each with one word written; all are kept, then each is checked to hold its own word
and the base's word at `probe`. -/
def sharingCheck (base : M) (addrs : List Nat) (probe : Nat) : Bool :=
  let vs := addrs.map fun a => (a, MemOps.store base a 4 (a + 1))
  let pb := MemOps.load base probe 4
  vs.all fun (a, v) => match v with
    | some m => MemOps.load m a 4 == some ((a + 1) % 2 ^ 32) && MemOps.load m probe 4 == pb
    | none => false

/-- `n` stores to a memory, one word each, `stride` apart, then a read of the last one. -/
def updates (m : M) (n stride : Nat) : Option Nat :=
  let rec go : Nat → M → M
    | 0, m => m
    | k + 1, m => go k ((MemOps.store m (k * stride) 4 k).getD m)
  MemOps.load (go n m) 0 4

end Sharing

/-- A zeroed list memory of `n` bytes. -/
def listZeros (n : Nat) : ListMem := ⟨List.replicate n 0⟩

end Silmaril.Wasm.KernelEval.Examples
