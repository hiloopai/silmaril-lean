module

public import Silmaril.Wasm.Execution.MemRep.Sim.Thms

/-! # The interpreter's memory family on `KMem` (`decide +kernel`)

`memoryStep?` runs directly on a `Store Unit KMem`: a store then a load of an `i32`, and a
`memory.grow` then `memory.size`, checked in the kernel. By `memoryStep?_toBytes` each step is,
through `toBytes`, the step on the `ByteArray` store.

The whole interpreter also runs on `KMem`: `runI` executes 64 scattered `i32.store`s into a
1 MiB memory and a load (194 steps), checked in the kernel (`scatterRun`). By `runI_toBytes`
the run, read through `toBytes`, is `runI` on the `ByteArray` configuration, which the kernel
cannot evaluate at this size (`docs/projects/wasm-memrep.md`).
-/

@[expose] public section

namespace Silmaril.Wasm.Execution.MemRepSimExamples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.SingleThreaded.Exec

/-- One page of `KMem` memory, memory 0 of the frame's module. -/
def store : Store Unit KMem := { mems := [⟨⟨.i32, ⟨1, none⟩⟩, MemRep.zeros 65536⟩] }
def frame : Frame := { module := { mems := [0] } }
def arg : MemArg := ⟨0, 0⟩

/-- The `i32` result of the last step, if it pushed exactly one. -/
def result? (c : Config Unit KMem) : Option Nat :=
  match c.code with
  | [.plain (.intConst .i32 v)] => some v.toNat
  | _ => none

/-- `i32.store` of `0x01020304` at address 100, then `i32.load` from 100. -/
def storeLoad : Option Nat := do
  let (_, c) ← memoryStep? neverFail store frame [.i32 100, .i32 0x01020304]
    (.plain (.intStore .i32 none ⟨0⟩ arg))
  let (_, c) ← memoryStep? neverFail c.store frame [.i32 100] (.plain (.intLoad .i32 none ⟨0⟩ arg))
  result? c

example : storeLoad = some 0x01020304 := by decide +kernel

/-- `memory.grow 1` (returns the old size, 1), then `memory.size`. -/
def growSize : Option (Nat × Nat) := do
  let (_, c) ← memoryStep? neverFail store frame [.i32 1] (.plain (.memoryGrow ⟨0⟩))
  let old ← result? c
  let (_, c) ← memoryStep? neverFail c.store frame [] (.plain (.memorySize ⟨0⟩))
  return (old, ← result? c)

example : growSize = some (1, 2) := by decide +kernel

/-! ## The interpreter on `KMem` -/

/-- An `i32` constant. -/
def i32 (n : Nat) : Admin := .plain (.intConst .i32 (BitVec.ofNat 32 n))

/-- 64 `i32.store`s of `k + 1` at scattered addresses below `size`, then a load of the last. -/
def scatterCode (size : Nat) : List Admin :=
  ((List.range 64).flatMap fun k =>
    [i32 ((k * 16411) % (size - 4)), i32 (k + 1), .plain (.intStore .i32 none ⟨0⟩ arg)]) ++
  [i32 ((63 * 16411) % (size - 4)), .plain (.intLoad .i32 none ⟨0⟩ arg)]

/-- A configuration over `KMem`: one 16-page (1 MiB) memory and `scatterCode`. -/
def scatterConfig : Config Unit KMem :=
  ⟨{ mems := [⟨⟨.i32, ⟨16, none⟩⟩, MemRep.zeros 1048576⟩] }, frame, scatterCode 1048576⟩

/-- Run the interpreter with fuel 300: the loaded value and whether the run stopped. -/
def scatterRun : Option Nat × Bool :=
  let r := runI neverFail 300 scatterConfig
  (result? r.1, r.2)

example : scatterRun = (some 64, true) := by decide +kernel

end Silmaril.Wasm.Execution.MemRepSimExamples
