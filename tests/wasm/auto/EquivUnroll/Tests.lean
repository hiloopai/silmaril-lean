module

public import Silmaril.Wasm.Auto.EquivUnroll.Thms

/-!
# Loop unrolling: tests

Loops with a constant trip count against their unrolled, simplified forms: decided in the kernel
by `checkXU` and proved by `segEquivXN_of_checkXU`.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.EquivUnroll.Tests

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Auto.Equiv Silmaril.Wasm.Auto.EquivUnroll

/-- `i = 0; do { x = x + x; i++ } while (i < 3)`. -/
def doubling : List Instr :=
  [.intConst .i32 0, .localSet ⟨1⟩,
    .loop .empty [.localGet ⟨0⟩, .localGet ⟨0⟩, .intBinOp .i32 .add, .localSet ⟨0⟩,
      .localGet ⟨1⟩, .intConst .i32 1, .intBinOp .i32 .add, .localTee ⟨1⟩, .intConst .i32 3,
      .intRelOp .i32 (.lt .signed), .brIf ⟨0⟩]]

/-- `x = x << 3; i = 3`. -/
def shifted : List Instr :=
  [.localGet ⟨0⟩, .intConst .i32 3, .intBinOp .i32 .shl, .localSet ⟨0⟩, .intConst .i32 3,
    .localSet ⟨1⟩]

/-- **A loop against its closed form** (three iterations, `x + x` doubled thrice = `x << 3`). -/
theorem doubling_unrolled : SegEquivXN [.i32, .i32] [] [] false doubling shifted :=
  segEquivXN_of_checkXU (fuel := 100) (by decide)

/-- `s = 0; i = 0; do { s += p[i]; i++ } while (i <u 4)` (bytes, memory `0`). -/
def sum4 : List Instr :=
  [.intConst .i32 0, .localSet ⟨1⟩, .intConst .i32 0, .localSet ⟨2⟩,
    .loop .empty [.localGet ⟨2⟩, .localGet ⟨0⟩, .localGet ⟨1⟩, .intBinOp .i32 .add,
      .intLoad .i32 (some (.i8, .unsigned)) ⟨0⟩ ⟨0, 0⟩, .intBinOp .i32 .add, .localSet ⟨2⟩,
      .localGet ⟨1⟩, .intConst .i32 1, .intBinOp .i32 .add, .localTee ⟨1⟩, .intConst .i32 4,
      .intRelOp .i32 (.lt .unsigned), .brIf ⟨0⟩]]

/-- One unrolled iteration `k`: `s += p[k]; i = k + 1`. -/
def sumStep (k : Nat) : List Instr :=
  [.localGet ⟨2⟩, .localGet ⟨0⟩, .intConst .i32 (BitVec.ofNat 32 k), .intBinOp .i32 .add,
    .intLoad .i32 (some (.i8, .unsigned)) ⟨0⟩ ⟨0, 0⟩, .intBinOp .i32 .add, .localSet ⟨2⟩,
    .intConst .i32 (BitVec.ofNat 32 (k + 1)), .localSet ⟨1⟩]

/-- The unrolled sum (what an unroller emits: the counter and the sum updated at every step, so
that the trap states of the four loads agree). -/
def sum4Unrolled : List Instr :=
  [.intConst .i32 0, .localSet ⟨1⟩, .intConst .i32 0, .localSet ⟨2⟩] ++
    sumStep 0 ++ sumStep 1 ++ sumStep 2 ++ sumStep 3

/-- **A memory loop fully unrolled** (four iterations; the in-bounds guards and their trap states
coincide). -/
theorem sum4_unrolled : SegEquivXN [.i32, .i32, .i32] [] [] true sum4 sum4Unrolled :=
  segEquivXN_of_checkXU (fuel := 100) (by decide)

/-- info: 'Silmaril.Wasm.Auto.EquivUnroll.Tests.sum4_unrolled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sum4_unrolled

end Silmaril.Wasm.Auto.EquivUnroll.Tests
