module

public import Silmaril.Wasm.Auto.EquivLoop.Thms

/-!
# Loops with memory and globals: tests

The rolled Adler-32 byte loop of `the adler benchmark kernel` with the sums in
globals `0` (`a`) and `1` (`b`), the pointer in local `0` and the end in local `1`
(`do { a += *p; b += a; p++ } while (p < end)`), against a rescheduled body (load before the
global read, `local.set` then `local.get` instead of `local.tee`, the comparison flipped). The
bodies are decided by `checkX` (memory `0` and the globals included, trap states compared) and
lifted by `loopEquivX`, in both readings.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.EquivLoop.TestsX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Auto.Equiv Silmaril.Wasm.Auto.EquivLoop

/-- `a += *p; b += a; p++; p < end`. -/
def adlerByte : List Instr :=
  [.globalGet ⟨0⟩, .localGet ⟨0⟩, .intLoad .i32 (some (.i8, .unsigned)) ⟨0⟩ ⟨0, 0⟩,
    .intBinOp .i32 .add, .globalSet ⟨0⟩,
    .globalGet ⟨1⟩, .globalGet ⟨0⟩, .intBinOp .i32 .add, .globalSet ⟨1⟩,
    .localGet ⟨0⟩, .intConst .i32 1, .intBinOp .i32 .add, .localTee ⟨0⟩, .localGet ⟨1⟩,
    .intRelOp .i32 (.lt .unsigned)]

/-- The rescheduled body. -/
def adlerByte' : List Instr :=
  [.localGet ⟨0⟩, .intLoad .i32 (some (.i8, .unsigned)) ⟨0⟩ ⟨0, 0⟩, .globalGet ⟨0⟩,
    .intBinOp .i32 .add, .globalSet ⟨0⟩,
    .globalGet ⟨0⟩, .globalGet ⟨1⟩, .intBinOp .i32 .add, .globalSet ⟨1⟩,
    .localGet ⟨0⟩, .intConst .i32 1, .intBinOp .i32 .add, .localSet ⟨0⟩, .localGet ⟨1⟩,
    .localGet ⟨0⟩, .intRelOp .i32 (.gt .unsigned)]

/-- **The Adler-32 byte loop, rescheduled**: equivalent loops (memory and globals, both readings). -/
theorem adler_loop : LoopEquivI (XInv [.i32, .i32] [.i32, .i32] true) .empty
    (adlerByte ++ [.brIf ⟨0⟩]) (adlerByte' ++ [.brIf ⟨0⟩]) :=
  loopEquivX ⟨0⟩ Silmaril.Wasm.Auto.Equiv.noParams_empty (by decide) (by decide)

/-- info: 'Silmaril.Wasm.Auto.EquivLoop.TestsX.adler_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms adler_loop

end Silmaril.Wasm.Auto.EquivLoop.TestsX
