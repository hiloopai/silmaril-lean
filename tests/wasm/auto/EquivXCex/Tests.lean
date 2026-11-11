module

public import Silmaril.Wasm.Auto.EquivXCex.Thms
public import tests.wasm.auto.EquivXBench.Defs
public import tests.wasm.auto.FrontBench.Defs

/-!
# Counterexamples for the extended checker: regression tests

Each refutation is a theorem: the counterexample (found by `findCexX`, checked here by `decide`)
refutes the equivalence through `not_segEquivX_of_cex` / `not_outEquivX_of_cex`.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.EquivXCex.Tests

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Auto.Equiv Silmaril.Wasm.Auto.EquivXCex Silmaril.Wasm.Auto.EquivXBench

/-- The reordered `global.set` of `EquivXBench.store_global_reordered`: with an empty memory the
store traps, after the global was set on the left and before it is set on the right. -/
def gsetA : List Instr :=
  [.localGet ⟨1⟩, .globalSet ⟨0⟩, .localGet ⟨0⟩, .globalGet ⟨0⟩, .intStore .i64 none ⟨0⟩ ⟨0, 8⟩]
def gsetB : List Instr :=
  [.localGet ⟨0⟩, .localGet ⟨1⟩, .localTee ⟨1⟩, .intStore .i64 none ⟨0⟩ ⟨0, 8⟩,
    .localGet ⟨1⟩, .globalSet ⟨0⟩]

theorem gset_search : findCexX true [.i32, .i64] [] [.i64] true gsetA gsetB =
    some ([0, 256, 305419896], 0) := by decide

theorem store_global_reordered_refuted : ¬ SegEquivX [.i32, .i64] [] [.i64] true gsetA gsetB :=
  not_segEquivX_of_cex [0, 256, 305419896] ByteArray.empty (by decide)

/-- **`requant` v0 (zero point added in 32 bits) against the fixed kernel**: refuted
by the extended checker's own differential testing (all inputs `2^31 - 1`). -/
theorem requantV0_not_outEquivX : ¬ OutEquivX requantLocals [] [] false
    (bodyOf Silmaril.Wasm.Auto.FrontBench.requantV0) (bodyOf Silmaril.Wasm.Auto.FrontBench.requantFixed) :=
  not_outEquivX_of_cex (List.replicate 10 2147483647) ByteArray.empty (by decide)

/-- A dropped division is not an equivalence (it traps for `y = 0`); it is a refinement
(`EquivXBench.drop_div_refines`). -/
theorem drop_div_not_equiv : ¬ SegEquivX [.i32, .i32] [] [] false
    [.localGet ⟨0⟩, .localGet ⟨1⟩, .intBinOp .i32 (.div .unsigned), .drop, .intConst .i32 0]
    [.intConst .i32 0] :=
  not_segEquivX_of_cex [0, 0] ByteArray.empty (by decide)

/-- A load at a different offset than the store does not read the stored value (32 zero bytes,
address `0`). -/
theorem load_other_offset : ¬ SegEquivX [.i32] [] [] true
    [.localGet ⟨0⟩, .intConst .i32 5, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩, .localGet ⟨0⟩,
      .intLoad .i32 none ⟨0⟩ ⟨0, 4⟩]
    [.localGet ⟨0⟩, .intConst .i32 5, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩, .intConst .i32 5] :=
  not_segEquivX_of_cex [0] (probeMems.getD 1 ByteArray.empty) (by decide)

/-- info: 'Silmaril.Wasm.Auto.EquivXCex.Tests.requantV0_not_outEquivX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms requantV0_not_outEquivX

/--
info: 'Silmaril.Wasm.Auto.EquivXCex.Tests.store_global_reordered_refuted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms store_global_reordered_refuted

end Silmaril.Wasm.Auto.EquivXCex.Tests
