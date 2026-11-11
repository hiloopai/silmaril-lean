module

public import Silmaril.Wasm.Auto.Equiv.Thms
public import tests.wasm.auto.EquivXBench.Defs

/-!
# The extended equivalence benchmark

Every entry is decided in the kernel (`decide`) by the checks of `Silmaril.Wasm.Auto.Equiv` and
turned into a theorem by their soundness theorems, so this module is a regression test with
pinned inputs (`Silmaril.Wasm.Auto.EquivXBench.Defs`). Timings:
`docs/projects/wasm-binaryen-tooling.md`.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.EquivXBench

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Auto.Equiv

/-! ## Unit cases -/

/-- `i32.wrap_i64 (i64.extend_i32_s x) = x`. -/
theorem wrap_extend : SegEquivX [.i32] [] [] false
    [.localGet ⟨0⟩, .convert (.extend .signed), .convert .wrap] [.localGet ⟨0⟩] :=
  segEquivX_of_checkX (by decide)

/-- `select` with equal branches, and with a constant condition. -/
theorem select_same : SegEquivX [.i32, .i32] [] [] false
    [.localGet ⟨0⟩, .localGet ⟨0⟩, .localGet ⟨1⟩, .select none, .intConst .i32 7,
      .localGet ⟨1⟩, .intConst .i32 1, .select none, .intBinOp .i32 .add]
    [.localGet ⟨0⟩, .intConst .i32 7, .intBinOp .i32 .add] :=
  segEquivX_of_checkX (by decide)

/-- A dropped division may trap: removing it is a **refinement**, not an equivalence. -/
theorem drop_div_refines : SegRefinesX [.i32, .i32] [] [] false
    [.localGet ⟨0⟩, .localGet ⟨1⟩, .intBinOp .i32 (.div .unsigned), .drop, .intConst .i32 0]
    [.intConst .i32 0] :=
  segRefinesX_of_refinesX (by decide)

/-- A load whose value is dropped: removing it is a refinement (memory `0`). -/
theorem drop_load_refines : SegRefinesX [.i32] [] [] true
    [.localGet ⟨0⟩, .intLoad .i32 none ⟨0⟩ ⟨0, 0⟩, .drop] [] :=
  segRefinesX_of_refinesX (by decide)

/-- A global round trip before a store: equal stores, also when the store traps. -/
theorem store_global : SegEquivX [.i32, .i64] [] [.i64] true
    [.localGet ⟨1⟩, .globalSet ⟨0⟩, .localGet ⟨0⟩, .globalGet ⟨0⟩, .intStore .i64 none ⟨0⟩ ⟨0, 8⟩]
    [.localGet ⟨1⟩, .localTee ⟨1⟩, .globalSet ⟨0⟩, .localGet ⟨0⟩, .localGet ⟨1⟩,
      .intStore .i64 none ⟨0⟩ ⟨0, 8⟩] :=
  segEquivX_of_checkX (by decide)

/-- Moving the `global.set` after the store is **not** an equivalence: if the store traps, the
global differs in the trap state. -/
theorem store_global_reordered :
    checkX [.i32, .i64] [] [.i64] true
      [.localGet ⟨1⟩, .globalSet ⟨0⟩, .localGet ⟨0⟩, .globalGet ⟨0⟩, .intStore .i64 none ⟨0⟩ ⟨0, 8⟩]
      [.localGet ⟨0⟩, .localGet ⟨1⟩, .localTee ⟨1⟩, .intStore .i64 none ⟨0⟩ ⟨0, 8⟩,
        .localGet ⟨1⟩, .globalSet ⟨0⟩] = false := by decide

/-! ## kernels -/

/-- **`requant` against Binaryen `-O2`** (translation validation): equal results in every
context (scratch locals ignored). -/
theorem requant_binaryenO2 : OutEquivX requantLocals [] [] false
    (bodyOf Silmaril.Wasm.Auto.FrontBench.requantFixed) (bodyOf requantO2) :=
  outEquivX_of_checkOutX (by decide)

/-- **`adler8` against Binaryen `-O2`**: equal globals, memory, results and trap behaviour. -/
theorem adler8_binaryenO2 : SegEquivX [.i32] [] [.i32, .i32] true (bodyOf adler8) (bodyOf adler8O2) :=
  segEquivX_of_checkX (by decide)

/-- **`adler1x8` against Binaryen `-O2`** (results; the pointer local is scratch). -/
theorem adler1x8_binaryenO2 : OutEquivX [.i32] [] [.i32, .i32] true (bodyOf adler1x8) (bodyOf adler1x8O2) :=
  outEquivX_of_checkOutX (by decide)

/-- The offset form (`load8_u offset=k p`) and the incremented-pointer form (`load8_u (p + k)`)
are **not** decided equal: they differ when `p + k` wraps at `2^32` (the first traps, the second
reads address `p + k - 2^32`). -/
theorem adler8_vs_rolled_unknown :
    checkOutX [.i32] [] [.i32, .i32] true (bodyOf adler8) (bodyOf adler1x8) = false := by decide

/-- info: 'Silmaril.Wasm.Auto.EquivXBench.requant_binaryenO2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms requant_binaryenO2

/-- info: 'Silmaril.Wasm.Auto.EquivXBench.adler8_binaryenO2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms adler8_binaryenO2

/-- info: 'Silmaril.Wasm.Auto.EquivXBench.drop_div_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms drop_div_refines

end Silmaril.Wasm.Auto.EquivXBench
