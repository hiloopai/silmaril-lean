module

public import Silmaril.Wasm.Auto.EGraph.Thms
public import Silmaril.Wasm.Auto.Rules.Thms

/-! # E-graph certificate checker: tests

Hand-checked certificates (as `wasm-egraph prove` prints them) and the library text that
`tools/wasm-egraph/rules.sexp` must match.
-/

namespace Silmaril.Wasm.Auto.EGraph.Tests

open Silmaril.Wasm Silmaril.Wasm.Auto.EGraph Silmaril.Wasm.Auto.Rules

/-- `local.get 1; local.get 0; i32.const 0; i32.add; i32.mul` ≡ `local.get 0; local.get 1; i32.mul`. -/
theorem mul_add0 :
    SegEquiv [.i32, .i32]
      (compileL [(.bin .i32 .mul (.lget 1) (.bin .i32 .add (.lget 0) (.const .i32 0)))])
      (compileL [(.bin .i32 .mul (.lget 0) (.lget 1))]) :=
  segEquiv_of_checkEqL [[.rw 4 true [] [], .rw 20 true [0] []]] library_sound (by decide +kernel)

/-- The same statement on the literal instruction sequences. -/
example :
    SegEquiv [.i32, .i32]
      [.localGet (lidx 1), .localGet (lidx 0), .intConst .i32 (BitVec.ofNat _ 0),
        .intBinOp .i32 .add, .intBinOp .i32 .mul]
      [.localGet (lidx 0), .localGet (lidx 1), .intBinOp .i32 .mul] :=
  mul_add0

/-- A wrong certificate is rejected (the rule does not match). -/
example : checkEqL [.i32] library [.bin .i32 .add (.lget 0) (.const .i32 1)] [.lget 0]
    [[.rw 20 true [] []]] = false := by decide +kernel

/-- A refinement step cannot be used as an equation. -/
example : checkEqL [.i32] library [.bin .i32 .sub (.lget 0) (.lget 0)] [.const .i32 0]
    [[.rw 78 true [] []]] = false := by decide +kernel

/-- … but it gives a refinement. -/
theorem sub_self_ref :
    SegRefines [.i32] (compileL [.bin .i32 .sub (.lget 0) (.lget 0)]) (compileL [.const .i32 0]) :=
  segRefines_of_checkRefL [[.rw 78 true [] []]] library_sound (by decide +kernel)

/-- Constant folding, then a neutral rule: `x + (2 - 2)` ≡ `x`. -/
theorem fold_then_add0 :
    SegEquiv [.i64]
      (compileL [.bin .i64 .add (.lget 0) (.bin .i64 .sub (.const .i64 2) (.const .i64 2))])
      (compileL [.lget 0]) :=
  segEquiv_of_checkEqL [[.fold [1], .rw 21 true [] []]] library_sound (by decide +kernel)

/-- A backward step that introduces a variable: `0 ⟶ x - x` for a total `x`, with the
binding supplied by the certificate. -/
theorem zero_sub_self :
    SegEquiv [.i32] (compileL [.const .i32 0]) (compileL [.bin .i32 .sub (.lget 0) (.lget 0)]) :=
  segEquiv_of_checkEqL [[.rw 100 false [] [(0, .lget 0)]]] library_sound (by decide +kernel)

/-- … which a division blocks: `x / y` may trap, so `x / y - x / y` is not `0`. -/
example : checkEqL [.i32, .i32] library [.const .i32 0]
    [.bin .i32 .sub (.bin .i32 (.div .unsigned) (.lget 0) (.lget 1))
      (.bin .i32 (.div .unsigned) (.lget 0) (.lget 1))]
    [[.rw 100 false [] [(0, .bin .i32 (.div .unsigned) (.lget 0) (.lget 1))]]] = false := by
  decide +kernel

/-- The rule names in library order (index `2k` at `i32`, `2k + 1` at `i64`). -/
example : (library.map Rule.name).length = 148 := by decide +kernel

end Silmaril.Wasm.Auto.EGraph.Tests
