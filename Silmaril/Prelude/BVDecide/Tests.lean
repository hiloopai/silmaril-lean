module

import Silmaril.Prelude.BVDecide.Defs
meta import Silmaril.Prelude.BVDecide.Defs

/-!
# Tests for `bv_decide_kernel`

Goals that `bv_normalize` closes are proved with standard axioms only, and the
tactic fails, rather than adding an axiom, on goals that need the SAT stage of
`bv_decide`. The positive cases include the lane and byte-image identities of
`Silmaril.X86.Float.State`.
-/

public section

namespace Silmaril.Prelude.BVDecide.Tests

theorem setLane32 (v : BitVec 128) (x : BitVec 32) :
    (v.extractLsb' 32 96 ++ x : BitVec 128).extractLsb' 0 32 = x := by bv_decide_kernel

theorem zeroLane64 (x : BitVec 64) : (x.setWidth 128).extractLsb' 0 64 = x := by
  bv_decide_kernel

theorem le32 (v : BitVec 32) :
    v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v := by
  bv_decide_kernel

theorem addSub (x y : BitVec 64) : x + y - y = x := by bv_decide_kernel

theorem withHyp (x y : BitVec 8) (h : x = y) : x + 0 = y := by bv_decide_kernel

/-- info: 'Silmaril.Prelude.BVDecide.Tests.setLane32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms setLane32

/-- info: 'Silmaril.Prelude.BVDecide.Tests.le32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms le32

/-! Goals that need SAT are rejected: `bv_decide` would prove them through a
`_native.bv_decide.ax_…` axiom. -/

/--
error: bv_decide_kernel: `bv_normalize` does not close the goal, so `bv_decide` would need the SAT solver and a native-evaluation axiom; run `bv_normalize` to see what remains
-/
#guard_msgs in
example (x y : BitVec 32) : (x ^^^ y) ^^^ y = x := by bv_decide_kernel

/--
error: bv_decide_kernel: `bv_normalize` does not close the goal, so `bv_decide` would need the SAT solver and a native-evaluation axiom; run `bv_normalize` to see what remains
-/
#guard_msgs in
example (x y : BitVec 8) : x * y = y * x := by bv_decide_kernel

/-! The axiom check reports anything outside the standard set. -/

open Lean in
/-- info: #[`sorryAx] -/
#guard_msgs in
#eval do
  nonstandardAxioms (.const ``sorryAx [.zero])

open Lean in
/-- info: #[] -/
#guard_msgs in
#eval do
  nonstandardAxioms (.const ``setLane32 [])

/-! `kernelFallback` reports `needsSat` and leaves the goal as it was, so a
caller can choose another route (here exhaustive `decide`). -/

open Lean Elab Tactic in
example : ∀ x y : BitVec 4, x * y = y * x := by
  run_tac do
    let r ← kernelFallback (← getMainGoal)
    unless r matches .needsSat do throwError "expected needsSat"
  decide

/-! Names of the axioms `bv_decide` adds are recognized (recognition only). -/

#guard isBvDecideNativeAxiom ((`Foo.bar).str "_native" |>.str "bv_decide" |>.str "ax_1_5")
#guard !isBvDecideNativeAxiom ((`Foo.bar).str "_native" |>.str "other" |>.str "ax_1")
#guard !isBvDecideNativeAxiom `propext
open Lean in
/-- info: false -/
#guard_msgs in
#eval isBvDecideNativeStatement ``propext

#guard nativeEvaluatedConst == `Std.Tactic.BVDecide.Reflect.verifyBVExpr

end Silmaril.Prelude.BVDecide.Tests
