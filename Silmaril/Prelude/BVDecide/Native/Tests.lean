module

import Silmaril.Prelude.BVDecide.Native.Defs
meta import Silmaril.Prelude.BVDecide.Native.Defs

/-!
# Tests for `bv_decide_policy`

The registration matches the reviewed procedure. Goals that `bv_normalize` closes are proved
by the kernel route in every profile. Goals that need SAT fail in the default and paranoid
profiles: `lean.std.bv_decide.verifyBVExpr` is not in the `default` set, and there is no kernel
route. The native path (profile `local`) is not exercised here, so that the library holds no
native axiom; docs/bv-decide-trust.md records how it was checked.
-/

public section

namespace Silmaril.Prelude.BVDecide.NativeTests

/-- info: none -/
#guard_msgs in
#eval show Lean.CoreM _ from registrationProblem

theorem addSub (x y : BitVec 64) : x + y - y = x := by bv_decide_policy

set_option silmaril.trust.profile "paranoid" in
theorem addSubParanoid (x y : BitVec 64) : x + y - y = x := by bv_decide_policy

/-- info: 'Silmaril.Prelude.BVDecide.NativeTests.addSub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms addSub

/--
error: bv_decide_policy: the goal needs SAT, which has no kernel-checked route, and lean.std.bv_decide.verifyBVExpr is not allowed natively here (profile default)
-/
#guard_msgs in
example (x y : BitVec 8) : x * y = y * x := by bv_decide_policy

/--
error: bv_decide_policy: the goal needs SAT, which has no kernel-checked route, and lean.std.bv_decide.verifyBVExpr is not allowed natively here (profile paranoid)
-/
#guard_msgs in
set_option silmaril.trust.profile "paranoid" in
example (x y : BitVec 8) : x * y = y * x := by bv_decide_policy

end Silmaril.Prelude.BVDecide.NativeTests
