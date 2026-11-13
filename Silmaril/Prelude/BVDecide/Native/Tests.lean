module

import Silmaril.Prelude.BVDecide.Native.Defs
meta import Silmaril.Prelude.BVDecide.Native.Defs

/-!
# Tests for `sil_bv_decide`

The registration matches the reviewed procedure. Goals that `bv_normalize` closes are proved
by the kernel route in every profile. Goals that need SAT fail in the default and paranoid
profiles: `lean.std.bv_decide.verifyBVExpr` is not in the `default` set, and there is no kernel
route. The native path (profile `local`), and the rejection of unrecorded or wrong native
axioms, are tested in `tests/trust/BVDecideNative.lean`, outside the library, so that the
library holds no native axiom.
-/

public section

namespace Silmaril.Prelude.BVDecide.NativeTests

/-- info: none -/
#guard_msgs in
#eval show Lean.CoreM _ from registrationProblem

theorem addSub (x y : BitVec 64) : x + y - y = x := by sil_bv_decide

set_option silmaril.trust.profile "paranoid" in
theorem addSubParanoid (x y : BitVec 64) : x + y - y = x := by sil_bv_decide

/-- info: 'Silmaril.Prelude.BVDecide.NativeTests.addSub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms addSub

/--
error: sil_bv_decide: the goal needs SAT, which has no kernel-checked route, and lean.std.bv_decide.verifyBVExpr is not allowed natively here (profile default)
-/
#guard_msgs in
example (x y : BitVec 8) : x * y = y * x := by sil_bv_decide

/--
error: sil_bv_decide: the goal needs SAT, which has no kernel-checked route, and lean.std.bv_decide.verifyBVExpr is not allowed natively here (profile paranoid)
-/
#guard_msgs in
set_option silmaril.trust.profile "paranoid" in
example (x y : BitVec 8) : x * y = y * x := by sil_bv_decide

end Silmaril.Prelude.BVDecide.NativeTests
