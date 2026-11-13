module

public import Silmaril.Prelude.BVDecide.Edge
public import Silmaril.Prelude.Trust.Policy.Defs

/-! # `sil_bv_decide` under each profile

`lean.std.bv_decide.verifyBVExpr` is in no default trust set, so the default profile uses the
kernel-only fallback, and the `local` profile (the scope's `max`) runs the SAT stage natively.
-/

@[expose] public section

set_option silmaril.trust.profile "default"

namespace Silmaril.Prelude.BVDecide.EdgeExamples

/-- `bv_normalize` closes it: a kernel-checked proof in every profile. -/
theorem addSub (x y : BitVec 64) : x + y - y = x := by sil_bv_decide

-- Needs SAT: native under `local`, with one verified `bv_decide` axiom.
set_option silmaril.trust.profile "local" in
theorem mulComm (x y : BitVec 8) : x * y = y * x := by sil_bv_decide

/--
error: sil_bv_decide: lean.std.bv_decide.verifyBVExpr may not run natively in Silmaril.Prelude.BVDecide.EdgeExamples under profile default, and bv_normalize alone does not close the goal (it needs the SAT stage)
-/
#guard_msgs in
example (x y : BitVec 8) : x * y = y * x := by sil_bv_decide

set_option silmaril.trust.profile "local" in
/--
info: {"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.Prelude.BVDecide.EdgeExamples.addSub","dep_native":[],"elaborated_profiles":["default"],"kind":"audit","module":"Silmaril.Prelude.BVDecide.EdgeExamples","native_axioms":[],"own_native":[],"profile":"local","schema":"silmaril.trust.v1","unverified_native":[],"violations":[]}
{"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.Prelude.BVDecide.EdgeExamples.mulComm","dep_native":[],"elaborated_profiles":["local"],"kind":"audit","module":"Silmaril.Prelude.BVDecide.EdgeExamples","native_axioms":["_private.Silmaril.Prelude.BVDecide.EdgeExamples.0.Silmaril.Prelude.BVDecide.EdgeExamples.mulComm._native.bv_decide.ax_1_5"],"own_native":["lean.std.bv_decide.verifyBVExpr"],"profile":"local","schema":"silmaril.trust.v1","unverified_native":[],"violations":[]}
-/
#guard_msgs in
trust_audit addSub mulComm

end Silmaril.Prelude.BVDecide.EdgeExamples
