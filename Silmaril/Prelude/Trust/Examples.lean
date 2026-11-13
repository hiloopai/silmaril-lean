module

public import Silmaril.Prelude.Trust.Policy.Defs

/-! # Trust profiles: examples

A toy procedure, not in the `default` set, under each profile. The proposition is the same in
every case; only the proof term (and its axioms) changes.
-/

@[expose] public section

-- These tests check each profile's behaviour, so they fix the profile they start from.
set_option silmaril.trust.profile "default"

namespace Silmaril.Trust.Examples

/-- Whether `0 + 1 + … + (n - 1)` is even. -/
def evenSum (n : Nat) : Bool := (List.range n).foldl (· + ·) 0 % 2 == 0

/-- Test procedure: a fold over a list. Trusts the compiled `List.range` and `Nat` arithmetic. -/
native_decider test.evenSum := Silmaril.Trust.Examples.evenSum with_kernel_fallback

/-- The same computation, registered again with no kernel fallback. -/
def evenSum' (n : Nat) : Bool := evenSum n

/-- A procedure with no kernel fallback. -/
native_decider test.evenSumNoKernel := Silmaril.Trust.Examples.evenSum'

/-- A set naming the toy procedure, usable as a profile. -/
trust_set toys := {test.evenSum}

-- Default profile: `test.evenSum` is not in `default`, so the kernel checks it.
theorem byDefault : evenSum 100 = true := by edge_decide

-- Local profile: everything in the scope's `max` (here `all`) runs natively.
set_option silmaril.trust.profile "local" in
theorem byLocal : evenSum 100 = true := by edge_decide

-- A named set as the profile.
set_option silmaril.trust.profile "toys" in
theorem byToys : evenSum 100 = true := by edge_decide

-- A procedure can be named explicitly; it must match the goal's head.
set_option silmaril.trust.profile "toys" in
theorem byName : evenSum 100 = true := by edge_decide test.evenSum

-- The build's ceiling bounds the profile a source file picks. (Only this test sets the ceiling
-- in source; scripts/check-layout.sh rejects it anywhere else.)
set_option silmaril.trust.ceiling "paranoid" in
set_option silmaril.trust.profile "local" in
theorem underCeiling : evenSum 100 = true := by edge_decide

/--
info: {"axioms":[],"decl":"Silmaril.Trust.Examples.underCeiling","dep_native":[],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":[],"own_native":[],"profile":"default","schema":"silmaril.trust.v1"}
-/
#guard_msgs in
trust_audit underCeiling

/--
error: edge_decide: test.evenSumNoKernel may not run natively in Silmaril.Prelude.Trust.Examples under profile default, and it has no kernel fallback
-/
#guard_msgs in
example : evenSum' 100 = true := by edge_decide

/--
error: edge_decide: test.evenSum evaluated to false
  evenSum 3
-/
#guard_msgs in
set_option silmaril.trust.profile "local" in
example : evenSum 3 = true := by edge_decide

/-- error: edge_decide: unknown trust set nosuchset -/
#guard_msgs in
set_option silmaril.trust.profile "nosuchset" in
example : evenSum 100 = true := by edge_decide

/--
info: {"axioms":[],"decl":"Silmaril.Trust.Examples.byDefault","dep_native":[],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":[],"own_native":[],"profile":"default","schema":"silmaril.trust.v1"}
-/
#guard_msgs in
trust_audit byDefault

-- The audit checks against the profile in force: `byLocal` ran natively, which the default
-- profile would not have allowed here.
/--
error: trust_audit Silmaril.Trust.Examples.byLocal: own native test.evenSum is not allowed
-/
#guard_msgs in
trust_audit byLocal

set_option silmaril.trust.profile "local" in
/--
info: {"axioms":[],"decl":"Silmaril.Trust.Examples.byLocal","dep_native":[],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":["_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byLocal._native.edge.test.evenSum.ax_1_1"],"own_native":["test.evenSum"],"profile":"local","schema":"silmaril.trust.v1"}
-/
#guard_msgs in
trust_audit byLocal

/--
info: {"doc":"Test procedure: a fold over a list. Trusts the compiled `List.range` and `Nat` arithmetic.","format":null,"function":"Silmaril.Trust.Examples.evenSum","kernel_fallback":true,"kind":"procedure","module":"Silmaril.Prelude.Trust.Examples","name":"test.evenSum","schema":"silmaril.trust.v1","sound":null}
{"doc":"A procedure with no kernel fallback.","format":null,"function":"Silmaril.Trust.Examples.evenSum'","kernel_fallback":false,"kind":"procedure","module":"Silmaril.Prelude.Trust.Examples","name":"test.evenSumNoKernel","schema":"silmaril.trust.v1","sound":null}
{"axiom":null,"decl":"Silmaril.Trust.Examples.byDefault","kind":"use","mode":"kernel","module":"Silmaril.Prelude.Trust.Examples","procedure":"test.evenSum","profile":"default","schema":"silmaril.trust.v1"}
{"axiom":"_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byLocal._native.edge.test.evenSum.ax_1_1","decl":"Silmaril.Trust.Examples.byLocal","kind":"use","mode":"native","module":"Silmaril.Prelude.Trust.Examples","procedure":"test.evenSum","profile":"local","schema":"silmaril.trust.v1"}
{"axiom":"_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byToys._native.edge.test.evenSum.ax_1_1","decl":"Silmaril.Trust.Examples.byToys","kind":"use","mode":"native","module":"Silmaril.Prelude.Trust.Examples","procedure":"test.evenSum","profile":"toys","schema":"silmaril.trust.v1"}
{"axiom":"_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byName._native.edge.test.evenSum.ax_1_1","decl":"Silmaril.Trust.Examples.byName","kind":"use","mode":"native","module":"Silmaril.Prelude.Trust.Examples","procedure":"test.evenSum","profile":"toys","schema":"silmaril.trust.v1"}
{"axiom":null,"decl":"Silmaril.Trust.Examples.underCeiling","kind":"use","mode":"kernel","module":"Silmaril.Prelude.Trust.Examples","procedure":"test.evenSum","profile":"local≤paranoid","schema":"silmaril.trust.v1"}
-/
#guard_msgs in
#trust_uses

end Silmaril.Trust.Examples
