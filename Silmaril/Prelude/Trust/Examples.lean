module

public import Silmaril.Prelude.Trust.Policy.Defs
meta import Silmaril.Prelude.Trust.Defs

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

/-! ### A paired backend: the statement and the kernel see `evenSum`; native runs execute
`evenSumRec`, and `evenSumRec_eq` transfers the result. -/

/-- `0 + 1 + … + (n - 1)`, by structural recursion. -/
def sumTo : Nat → Nat
  | 0 => 0
  | k + 1 => sumTo k + k

def evenSumRec (n : Nat) : Bool := sumTo n % 2 == 0

theorem foldl_add_range (n : Nat) : (List.range n).foldl (· + ·) 0 = sumTo n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [List.range_succ, List.foldl_append, ih]; rfl

theorem evenSumRec_eq : @evenSumRec = @evenSum := by
  funext n; simp only [evenSumRec, evenSum, foldl_add_range]

/-- `evenSum`, run natively as `evenSumRec`. -/
native_decider test.evenSumPaired := Silmaril.Trust.Examples.evenSum with_kernel_fallback
  native Silmaril.Trust.Examples.evenSumRec via Silmaril.Trust.Examples.evenSumRec_eq

set_option silmaril.trust.profile "local" in
theorem byPaired : evenSum 100 = true := by edge_decide test.evenSumPaired

-- The paranoid profile checks the same statement with `evenSum` itself in the kernel.
set_option silmaril.trust.profile "paranoid" in
theorem byPairedKernel : evenSum 100 = true := by edge_decide test.evenSumPaired

set_option silmaril.trust.profile "local" in
/--
info: {"axioms":["propext","Quot.sound"],"decl":"Silmaril.Trust.Examples.byPaired","dep_native":[],"elaborated_profiles":["local"],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":["_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byPaired._native.edge.test.evenSumPaired.ax_1_1"],"own_native":["test.evenSumPaired"],"profile":"local","schema":"silmaril.trust.v1","violations":[]}
{"axioms":[],"decl":"Silmaril.Trust.Examples.byPairedKernel","dep_native":[],"elaborated_profiles":["paranoid"],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":[],"own_native":[],"profile":"local","schema":"silmaril.trust.v1","violations":[]}
-/
#guard_msgs in
trust_audit byPaired byPairedKernel

/-! ### A same-target pair: two checkers with different arguments, one proposition. -/

/-- The proposition both checkers establish. -/
def SumEven (n : Nat) : Prop := sumTo n % 2 = 0

/-- Kernel-side checker: on `n`. -/
def sumEvenK (n : Nat) : Bool := sumTo n % 2 == 0
/-- Native-side checker: on a different argument, `n` as a list of its predecessors. -/
def sumEvenN (l : List Nat) : Bool := l.foldl (· + ·) 0 % 2 == 0

theorem sumEvenK_sound (n : Nat) (h : sumEvenK n = true) : SumEven n := by
  simpa [sumEvenK, SumEven] using h
theorem sumEvenN_sound (n : Nat) (h : sumEvenN (List.range n) = true) : SumEven n := by
  simpa [sumEvenN, SumEven, foldl_add_range] using h

/-- Kernel side of the pair. -/
native_decider test.sumEvenK := Silmaril.Trust.Examples.sumEvenK with_kernel_fallback
/-- Native side of the pair (no kernel fallback of its own). -/
native_decider test.sumEvenN := Silmaril.Trust.Examples.sumEvenN

set_option silmaril.trust.profile "local" in
theorem pairNative : SumEven 100 :=
  by edge_pair (native := sumEvenN_sound 100) (kernel := sumEvenK_sound 100)

set_option silmaril.trust.profile "paranoid" in
theorem pairKernel : SumEven 100 :=
  by edge_pair (native := sumEvenN_sound 100) (kernel := sumEvenK_sound 100)

/-- Allows the kernel side natively, but not the native side. -/
trust_set kernelSideOnly := {test.sumEvenK}

-- The kernel side still runs in the kernel, not natively.
set_option silmaril.trust.profile "kernelSideOnly" in
theorem pairKernelAllowed : SumEven 100 :=
  by edge_pair (native := sumEvenN_sound 100) (kernel := sumEvenK_sound 100)

/--
info: {"axioms":["propext","Quot.sound"],"decl":"Silmaril.Trust.Examples.pairKernelAllowed","dep_native":[],"elaborated_profiles":["kernelSideOnly"],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":[],"own_native":[],"profile":"default","schema":"silmaril.trust.v1","violations":[]}
-/
#guard_msgs in
trust_audit pairKernelAllowed

set_option silmaril.trust.profile "local" in
/--
info: {"axioms":["propext","Quot.sound"],"decl":"Silmaril.Trust.Examples.pairNative","dep_native":[],"elaborated_profiles":["local"],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":["_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.pairNative._native.edge.test.sumEvenN.ax_1_1"],"own_native":["test.sumEvenN"],"profile":"local","schema":"silmaril.trust.v1","violations":[]}
{"axioms":["propext","Quot.sound"],"decl":"Silmaril.Trust.Examples.pairKernel","dep_native":[],"elaborated_profiles":["paranoid"],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":[],"own_native":[],"profile":"local","schema":"silmaril.trust.v1","violations":[]}
{"axioms":["propext","Quot.sound"],"decl":"Silmaril.Trust.Examples.pairKernelAllowed","dep_native":[],"elaborated_profiles":["kernelSideOnly"],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":[],"own_native":[],"profile":"local","schema":"silmaril.trust.v1","violations":[]}
-/
#guard_msgs in
trust_audit pairNative pairKernel pairKernelAllowed

/-! ### A declared two-backend procedure (`ProcDecl`, `sil_check`)

The declaration needs only `Silmaril.Prelude.Trust.Decl.Defs`. -/

/-- Even sums: natively over the list, by the kernel over `n`. -/
def _root_.Silmaril.Procedures.test.sumEven : ProcDecl where
  doc := "Even sums. Native: compiled List.foldl over List.range."
  native := some ⟨``sumEvenN, ``sumEvenN_sound⟩
  kernel := some ⟨``sumEvenK, ``sumEvenK_sound⟩

/-- Allows the declared procedure natively. -/
trust_set sumEvenSet := {test.sumEven}

set_option silmaril.trust.profile "sumEvenSet" in
theorem silNative : SumEven 100 := by
  sil_check test.sumEven (native := sumEvenN_sound 100) (kernel := sumEvenK_sound 100)

-- Default profile: `test.sumEven` is not in `default`, so the kernel backend is used.
theorem silKernel : SumEven 100 := by
  sil_check test.sumEven (native := sumEvenN_sound 100) (kernel := sumEvenK_sound 100)

-- Kernel side alone.
theorem silKernelOnly : SumEven 100 := by sil_check test.sumEven (kernel := sumEvenK_sound 100)

/--
error: sil_check test.sumEven: the native side must apply Silmaril.Trust.Examples.sumEvenN_sound
  sumEvenK_sound 100
-/
#guard_msgs in
set_option silmaril.trust.profile "sumEvenSet" in
example : SumEven 100 := by sil_check test.sumEven (native := sumEvenK_sound 100)

/--
info: {"axioms":["propext","Quot.sound"],"decl":"Silmaril.Trust.Examples.silKernel","dep_native":[],"elaborated_profiles":["default"],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":[],"own_native":[],"profile":"default","schema":"silmaril.trust.v1","violations":[]}
{"axioms":["propext","Quot.sound"],"decl":"Silmaril.Trust.Examples.silKernelOnly","dep_native":[],"elaborated_profiles":["default"],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":[],"own_native":[],"profile":"default","schema":"silmaril.trust.v1","violations":[]}
-/
#guard_msgs in
trust_audit silKernel silKernelOnly

set_option silmaril.trust.profile "sumEvenSet" in
/--
info: {"axioms":["propext","Quot.sound"],"decl":"Silmaril.Trust.Examples.silNative","dep_native":[],"elaborated_profiles":["sumEvenSet"],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":["_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.silNative._native.edge.test.sumEven.ax_1_1"],"own_native":["test.sumEven"],"profile":"sumEvenSet","schema":"silmaril.trust.v1","violations":[]}
-/
#guard_msgs in
trust_audit silNative

/--
info: {"constant":"Silmaril.Procedures.test.sumEven","doc":"Even sums. Native: compiled List.foldl over List.range.","format":null,"kernel":{"check":"Silmaril.Trust.Examples.sumEvenK","sound":"Silmaril.Trust.Examples.sumEvenK_sound"},"kind":"declared_procedure","name":"test.sumEven","native":{"check":"Silmaril.Trust.Examples.sumEvenN","sound":"Silmaril.Trust.Examples.sumEvenN_sound"},"schema":"silmaril.trust.v1"}
-/
#guard_msgs in
#trust_decls

/-- A set naming the toy procedure, usable as a profile. -/
trust_set toys := {test.evenSum}

-- Default profile: `test.evenSum` is not in `default`, so the kernel checks it.
theorem byDefault : evenSum 100 = true := by edge_decide test.evenSum

-- Local profile: everything in the scope's `max` (here `all`) runs natively.
set_option silmaril.trust.profile "local" in
theorem byLocal : evenSum 100 = true := by edge_decide test.evenSum

-- A named set as the profile.
set_option silmaril.trust.profile "toys" in
theorem byToys : evenSum 100 = true := by edge_decide test.evenSum

-- A procedure can be named explicitly; it must match the goal's head.
set_option silmaril.trust.profile "toys" in
theorem byName : evenSum 100 = true := by edge_decide test.evenSum

-- The build's ceiling bounds the profile a source file picks. (Only this test sets the ceiling
-- in source; scripts/check-layout.sh rejects it anywhere else.)
set_option silmaril.trust.ceiling "paranoid" in
set_option silmaril.trust.profile "local" in
theorem underCeiling : evenSum 100 = true := by edge_decide test.evenSum

/--
info: {"axioms":[],"decl":"Silmaril.Trust.Examples.underCeiling","dep_native":[],"elaborated_profiles":["local≤paranoid"],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":[],"own_native":[],"profile":"default","schema":"silmaril.trust.v1","violations":[]}
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
example : evenSum 3 = true := by edge_decide test.evenSum

/-- error: edge_decide: unknown trust set nosuchset -/
#guard_msgs in
set_option silmaril.trust.profile "nosuchset" in
example : evenSum 100 = true := by edge_decide test.evenSum

/--
info: {"axioms":[],"decl":"Silmaril.Trust.Examples.byDefault","dep_native":[],"elaborated_profiles":["default"],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":[],"own_native":[],"profile":"default","schema":"silmaril.trust.v1","violations":[]}
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
info: {"axioms":[],"decl":"Silmaril.Trust.Examples.byLocal","dep_native":[],"elaborated_profiles":["local"],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":["_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byLocal._native.edge.test.evenSum.ax_1_1"],"own_native":["test.evenSum"],"profile":"local","schema":"silmaril.trust.v1","violations":[]}
-/
#guard_msgs in
trust_audit byLocal

/--
info: {"doc":"Test procedure: a fold over a list. Trusts the compiled `List.range` and `Nat` arithmetic.","format":null,"function":"Silmaril.Trust.Examples.evenSum","kernel_fallback":true,"kind":"procedure","module":"Silmaril.Prelude.Trust.Examples","name":"test.evenSum","native_eq":null,"native_function":null,"schema":"silmaril.trust.v1","sound":null}
{"doc":"A procedure with no kernel fallback.","format":null,"function":"Silmaril.Trust.Examples.evenSum'","kernel_fallback":false,"kind":"procedure","module":"Silmaril.Prelude.Trust.Examples","name":"test.evenSumNoKernel","native_eq":null,"native_function":null,"schema":"silmaril.trust.v1","sound":null}
{"doc":"`evenSum`, run natively as `evenSumRec`.","format":null,"function":"Silmaril.Trust.Examples.evenSum","kernel_fallback":true,"kind":"procedure","module":"Silmaril.Prelude.Trust.Examples","name":"test.evenSumPaired","native_eq":"Silmaril.Trust.Examples.evenSumRec_eq","native_function":"Silmaril.Trust.Examples.evenSumRec","schema":"silmaril.trust.v1","sound":null}
{"doc":"Kernel side of the pair.","format":null,"function":"Silmaril.Trust.Examples.sumEvenK","kernel_fallback":true,"kind":"procedure","module":"Silmaril.Prelude.Trust.Examples","name":"test.sumEvenK","native_eq":null,"native_function":null,"schema":"silmaril.trust.v1","sound":null}
{"doc":"Native side of the pair (no kernel fallback of its own).","format":null,"function":"Silmaril.Trust.Examples.sumEvenN","kernel_fallback":false,"kind":"procedure","module":"Silmaril.Prelude.Trust.Examples","name":"test.sumEvenN","native_eq":null,"native_function":null,"schema":"silmaril.trust.v1","sound":null}
{"axiom":"_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byPaired._native.edge.test.evenSumPaired.ax_1_1","decl":"Silmaril.Trust.Examples.byPaired","kind":"use","mode":"native","module":"Silmaril.Prelude.Trust.Examples","procedure":"test.evenSumPaired","profile":"local","schema":"silmaril.trust.v1"}
{"axiom":null,"decl":"Silmaril.Trust.Examples.byPairedKernel","kind":"use","mode":"kernel","module":"Silmaril.Prelude.Trust.Examples","procedure":"test.evenSumPaired","profile":"paranoid","schema":"silmaril.trust.v1"}
{"axiom":"_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.pairNative._native.edge.test.sumEvenN.ax_1_1","decl":"Silmaril.Trust.Examples.pairNative","kind":"use","mode":"native","module":"Silmaril.Prelude.Trust.Examples","procedure":"test.sumEvenN","profile":"local","schema":"silmaril.trust.v1"}
{"axiom":null,"decl":"Silmaril.Trust.Examples.pairKernel","kind":"use","mode":"kernel","module":"Silmaril.Prelude.Trust.Examples","procedure":"test.sumEvenK","profile":"paranoid","schema":"silmaril.trust.v1"}
{"axiom":null,"decl":"Silmaril.Trust.Examples.pairKernelAllowed","kind":"use","mode":"kernel","module":"Silmaril.Prelude.Trust.Examples","procedure":"test.sumEvenK","profile":"kernelSideOnly","schema":"silmaril.trust.v1"}
{"axiom":"_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.silNative._native.edge.test.sumEven.ax_1_1","decl":"Silmaril.Trust.Examples.silNative","kind":"use","mode":"native","module":"Silmaril.Prelude.Trust.Examples","procedure":"test.sumEven","profile":"sumEvenSet","schema":"silmaril.trust.v1"}
{"axiom":null,"decl":"Silmaril.Trust.Examples.silKernel","kind":"use","mode":"kernel","module":"Silmaril.Prelude.Trust.Examples","procedure":"test.sumEven","profile":"default","schema":"silmaril.trust.v1"}
{"axiom":null,"decl":"Silmaril.Trust.Examples.silKernelOnly","kind":"use","mode":"kernel","module":"Silmaril.Prelude.Trust.Examples","procedure":"test.sumEven","profile":"default","schema":"silmaril.trust.v1"}
{"axiom":null,"decl":"Silmaril.Trust.Examples.byDefault","kind":"use","mode":"kernel","module":"Silmaril.Prelude.Trust.Examples","procedure":"test.evenSum","profile":"default","schema":"silmaril.trust.v1"}
{"axiom":"_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byLocal._native.edge.test.evenSum.ax_1_1","decl":"Silmaril.Trust.Examples.byLocal","kind":"use","mode":"native","module":"Silmaril.Prelude.Trust.Examples","procedure":"test.evenSum","profile":"local","schema":"silmaril.trust.v1"}
{"axiom":"_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byToys._native.edge.test.evenSum.ax_1_1","decl":"Silmaril.Trust.Examples.byToys","kind":"use","mode":"native","module":"Silmaril.Prelude.Trust.Examples","procedure":"test.evenSum","profile":"toys","schema":"silmaril.trust.v1"}
{"axiom":"_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byName._native.edge.test.evenSum.ax_1_1","decl":"Silmaril.Trust.Examples.byName","kind":"use","mode":"native","module":"Silmaril.Prelude.Trust.Examples","procedure":"test.evenSum","profile":"toys","schema":"silmaril.trust.v1"}
{"axiom":null,"decl":"Silmaril.Trust.Examples.underCeiling","kind":"use","mode":"kernel","module":"Silmaril.Prelude.Trust.Examples","procedure":"test.evenSum","profile":"local≤paranoid","schema":"silmaril.trust.v1"}
-/
#guard_msgs in
#trust_uses

/--
info: roundtrip ok: 5 procedures, 13 uses
-/
#guard_msgs in
#trust_roundtrip

/-! ### No escalation: a child scope cannot grant more than its parent. -/

/-- info: policy scope Silmaril.X: deps exceeds its parent's deps -/
#guard_msgs in
open Lean in
#eval show CoreM Unit from do
  let root : Scope := { module := `Silmaril, max := some `all, dflt := some `none,
                        deps := some `none, axiomSet := some `none }
  let child : Scope := { module := `Silmaril.X, deps := some `all }
  match effectiveIn (← getEnv) { scopes := #[root, child] } `Silmaril.X.Y with
  | .ok _ => logInfo "accepted"
  | .error e => logInfo m!"{e}"

/-- info: policy scope Silmaril.X: axioms exceeds its parent's axioms -/
#guard_msgs in
open Lean in
#eval show CoreM Unit from do
  let root : Scope := { module := `Silmaril, max := some `all, dflt := some `none,
                        deps := some `none, axiomSet := some `none }
  let child : Scope := { module := `Silmaril.X, axiomSet := some `all }
  match effectiveIn (← getEnv) { scopes := #[root, child] } `Silmaril.X.Y with
  | .ok _ => logInfo "accepted"
  | .error e => logInfo m!"{e}"

end Silmaril.Trust.Examples
