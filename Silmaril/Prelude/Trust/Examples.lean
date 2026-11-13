module

public import Silmaril.Prelude.Trust.Policy.Defs
meta import Silmaril.Prelude.Trust.Defs
meta import Silmaril.Prelude.Trust.Elab.Defs
import Silmaril.Prelude.Trust.TestForge

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
info: {"axioms":["propext","Quot.sound"],"decl":"Silmaril.Trust.Examples.byPaired","dep_native":[],"elaborated_profiles":["local"],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":["_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byPaired._native.edge.test.evenSumPaired.ax_1_1"],"own_native":["test.evenSumPaired"],"profile":"local","schema":"silmaril.trust.v1","unverified_native":[],"violations":[]}
{"axioms":[],"decl":"Silmaril.Trust.Examples.byPairedKernel","dep_native":[],"elaborated_profiles":["paranoid"],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":[],"own_native":[],"profile":"local","schema":"silmaril.trust.v1","unverified_native":[],"violations":[]}
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
info: {"axioms":["propext","Quot.sound"],"decl":"Silmaril.Trust.Examples.pairKernelAllowed","dep_native":[],"elaborated_profiles":["kernelSideOnly"],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":[],"own_native":[],"profile":"default","schema":"silmaril.trust.v1","unverified_native":[],"violations":[]}
-/
#guard_msgs in
trust_audit pairKernelAllowed

set_option silmaril.trust.profile "local" in
/--
info: {"axioms":["propext","Quot.sound"],"decl":"Silmaril.Trust.Examples.pairNative","dep_native":[],"elaborated_profiles":["local"],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":["_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.pairNative._native.edge.test.sumEvenN.ax_1_1"],"own_native":["test.sumEvenN"],"profile":"local","schema":"silmaril.trust.v1","unverified_native":[],"violations":[]}
{"axioms":["propext","Quot.sound"],"decl":"Silmaril.Trust.Examples.pairKernel","dep_native":[],"elaborated_profiles":["paranoid"],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":[],"own_native":[],"profile":"local","schema":"silmaril.trust.v1","unverified_native":[],"violations":[]}
{"axioms":["propext","Quot.sound"],"decl":"Silmaril.Trust.Examples.pairKernelAllowed","dep_native":[],"elaborated_profiles":["kernelSideOnly"],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":[],"own_native":[],"profile":"local","schema":"silmaril.trust.v1","unverified_native":[],"violations":[]}
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
info: {"axioms":["propext","Quot.sound"],"decl":"Silmaril.Trust.Examples.silKernel","dep_native":[],"elaborated_profiles":["default"],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":[],"own_native":[],"profile":"default","schema":"silmaril.trust.v1","unverified_native":[],"violations":[]}
{"axioms":["propext","Quot.sound"],"decl":"Silmaril.Trust.Examples.silKernelOnly","dep_native":[],"elaborated_profiles":["default"],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":[],"own_native":[],"profile":"default","schema":"silmaril.trust.v1","unverified_native":[],"violations":[]}
-/
#guard_msgs in
trust_audit silKernel silKernelOnly

set_option silmaril.trust.profile "sumEvenSet" in
/--
info: {"axioms":["propext","Quot.sound"],"decl":"Silmaril.Trust.Examples.silNative","dep_native":[],"elaborated_profiles":["sumEvenSet"],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":["_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.silNative._native.edge.test.sumEven.ax_1_1"],"own_native":["test.sumEven"],"profile":"sumEvenSet","schema":"silmaril.trust.v1","unverified_native":[],"violations":[]}
-/
#guard_msgs in
trust_audit silNative

/--
info: {"bound":null,"constant":"Silmaril.Procedures.test.sumEven","doc":"Even sums. Native: compiled List.foldl over List.range.","format":null,"kernel":{"check":"Silmaril.Trust.Examples.sumEvenK","sound":"Silmaril.Trust.Examples.sumEvenK_sound"},"kind":"declared_procedure","name":"test.sumEven","native":{"check":"Silmaril.Trust.Examples.sumEvenN","sound":"Silmaril.Trust.Examples.sumEvenN_sound"},"schema":"silmaril.trust.v1"}
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
info: {"axioms":[],"decl":"Silmaril.Trust.Examples.underCeiling","dep_native":[],"elaborated_profiles":["local≤paranoid"],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":[],"own_native":[],"profile":"default","schema":"silmaril.trust.v1","unverified_native":[],"violations":[]}
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
info: {"axioms":[],"decl":"Silmaril.Trust.Examples.byDefault","dep_native":[],"elaborated_profiles":["default"],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":[],"own_native":[],"profile":"default","schema":"silmaril.trust.v1","unverified_native":[],"violations":[]}
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
info: {"axioms":[],"decl":"Silmaril.Trust.Examples.byLocal","dep_native":[],"elaborated_profiles":["local"],"kind":"audit","module":"Silmaril.Prelude.Trust.Examples","native_axioms":["_private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byLocal._native.edge.test.evenSum.ax_1_1"],"own_native":["test.evenSum"],"profile":"local","schema":"silmaril.trust.v1","unverified_native":[],"violations":[]}
-/
#guard_msgs in
trust_audit byLocal

/--
info: {"axiom_pattern":null,"components":[],"doc":"Test procedure: a fold over a list. Trusts the compiled `List.range` and `Nat` arithmetic.","fallback_coverage":"","format":null,"function":"Silmaril.Trust.Examples.evenSum","kernel_fallback":true,"kind":"procedure","module":"Silmaril.Prelude.Trust.Examples","name":"test.evenSum","native_eq":null,"native_function":null,"schema":"silmaril.trust.v1","sound":null,"toolchain":""}
{"axiom_pattern":null,"components":[],"doc":"A procedure with no kernel fallback.","fallback_coverage":"","format":null,"function":"Silmaril.Trust.Examples.evenSum'","kernel_fallback":false,"kind":"procedure","module":"Silmaril.Prelude.Trust.Examples","name":"test.evenSumNoKernel","native_eq":null,"native_function":null,"schema":"silmaril.trust.v1","sound":null,"toolchain":""}
{"axiom_pattern":null,"components":[],"doc":"`evenSum`, run natively as `evenSumRec`.","fallback_coverage":"","format":null,"function":"Silmaril.Trust.Examples.evenSum","kernel_fallback":true,"kind":"procedure","module":"Silmaril.Prelude.Trust.Examples","name":"test.evenSumPaired","native_eq":"Silmaril.Trust.Examples.evenSumRec_eq","native_function":"Silmaril.Trust.Examples.evenSumRec","schema":"silmaril.trust.v1","sound":null,"toolchain":""}
{"axiom_pattern":null,"components":[],"doc":"Kernel side of the pair.","fallback_coverage":"","format":null,"function":"Silmaril.Trust.Examples.sumEvenK","kernel_fallback":true,"kind":"procedure","module":"Silmaril.Prelude.Trust.Examples","name":"test.sumEvenK","native_eq":null,"native_function":null,"schema":"silmaril.trust.v1","sound":null,"toolchain":""}
{"axiom_pattern":null,"components":[],"doc":"Native side of the pair (no kernel fallback of its own).","fallback_coverage":"","format":null,"function":"Silmaril.Trust.Examples.sumEvenN","kernel_fallback":false,"kind":"procedure","module":"Silmaril.Prelude.Trust.Examples","name":"test.sumEvenN","native_eq":null,"native_function":null,"schema":"silmaril.trust.v1","sound":null,"toolchain":""}
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

/-! ### A registered native tactic

`decide +native` adds `<decl>._native.decide.ax_…`. Registered under the tag `decide`, that
one is classified as the procedure, but it counts as an audited use only if a framework
recorded the run that produced exactly that axiom. Here nothing recorded it, so the audit
flags it as unverified even where the procedure is allowed. -/

/-- Test registration of the native-evaluating `decide`. -/
native_tactic test.decideNative evaluates Decidable.decide axiom_tag decide
  components ["compiled Decidable instance"] toolchain "leanprover/lean4:nightly-2026-11-05"

/-- error: axiom tag decide already belongs to test.decideNative -/
#guard_msgs in
native_tactic test.other evaluates Decidable.decide axiom_tag decide
  toolchain "leanprover/lean4:nightly-2026-11-05"

/-- error: native_tactic test.missing: the evaluated constant No.Such.fn does not exist -/
#guard_msgs in
native_tactic test.missing evaluates No.Such.fn axiom_tag missing
  toolchain "leanprover/lean4:nightly-2026-11-05"

/--
error: native_tactic test.oldToolchain: described for toolchain "leanprover/lean4:v4.0.0", but this is "leanprover/lean4:nightly-2026-11-05"; review the description and update it
-/
#guard_msgs in
native_tactic test.oldToolchain evaluates Decidable.decide axiom_tag old
  toolchain "leanprover/lean4:v4.0.0"

theorem byDecideNative : (List.range 50).length = 50 := by decide +native

set_option silmaril.trust.profile "local" in
/--
error: trust_audit Silmaril.Trust.Examples.byDecideNative: unverified native axiom _private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byDecideNative._native.decide.ax_1_1: matches test.decideNative by name, but no recorded use of test.decideNative names it with the exact shape `f … = true`
-/
#guard_msgs in
trust_audit byDecideNative

/--
error: trust_audit Silmaril.Trust.Examples.byDecideNative: unverified native axiom _private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.byDecideNative._native.decide.ax_1_1: matches test.decideNative by name, but no recorded use of test.decideNative names it with the exact shape `f … = true`
-/
#guard_msgs in
trust_audit byDecideNative

/--
info: roundtrip ok: 6 procedures, 13 uses
-/
#guard_msgs in
#trust_roundtrip

/-! ### A generic checker bound to one instance (`ProcDecl.bound`) -/

def leafA : Nat := 2
def leafB : Nat := 3
/-- One checker for every "leaf". -/
def genericCheck (l n : Nat) : Bool := n % l == 0
theorem genericSound (l n : Nat) (h : genericCheck l n = true) : n % l = 0 := by
  simpa [genericCheck] using h

/-- The procedure for `leafA` only. -/
def _root_.Silmaril.Procedures.test.leafA : ProcDecl where
  doc := "genericCheck on leafA"
  native := some ⟨``genericCheck, ``genericSound⟩
  kernel := some ⟨``genericCheck, ``genericSound⟩
  bound := some ``leafA

theorem leafAOk : 100 % leafA = 0 := by sil_check test.leafA (kernel := genericSound leafA 100)

/--
error: sil_check test.leafA: the kernel check is not bound to Silmaril.Trust.Examples.leafA
  genericCheck leafB 99
-/
#guard_msgs in
example : 99 % leafB = 0 := by sil_check test.leafA (kernel := genericSound leafB 99)

/-! ### Forged records do not verify

`recordUse` is trusted instrumentation, so a test can forge one (`TestForge`). Verification also
needs the axiom to have the exact shape `f … = true` with the procedure's function at the head.
Each axiom below states `decide p = true`, whatever its tag claims. -/

/-- A procedure whose evaluated constant is `List.length`. -/
native_tactic test.lengthNative evaluates List.length axiom_tag lengthNative
  toolchain "leanprover/lean4:nightly-2026-11-05"

/-- Tagged `lengthNative` and recorded as `test.lengthNative`; `List.length` occurs in the
statement, but `Decidable.decide` is its head. -/
theorem forgedShape : (List.range 7).length = 7 :=
  forge_native% lengthNative test.lengthNative ((List.range 7).length = 7)

/-- Tagged as an `edge` run of the declared procedure `test.sumEven` and recorded as it; its
head is not the declared native check `sumEvenN`. -/
theorem forgedDecl : SumEven 4 :=
  forge_native% edge.test.sumEven test.sumEven (sumTo 4 % 2 = 0)

set_option silmaril.trust.profile "local" in
/--
error: trust_audit Silmaril.Trust.Examples.forgedShape: unverified native axiom _private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.forgedShape._native.lengthNative.ax_1_1: matches test.lengthNative by name, but no recorded use of test.lengthNative names it with the exact shape `f … = true`
-/
#guard_msgs in
trust_audit forgedShape

set_option silmaril.trust.profile "local" in
/--
error: trust_audit Silmaril.Trust.Examples.forgedDecl: unverified native axiom _private.Silmaril.Prelude.Trust.Examples.0.Silmaril.Trust.Examples.forgedDecl._native.edge.test.sumEven.ax_1_1: matches test.sumEven by name, but no recorded use of test.sumEven names it with the exact shape `f … = true`
-/
#guard_msgs in
trust_audit forgedDecl

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
