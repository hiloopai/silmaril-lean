module

public import Silmaril.Logic.ACL2.X86Run.Status.EnvironmentSource
public import Silmaril.Logic.ACL2.X86Run.Status.RecordThms
import Silmaril.Logic.ACL2.Standard.Objects.Thms

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Run.Status.Environment

open Standard

theorem alistP_native (x : Object) :
    alistP x = (if x.consp then x.car.consp && alistP x.cdr else decide (x = .nil)) := by
  cases x <;> rfl

theorem len_native (x : Object) :
    len x = (if x.consp then 1 + len x.cdr else 0) := by
  cases x <;> rfl

theorem assocEqual_native (k x : Object) : assocEqual k x =
    (if x.consp then if k = x.car.car then x.car else assocEqual k x.cdr else .nil) := by
  cases x <;> rfl

theorem trueListp_native (x : Object) :
    x.trueListp = (if x.consp then x.cdr.trueListp else decide (x = .nil)) := by
  cases x <;> rfl

theorem signedByteP_iff (width : Nat) (x : Object) : signedByteP width x = true ↔
    0 < width ∧ ∃ i : Int, x = .integer i ∧ -(2 : Int) ^ (width - 1) ≤ i ∧
      i < (2 : Int) ^ (width - 1) := by
  cases h : x.integerValue? <;> simp [signedByteP, ← Object.integerValue?_eq_some_iff, h]

theorem ripRetAlistP_native (x : Object) : ripRetAlistP addressWidth x =
    (if x.consp then
      x.car.consp && signedByteP addressWidth x.car.car && x.car.cdr.trueListp &&
        ripRetAlistP addressWidth x.cdr
    else decide (x = .nil)) := by
  cases x <;> rfl

theorem envAlistP_native (x : Object) : envAlistP x =
    (if x = .nil then true else
      let descriptors := assocEqual descriptorsKey x
      let contents := assocEqual contentsKey x
      let oracle := assocEqual oracleKey x
      alistP x && decide (len x = fieldCount) &&
        descriptors.consp && alistP descriptors.cdr &&
        contents.consp && alistP contents.cdr &&
        oracle.consp && ripRetAlistP addressWidth oracle.cdr) := by
  by_cases h : x = .nil <;> simp [envAlistP, h]

/-- The exported environment recognizer is fixed. TLBP stays a separate predicate. -/
def fieldPredicatesWithEnvironment (tlb : Object → Bool) : FieldPredicates := ⟨envAlistP, tlb⟩

/-- On a singleton environment entry the recognizer additionally excludes the NIL default. -/
theorem env_entry (tlb : Object → Bool) (x : Object) :
    entriesP fieldRules (fieldPredicatesWithEnvironment tlb)
        (.cons (.cons (.cons (.symbol ((Symbol.ofName? ⟨"KEYWORD", "ENV"⟩).get (by decide))) .nil) x) .nil) =
      (envAlistP x && decide (x ≠ .nil)) := by
  simp [entriesP, Object.car, fieldPredicatesWithEnvironment, Object.nil]
  rfl

/-- The only external bindings are logical TLBP and X86-FETCH-DECODE-EXECUTE. -/
def machineBindingsWithEnvironment (tlb : Object → Bool) (step : Object → Object) : MachineBindings :=
  machineBindingsWithFields (fieldPredicatesWithEnvironment tlb) step

theorem halted_holds_with_environment (tlb : Object → Bool) (step : Object → Object) :
    halted.Holds (machineBindingsWithEnvironment tlb step).admittedModel :=
  halted_holds_with_fields (fieldPredicatesWithEnvironment tlb) step

end Silmaril.Logic.ACL2.X86Run.Status.Environment
