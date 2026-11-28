module

public import Silmaril.Logic.ACL2.X86Run.Status.RecordSource
public import Silmaril.Logic.ACL2.X86Run.Status.Thms
public import Silmaril.Logic.ACL2.Standard.ObjectOrder.Thms

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Run.Status

open Standard

/-- Non-NIL projection of the translated X86REC-P1 branches, with total CAR and CDR. -/
theorem entriesP_native (rules : List FieldRule) (p : FieldPredicates) (x : Object) :
    entriesP rules p x =
      if x = .nil then true
      else if x.consp && x.car.consp then
        let k := x.car.car
        let v := x.car.cdr
        let rule := fieldRule rules k.car
        entriesP rules p x.cdr && rule.fieldType.accepts p v && decide (v ≠ rule.fallback) &&
          (if x.cdr = .nil then true else ObjectOrder.before k x.cdr.car.car)
      else false := by
  cases x with
  | cons entry _ =>
    cases entry <;> simp [entriesP, Object.nil, Object.consp, Object.car, Object.cdr]
    rfl
  | _ => simp [entriesP, Object.nil, Object.consp]

theorem adjacent_before (rules : List FieldRule) (p : FieldPredicates) (k v next tail : Object)
    (h : entriesP rules p (.cons (.cons k v) (.cons next tail)) = true) :
    ObjectOrder.before k next.car = true := by
  simp only [entriesP, Object.car, Object.nil, reduceCtorEq, ↓reduceIte, Bool.and_eq_true] at h
  simpa [Object.car, Object.nil] using h.2

/-- Both readers use the concrete translated entry-list recognizer and ACL2 order.
The remaining field recognizers and the logical step are supplied explicitly. -/
def machineBindingsWithFields (p : FieldPredicates) (step : Object → Object) : MachineBindings :=
  machineBindings (recordPrimitives fieldRules p) step

theorem halted_holds_with_fields (p : FieldPredicates) (step : Object → Object) :
    halted.Holds (machineBindingsWithFields p step).admittedModel :=
  (machineBindingsWithFields p step).halted_holds

end Silmaril.Logic.ACL2.X86Run.Status
