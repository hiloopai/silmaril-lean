module

import Silmaril.Logic.ACL2.X86Run.Status.RecordThms
import Lean

namespace Silmaril.Logic.ACL2.X86Run.Status.RecordTests

open Standard

example : orderObservations.all (fun (x, y, xy, yx, lexy, leyx) =>
    decide (ObjectOrder.before x y = xy ∧ ObjectOrder.before y x = yx ∧
      ObjectOrder.lexorder x y = lexy ∧ ObjectOrder.lexorder y x = leyx)) = true := by
  decide +kernel

-- These native observations exercise closed branches of the exported field dispatcher.
example (p : FieldPredicates) : entryObservations.all (fun (state, expected) =>
    decide (entriesP fieldRules p state = expected)) = true := rfl

example (p : FieldPredicates) : observations.all (fun o =>
    let primitives := recordPrimitives fieldRules p
    decide (logicalStateP primitives o.state = o.valid ∧
      ms.read primitives o.state = o.ms ∧ fault.read primitives o.state = o.fault)) = true := rfl

private def both := (observations[1]'(by decide)).state
private def msOnly := (observations[2]'(by decide)).state

example (p : FieldPredicates) (step : Object → Object) :
    (machineBindingsWithFields p step).run (.integer 2) both = both :=
  fault_exit (recordPrimitives fieldRules p) step _ _ (by intro h; contradiction)

example (p : FieldPredicates) (step : Object → Object) :
    (machineBindingsWithFields p step).run (.rational (Rat.divInt 1 2)) msOnly = msOnly :=
  ms_exit (recordPrimitives fieldRules p) step _ _ rfl (by intro h; contradiction)

example (p : FieldPredicates) (step : Object → Object) :
    halted.Holds (machineBindingsWithFields p step).admittedModel := halted_holds_with_fields p step

run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[``ObjectOrder.before, ``ObjectOrder.before_native,
    ``ObjectOrder.before_trans, ``ObjectOrder.before_trichotomy, ``ObjectOrder.before_irrefl,
    ``ObjectOrder.lexorder_cons, ``ObjectOrder.lexorder_symbols, ``ObjectOrder.lexorder_strings,
    ``ObjectOrder.lexorder_alphorder,
    ``entriesP_native, ``adjacent_before, ``ttyBufferP, ``halted_holds_with_fields]
  for declaration in declarations do
    for axiomName in ← Lean.collectAxioms declaration do
      unless allowed.contains axiomName do
        throwError "{declaration} depends on unapproved axiom {axiomName}"
  Lean.logInfo m!"ACL2 object order and record recognition: audited {declarations.size} declarations"

end Silmaril.Logic.ACL2.X86Run.Status.RecordTests
