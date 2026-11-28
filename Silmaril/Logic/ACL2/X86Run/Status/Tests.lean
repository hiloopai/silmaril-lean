module

import Silmaril.Logic.ACL2.X86Run.Status.Thms
import Lean

namespace Silmaril.Logic.ACL2.X86Run.Status.Tests

open Standard

private def statusKeyBefore (lhs rhs : Object) : Bool :=
  decide (lhs = fault.key ∧ rhs = ms.key)

-- A test interpretation restricted to status-only entry lists. The library accepts any
-- interpretation of the two named record primitives.
private def statusEntriesP : Object → Bool
  | .cons (.cons key value) tail =>
    decide ((key = fault.key ∨ key = ms.key) ∧ value ≠ Object.nil) &&
      statusEntriesP tail && (decide (tail = Object.nil) || statusKeyBefore key tail.car.car)
  | x => decide (x = Object.nil)

private def statusOnly : RecordPrimitives := ⟨statusEntriesP, statusKeyBefore⟩

example : observations.all (fun o =>
    decide (logicalStateP statusOnly o.state = o.valid ∧
      ms.read statusOnly o.state = o.ms ∧ fault.read statusOnly o.state = o.fault)) = true := by
  decide +kernel

private def both := (observations[1]'(by decide)).state
private def msOnly := (observations[2]'(by decide)).state

example (step : Object → Object) :
    (machineBindings statusOnly step).run (Object.integer 2) both = both :=
  fault_exit statusOnly step _ _ (by decide +kernel)

example (step : Object → Object) :
    (machineBindings statusOnly step).run (.rational (Rat.divInt 1 2)) msOnly = msOnly :=
  ms_exit statusOnly step _ _ (by decide +kernel) (by decide +kernel)

example : ms.readFoundation (Object.ofList [.integer 40, .integer 42]) = .integer 40 ∧
    fault.readFoundation (Object.ofList [.integer 40, .integer 42]) = .integer 42 := by
  decide +kernel

example (p : RecordPrimitives) (step : Object → Object) :
    halted.Holds (machineBindings p step).admittedModel := halted_holds p step

run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[``logicalStateP_of_entries, ``Accessor.read_of_entries, ``Accessor.read_atom,
    ``Accessor.readFoundation, ``fault_exit, ``ms_exit, ``halted_holds]
  for declaration in declarations do
    for axiomName in ← Lean.collectAxioms declaration do
      unless allowed.contains axiomName do
        throwError "{declaration} depends on unapproved axiom {axiomName}"
  Lean.logInfo m!"X86 status accessors: audited {declarations.size} declarations"

end Silmaril.Logic.ACL2.X86Run.Status.Tests
