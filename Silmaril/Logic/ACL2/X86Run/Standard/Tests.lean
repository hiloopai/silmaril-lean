module

import Silmaril.Logic.ACL2.X86Run.Standard.Thms
import Silmaril.Logic.ACL2.Standard.Objects.Thms
import Lean

namespace Silmaril.Logic.ACL2.X86Run.Tests

open Standard

example (m : MachineBindings) : m.admittedModel.primitives = objectPrimitives := rfl

example (m : MachineBindings) (x : Object) :
    m.objectModel.interpret zpSymbol (fun _ => x) = x.zp := rfl

example (m : MachineBindings) (x y : Object) :
    m.objectModel.interpret addSymbol ![x, y] = x.binaryAdd y := rfl

example (m : MachineBindings) :
    m.objectModel.interpret minusOneSymbol Fin.elim0 = Object.integer (-1) := rfl

example (m : MachineBindings) (x86 : Object) :
    m.objectModel.interpret stepSymbol (fun _ => x86) = m.fetchDecodeExecute x86 := rfl

example (m : MachineBindings) (n x86 : Object) :
    rank m.countLaws ⟨2, runSymbol, ![n, x86]⟩ = n.natRank := rfl

-- The exported recursive argument places -1 first. The standard decrement lemma
-- places it second, so align the two component additions.
example (m : MachineBindings) (n : Object)
    (h : m.objectModel.interpret zpSymbol (fun _ => n) = Object.nil) :
    (m.objectModel.interpret addSymbol
      ![m.objectModel.interpret minusOneSymbol Fin.elim0, n]).natRank < n.natRank := by
  change ((Object.integer (-1)).binaryAdd n).natRank < n.natRank
  simpa only [Object.decrement, Object.binaryAdd, Rat.add_comm] using
    (Object.natRank_decrement_lt h)

-- Test the generated body with fixtures that make each status exit observable.
private def fixture : MachineBindings :=
  ⟨Object.car, Object.cdr, fun _ => Object.nil⟩

private def faultState : Object := .cons (.integer 3) .nil
private def msState : Object := .cons .nil (.integer 4)

example : fixture.run (Object.integer 2) faultState = faultState :=
  fixture.fault_exit _ _ (by decide)

-- The halt equation also applies to counts outside the native guard.
example : fixture.run (.rational (Rat.divInt 1 2)) msState = msState :=
  fixture.ms_exit _ _ rfl (by decide)

example (m : MachineBindings) : (declaration.equation runSymbol).Holds m.admittedModel :=
  m.equation_holds

example (m : MachineBindings) : halted.Holds m.admittedModel := m.halted_holds

run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[``MachineBindings.objectModel, ``MachineBindings.countLaws,
    ``MachineBindings.admittedModel, ``MachineBindings.run, ``MachineBindings.equation_holds,
    ``MachineBindings.fault_exit, ``MachineBindings.ms_exit, ``MachineBindings.halted_holds]
  for declaration in declarations do
    for axiomName in ← Lean.collectAxioms declaration do
      unless allowed.contains axiomName do
        throwError "{declaration} depends on unapproved axiom {axiomName}"
  Lean.logInfo m!"Standard X86-RUN: audited {declarations.size} bindings and theorems"

end Silmaril.Logic.ACL2.X86Run.Tests
