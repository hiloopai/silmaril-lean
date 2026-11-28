module

import Silmaril.Logic.ACL2.X86Run.WithStep.Thms
import Lean

namespace Silmaril.Logic.ACL2.X86Run.WithStep

example : X86Step.definition.symbol.val = stepSymbol.val := rfl

run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[``fetchDecodeExecute, ``machineBindings, ``step_defining_equation,
    ``run_equation_holds, ``halted_holds]
  for declaration in declarations do
    for axiomName in ← Lean.collectAxioms declaration do
      unless allowed.contains axiomName do
        throwError "{declaration} depends on unapproved axiom {axiomName}"
  Lean.logInfo m!"ACL2 X86-RUN with checked step: audited {declarations.size} declarations"

#print axioms step_defining_equation
#print axioms run_equation_holds
#print axioms halted_holds

end Silmaril.Logic.ACL2.X86Run.WithStep
