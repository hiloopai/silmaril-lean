module

import Silmaril.Logic.ACL2.Standard.Pure.Thms
import Lean

namespace Silmaril.Logic.ACL2.Standard.Pure.Tests

example : mvNthObservations.all (fun (index, values, expected) =>
    decide (index.mvNth values = expected)) = true := by
  decide +kernel

example : eqlObservations.all (fun (x, y, expected) => decide (x.eql y = expected)) = true := by
  decide +kernel

example : notObservations.all (fun (x, expected) =>
    decide (x.logicalNot = expected)) = true := by
  decide +kernel

example : binding ⟨"ACL2", "MV-NTH"⟩ 2 = some (fun args => (args 0).mvNth (args 1)) := rfl
example : binding ⟨"COMMON-LISP", "EQL"⟩ 2 = some (fun args => (args 0).eql (args 1)) := rfl
example : binding ⟨"COMMON-LISP", "NOT"⟩ 1 = some (fun args => (args 0).logicalNot) := rfl
example : binding ⟨"ACL2", "EQL"⟩ 2 = none := rfl
example : binding ⟨"ACL2", "MV-NTH"⟩ 1 = none := rfl

run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[``binding, ``eql_native, ``logicalNot_native, ``atom_native,
    ``mvNth_native, ``mvNth_atom, ``mvNth_of_not_positive]
  for declaration in declarations do
    for axiomName in ← Lean.collectAxioms declaration do
      unless allowed.contains axiomName do
        throwError "{declaration} depends on unapproved axiom {axiomName}"
  Lean.logInfo m!"ACL2 pure helpers: audited {declarations.size} declarations"

end Silmaril.Logic.ACL2.Standard.Pure.Tests
