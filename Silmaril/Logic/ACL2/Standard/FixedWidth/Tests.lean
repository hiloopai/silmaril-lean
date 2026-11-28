module

import Silmaril.Logic.ACL2.Standard.FixedWidth.Thms
import Lean

namespace Silmaril.Logic.ACL2.Standard.FixedWidth.Tests

open Object

example : Source.observations.all (fun (x, fixed, adr, num, nxt) =>
    decide (x.prefixesFix = fixed ∧ x.prefixesAdr = adr ∧ x.prefixesNum = num ∧ x.prefixesNxt = nxt)) = true := by
  decide +kernel

-- A field crossing the container boundary must keep the fix.
example : fixedWidthProjection 4 2 3 (integer 16) ≠
    partSelectWidthLow (integer 16) (integer 2) (integer 3) := by
  decide +kernel

run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[``fixedWidthProjection, ``prefixesFix, ``prefixesAdr, ``prefixesNum, ``prefixesNxt,
    ``Source.prefixesFix, ``Source.prefixesAdr, ``Source.prefixesNum, ``Source.prefixesNxt,
    ``fixedWidthProjection_eq_select, ``fixedWidthProjection_range,
    ``fixedWidthProjection_of_noninteger, ``prefixesFix_source, ``prefixesAdr_source,
    ``prefixesNum_source, ``prefixesNxt_source, ``prefixesAdr_eq_select,
    ``prefixesNum_eq_select, ``prefixesNxt_eq_select]
  for declaration in declarations do
    for axiomName in ← Lean.collectAxioms declaration do
      unless allowed.contains axiomName do
        throwError "{declaration} depends on unapproved axiom {axiomName}"
  Lean.logInfo m!"ACL2 fixed-width object projections: audited {declarations.size} declarations"

end Silmaril.Logic.ACL2.Standard.FixedWidth.Tests
