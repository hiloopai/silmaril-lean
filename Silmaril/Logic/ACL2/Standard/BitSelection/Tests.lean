module

import Silmaril.Logic.ACL2.Standard.BitSelection.Thms
import Lean

namespace Silmaril.Logic.ACL2.Standard.BitSelection.Tests

open Object

example : Source.observations.length = 31 := by decide +kernel
example : Source.observations.all (fun (actual, expected) => decide (actual = expected)) = true := by
  decide +kernel

-- Replacing the width by high - low drops the selected bit when the bounds coincide.
example : partSelectLowHigh (integer 16) (integer 4) (integer 4) ≠
    partSelectWidthLow (integer 16) (integer 0) (integer 4) := by decide +kernel

-- Fixing each bound before computing the width erases fractional cancellation.
example : partSelectLowHigh (integer 254) (rational (Rat.divInt 1 2)) (rational (Rat.divInt 5 2)) ≠
    partSelectLowHigh (integer 254) (integer 0) (integer 0) := by decide +kernel

run_elab do
  let env ← Lean.getEnv
  let modules := #[`Silmaril.Logic.ACL2.Standard.BitSelection.Defs,
    `Silmaril.Logic.ACL2.Standard.BitSelection.Source,
    `Silmaril.Logic.ACL2.Standard.BitSelection.Thms]
  let indices ← modules.mapM fun name => do
    let some index := env.getModuleIdx? name | throwError "Missing audited module {name}"
    pure index
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants do
    if (env.getModuleIdxFor? name).any indices.contains then
      for axiomName in ← Lean.collectAxioms name do
        unless allowed.contains axiomName do
          throwError "{name} depends on unapproved axiom {axiomName}"
      count := count + 1
  if count == 0 then throwError "No ACL2 bit selection declarations audited"
  Lean.logInfo m!"ACL2 bit selection: checked {count} declarations against the three-axiom ceiling"

end Silmaril.Logic.ACL2.Standard.BitSelection.Tests
