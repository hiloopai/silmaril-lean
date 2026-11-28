module

import Silmaril.Logic.ACL2.Standard.FixedLayout.Thms
import Lean

namespace Silmaril.Logic.ACL2.Standard.FixedLayout.Tests

open Object

example : Source.observations.length = 18 := by decide +kernel
example : Source.observations.all (fun (actual, expected) => decide (actual = expected)) = true := by
  decide +kernel

-- Off-guard writes extend the logical list instead of clipping the index.
example : Toy.writeCell (integer 4) (integer 5) (Toy.encode (-2) [7, 8, 9]) ≠
    Toy.writeCell (integer 2) (integer 5) (Toy.encode (-2) [7, 8, 9]) := by decide +kernel

-- Distinct index objects can denote the same logical slot.
example : Toy.readCell (integer (-4)) (Toy.writeCell (string [120]) (integer 5) Toy.initial) =
    integer 5 := by decide +kernel

run_elab do
  let env ← Lean.getEnv
  let modules := #[`Silmaril.Logic.ACL2.Standard.FixedLayout.Defs,
    `Silmaril.Logic.ACL2.Standard.FixedLayout.Source,
    `Silmaril.Logic.ACL2.Standard.FixedLayout.Thms]
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
  if count == 0 then throwError "No ACL2 fixed-layout declarations audited"
  Lean.logInfo m!"ACL2 fixed layout: checked {count} declarations against the three-axiom ceiling"

end Silmaril.Logic.ACL2.Standard.FixedLayout.Tests
