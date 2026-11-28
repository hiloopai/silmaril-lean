module

import Silmaril.Logic.ACL2.Standard.IntegerBits.Thms
import Lean

namespace Silmaril.Logic.ACL2.Standard.IntegerBits.Tests

open Object

private def ratio : Object := .rational (Rat.divInt 3 2)
private def complex : Object := ofParts 3 1

example : (integer (-13)).binaryLogand (integer (-10)) = integer (-14) := by decide +kernel
example : (integer (-1)).binaryLogand ratio = integer 0 := by
  rw [binaryLogand_neg_one_left]
  rfl
example : logand [] = integer (-1) ∧ logand [ratio] = ratio := by simp [logand]
example : logand [integer (-1), integer (-13), integer (-10)] = integer (-14) := by
  simp only [logand]
  decide +kernel
example : (integer (-13)).binaryLogior (integer (-10)) = integer (-9) := by decide +kernel
example : (integer (-13)).binaryLogxor (integer (-10)) = integer 5 := by decide +kernel
example : complex.binaryLogxor (integer (-13)) = integer (-13) := by decide +kernel
example : logior [nil] = nil ∧ logxor [complex] = complex := by simp [logior, logxor]
example : (integer (-13)).lognot = integer 12 ∧ ratio.lognot = integer (-1) := by decide
example : (integer (-13)).ash (integer (-2)) = integer (-4) := by decide +kernel
example : (integer (-13)).ash ratio = integer (-13) := by decide +kernel
example : ratio.ash (integer 16) = integer 0 := by decide +kernel
example : (integer (-1)).ash (integer 129) = integer (-(2 ^ 129)) := by decide +kernel
example : (integer (-13)).ash (integer (-129)) = integer (-1) := by decide +kernel
example : (integer (-4)).logbitp (integer 3) = truth := by decide +kernel
example : (integer 129).logbitp (integer (-13)) = truth := by decide +kernel
example : (integer 4).logbitp complex = nil := by decide +kernel
example : ratio.logbitp (integer (-13)) = truth := by decide +kernel
example : (integer 2).logbitp (integer (-13)) = nil := by decide +kernel
example : (integer (-257)).integerLength = integer 9 := by decide +kernel
example : (integer (-256)).integerLength = integer 8 := by decide +kernel
example : (integer (2 ^ 128)).integerLength = integer 129 := by decide +kernel
example : ratio.integerLength = integer 0 := by decide +kernel

-- The imported modules include the transitive axiom data for their proofs.
run_elab do
  let env ← Lean.getEnv
  let modules := #[`Silmaril.Logic.ACL2.Standard.IntegerBits.Defs,
    `Silmaril.Logic.ACL2.Standard.IntegerBits.Thms]
  let moduleIndices ← modules.mapM fun m => do
    let some index := env.getModuleIdx? m | throwError "Missing audited module {m}"
    pure index
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants do
    if (env.getModuleIdxFor? name).any moduleIndices.contains then
      for axiomName in ← Lean.collectAxioms name do
        unless allowed.contains axiomName do
          throwError "{name} depends on unapproved axiom {axiomName}"
      count := count + 1
  if count == 0 then throwError "No ACL2 integer bit declarations audited"
  Lean.logInfo m!"ACL2 integer bit operations: checked {count} declarations against the three-axiom ceiling"

end Silmaril.Logic.ACL2.Standard.IntegerBits.Tests
