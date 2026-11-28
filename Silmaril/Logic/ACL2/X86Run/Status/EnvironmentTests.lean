module

import Silmaril.Logic.ACL2.X86Run.Status.EnvironmentThms
import Lean

namespace Silmaril.Logic.ACL2.X86Run.Status.Environment.Tests

open Standard

example : helperObservations.all (fun (key, x, entry, size, alist, proper, oracle) =>
    decide (assocEqual key x = entry ∧ len x = size ∧ alistP x = alist ∧
      x.trueListp = proper ∧ ripRetAlistP addressWidth x = oracle)) = true := by
  decide +kernel

-- These native records use ENV, FAULT, and MS. The TLB recognizer stays arbitrary.
example (tlb : Object → Bool) : environmentObservations.all
    (fun (_, x, envOK, entries, entriesOK, stateOK, nativeMS, nativeFault) =>
      let primitives := recordPrimitives fieldRules (fieldPredicatesWithEnvironment tlb)
      let state : Object := .cons entries .nil
      decide (envAlistP x = envOK ∧ primitives.entriesP entries = entriesOK ∧
        logicalStateP primitives state = stateOK ∧ ms.read primitives state = nativeMS ∧
        fault.read primitives state = nativeFault)) = true := rfl

private def withEnvironment : Object :=
  let (_, _, _, entries, _, _, _, _) := environmentObservations[3]'(by decide)
  .cons entries .nil

example (tlb : Object → Bool) (step : Object → Object) :
    (machineBindingsWithEnvironment tlb step).run (.integer 2) withEnvironment = withEnvironment :=
  fault_exit (recordPrimitives fieldRules (fieldPredicatesWithEnvironment tlb)) step _ _
    (by intro h; contradiction)

example (tlb : Object → Bool) (step : Object → Object) :
    halted.Holds (machineBindingsWithEnvironment tlb step).admittedModel :=
  halted_holds_with_environment tlb step

run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[``alistP_native, ``len_native, ``assocEqual_native, ``trueListp_native,
    ``signedByteP_iff, ``ripRetAlistP_native, ``envAlistP_native, ``env_entry,
    ``machineBindingsWithEnvironment, ``halted_holds_with_environment]
  for declaration in declarations do
    for axiomName in ← Lean.collectAxioms declaration do
      unless allowed.contains axiomName do
        throwError "{declaration} depends on unapproved axiom {axiomName}"
  Lean.logInfo m!"ACL2 logical environment: audited {declarations.size} declarations"

end Silmaril.Logic.ACL2.X86Run.Status.Environment.Tests
