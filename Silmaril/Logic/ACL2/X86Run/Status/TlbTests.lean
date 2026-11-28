module

import Silmaril.Logic.ACL2.X86Run.Status.TlbThms
import Lean

namespace Silmaril.Logic.ACL2.X86Run.Status.Tlb.Tests

open Standard

example : arithmeticObservations.all (fun (n, d, quotient, floor, remainder) =>
    decide (Quotient.nonnegativeQuotient n.toNat d = quotient ∧
      Quotient.floorInteger n d = floor ∧ Quotient.modInteger n d = remainder)) = true := by
  decide +kernel

example : keyObservations.all (fun (x, key, good, mode) =>
    let access : Object := if keyP layout x then
      .integer (selectedBits layout.modeWidth layout.modeOffset x.natRank)
      else .nil
    decide (keyP layout x = key ∧ goodKeyP layout x = good ∧ access = mode)) = true := by
  decide +kernel

example : tlbObservations.all (fun (x, tlbOK, entries, entriesOK, stateOK, nativeMS, nativeFault) =>
    let primitives := recordPrimitives fieldRules recordFields
    let state : Object := .cons entries .nil
    decide (tlbP x = tlbOK ∧ primitives.entriesP entries = entriesOK ∧
      logicalStateP primitives state = stateOK ∧ ms.read primitives state = nativeMS ∧
      fault.read primitives state = nativeFault)) = true := by
  decide +kernel

private def withTlb : Object :=
  let (_, _, entries, _, _, _, _) := tlbObservations[4]'(by decide)
  .cons entries .nil

example (step : Object → Object) :
    (machineBindingsWithRecord step).run (.integer 2) withTlb = withTlb :=
  fault_exit (recordPrimitives fieldRules recordFields) step _ _ (by decide +kernel)

example (step : Object → Object) :
    halted.Holds (machineBindingsWithRecord step).admittedModel := halted_holds_with_record step

run_elab do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[``Quotient.quotient_eq_div, ``Quotient.floorRatio_eq_floor,
    ``Quotient.floorInteger_eq_div, ``Quotient.modInteger_eq_mod, ``selectedBits_native,
    ``selectedBits_eq_floor_mod, ``goodKeyP_native, ``entryP_native, ``tlbP_native, ``tlb_entry,
    ``machineBindingsWithRecord, ``halted_holds_with_record]
  for declaration in declarations do
    for axiomName in ← Lean.collectAxioms declaration do
      unless allowed.contains axiomName do
        throwError "{declaration} depends on unapproved axiom {axiomName}"
  Lean.logInfo m!"ACL2 logical TLB: audited {declarations.size} declarations"

end Silmaril.Logic.ACL2.X86Run.Status.Tlb.Tests
