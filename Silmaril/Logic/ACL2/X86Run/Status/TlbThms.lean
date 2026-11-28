module

public import Silmaril.Logic.ACL2.X86Run.Status.TlbSource
public import Silmaril.Logic.ACL2.X86Run.Status.EnvironmentThms
public import Silmaril.Logic.ACL2.Standard.Quotient.Thms
import Silmaril.Proofs.Logic.ACL2.X86Run.Tlb

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Run.Status.Tlb

open Standard

theorem selectedBits_native (l : Layout) (key : Nat) (valid : key < 2 ^ l.keyWidth) :
    (selectedBits l.modeWidth l.modeOffset key : Int) =
      Quotient.modInteger
        (Quotient.floorInteger (Quotient.modInteger key (2 ^ l.keyWidth)) (2 ^ l.modeOffset))
        (2 ^ l.modeWidth) :=
  Proofs.Logic.ACL2.X86Run.Tlb.selectedBits_native l key valid

/-- The arithmetic side of the native valid-key accessor theorem. -/
theorem selectedBits_eq_floor_mod (key : Nat) :
    (selectedBits layout.modeWidth layout.modeOffset key : Int) =
      Quotient.modInteger (Quotient.floorInteger key 64) 4 := by
  rw [Quotient.modInteger_eq_mod, Quotient.floorInteger_eq_div, Int.ofNat_ediv_ofNat, Int.ofNat_mod_ofNat]
  rfl

/-- Logical key validation, with the translated fix, floor and modulus on accepted keys. -/
theorem goodKeyP_native (l : Layout) (x : Object) : goodKeyP l x =
    (if keyP l x then
      decide (Quotient.modInteger
        (Quotient.floorInteger (Quotient.modInteger x.natRank (2 ^ l.keyWidth)) (2 ^ l.modeOffset))
        (2 ^ l.modeWidth) ≤ (l.maxMode : Int))
    else false) :=
  Proofs.Logic.ACL2.X86Run.Tlb.goodKeyP_native l x

theorem entryP_native (l : Layout) (x : Object) : entryP l x =
    (if x.consp then goodKeyP l x.car && unsignedByteP l.pageWidth x.cdr else false) := by
  cases x <;> rfl

/-- The non-NIL projection of the translated TLBP body on all stock objects. -/
theorem tlbP_native (x : Object) : tlbP x =
    (if x.consp then entryP layout x.car && tlbP x.cdr else decide (x = layout.marker)) := by
  cases x <;> rfl

def recordFields : FieldPredicates := Environment.fieldPredicatesWithEnvironment tlbP

/-- A singleton TLB entry is valid when its value is recognized and differs from the default. -/
theorem tlb_entry (x : Object) :
    entriesP fieldRules recordFields (.cons (.cons (.cons layout.marker .nil) x) .nil) =
      (tlbP x && decide (x ≠ layout.marker)) := by
  simp [entriesP, Object.car, recordFields, Object.nil]
  rfl

/-- Specialize the exported X86-RUN with both former record predicates fixed. -/
def machineBindingsWithRecord (step : Object → Object) : MachineBindings :=
  Environment.machineBindingsWithEnvironment tlbP step

theorem halted_holds_with_record (step : Object → Object) :
    halted.Holds (machineBindingsWithRecord step).admittedModel :=
  Environment.halted_holds_with_environment tlbP step

end Silmaril.Logic.ACL2.X86Run.Status.Tlb
