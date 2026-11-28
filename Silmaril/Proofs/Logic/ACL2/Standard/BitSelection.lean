module

public import Silmaril.Logic.ACL2.Standard.BitSelection.Source
public import Silmaril.Logic.ACL2.Standard.IntegerBits.Thms
public import Silmaril.Logic.ACL2.Standard.Quotient.Thms
import Silmaril.Logic.ACL2.Standard.Objects.Thms

@[expose] public section

namespace Silmaril.Proofs.Logic.ACL2.Standard.BitSelection

open Silmaril.Logic.ACL2.Standard
open Object
open Silmaril.Logic.ACL2.Standard.BitSelection

private theorem expt2_integerFix (n : Object) :
    (Source.expt2 n).integerFix = (2 ^ n.natRank : Nat) := by
  simp [Source.expt2, nfix]

private theorem floorIntegers_nat (x : Int) (d : Nat) :
    Source.floorIntegers x d = integer (x / d) :=
  congrArg integer (Quotient.floorInteger_eq_div x d)

private theorem modIntegers_nat (x : Int) (d : Nat) :
    Source.modIntegers x d = integer (x % d) :=
  congrArg integer (Quotient.modInteger_eq_mod x d)

theorem loghead_source (width x : Object) : loghead width x = Source.loghead width x := by
  simp only [Source.loghead, Source.imod, ← integer_integerFix, integerFix_integer,
    expt2_integerFix, modIntegers_nat, loghead]

theorem logtail_source (low x : Object) : logtail low x = Source.logtail low x := by
  simp only [Source.logtail, Source.ifloor, ← integer_integerFix, integerFix_integer,
    expt2_integerFix, floorIntegers_nat, logtail]

theorem logtail_ash (low x : Object) : logtail low x = x.ash (integer (-(low.natRank : Int))) := by
  rw [ash_eq, integerFix_integer]
  by_cases zero : low.natRank = 0
  · simp [logtail, zero]
  · simp [logtail, zero]

theorem selectionWidth_parts (low high : Object) :
    selectionWidth low high = ofParts (1 + (high.real - low.real)) (high.imag - low.imag) := by
  simp only [selectionWidth, binaryAdd, unaryMinus, real_ofParts, imag_ofParts, integer]
  change ofParts (1 + (high.real + -low.real)) (0 + (high.imag + -low.imag)) = _
  rw [Rat.zero_add, ← Rat.sub_eq_add_neg, ← Rat.sub_eq_add_neg]

theorem selectionWidth_integer (low high : Int) :
    selectionWidth (integer low) (integer high) = integer (1 + (high - low)) := by
  rw [selectionWidth_parts]
  simp only [integer, real, imag]
  rw [Rat.sub_self, ofParts_zero]
  change rational (1 + ((high : Rat) - (low : Rat))) = rational ((1 + (high - low) : Int) : Rat)
  simp

theorem loghead_range (width x : Object) :
    0 ≤ (loghead width x).integerFix ∧ (loghead width x).integerFix < (2 ^ width.natRank : Nat) := by
  have positive : (0 : Int) < (2 ^ width.natRank : Nat) := by exact_mod_cast Nat.two_pow_pos _
  simp only [loghead, integerFix_integer]
  exact ⟨Int.emod_nonneg _ (ne_of_gt positive), Int.emod_lt_of_pos _ positive⟩

end Silmaril.Proofs.Logic.ACL2.Standard.BitSelection
