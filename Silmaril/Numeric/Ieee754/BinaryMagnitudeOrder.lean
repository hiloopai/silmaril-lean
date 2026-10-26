module

public import Silmaril.Numeric.Ieee754.BinaryMagnitude
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Data.Rat.Cast.Order

/-! # Order and parity of unsigned binary magnitudes

These utilities are independent of decimal formatting and make adjacent
encoding search reusable for exact rational conversion.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.BinaryMagnitude

theorem value_strictMono (fractionBits : Nat) (bias : Int) :
    StrictMono (value fractionBits bias) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [value_succ]
  exact lt_add_of_pos_right _ (spacing_pos fractionBits bias _)

@[simp] theorem value_zero (fractionBits : Nat) (bias : Int) : value fractionBits bias 0 = 0 := by
  simp [value, significand]

/-- The raw encoding and its restored significand have equal low-bit parity
whenever there is at least one trailing significand bit. -/
theorem significand_parity (fractionBits encoding : Nat) (positive : 0 < fractionBits) :
    significand fractionBits (encoding / radix fractionBits) (encoding % radix fractionBits) % 2 =
      encoding % 2 := by
  have evenRadix : 2 ∣ radix fractionBits := by
    unfold radix
    exact dvd_pow_self 2 (by omega : fractionBits ≠ 0)
  have remainder := Nat.mod_mod_of_dvd encoding evenRadix
  unfold significand
  split
  · exact remainder
  · rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd evenRadix, Nat.zero_add, Nat.mod_mod]
    exact remainder

end Silmaril.Numeric.Ieee754.BinaryMagnitude
