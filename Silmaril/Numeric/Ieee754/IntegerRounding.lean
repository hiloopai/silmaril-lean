module

public import Silmaril.Numeric.Ieee754.RoundingCorrectness

/-!
# Correct integer rounding

`toInt?_finite_correct` relates the executable float-to-integer operation to
IEEE 754-2019 §§4.3 and 5.8's rounding directions, for arbitrary finite dyadic
inputs. Destination integer bounds and exception signaling are separate from
this unbounded integer theorem.
<https://standards.ieee.org/ieee/754/6210/>.
-/

@[expose] public section
namespace Silmaril.Numeric.Ieee754.Conformance
open Float.Model Float.Model.UnpackedFloat

/-- Unbounded integer conversion selects the mathematically nearest or directed
integer magnitude and applies the source sign, in all five rounding modes. -/
theorem toInt?_finite_correct (mode : RoundingMode) (sign : Sign) (n : Nat)
    (exponent : Int) (hn : 0 < n) :
    ∃ rounded : Nat,
      Rounding.toInt? mode (.finite sign n exponent hn) = some (sign.apply rounded) ∧
      MantissaRounds mode sign ((n : ℚ) * (2 : ℚ) ^ exponent) rounded := by
  by_cases he : 0 ≤ exponent
  · refine ⟨n <<< exponent.toNat, ?_, ?_⟩
    · simp [Rounding.toInt?, he]
    · have hvalue : (n : ℚ) * (2 : ℚ) ^ exponent = (n <<< exponent.toNat : Nat) := by
        simp only [Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        rw [← zpow_natCast, Int.toNat_of_nonneg he]
      rw [hvalue]
      exact exact_mantissaRounds mode sign _
  · let shifted := shiftToExponent n exponent .exact 0
    let rounded := Rounding.roundMantissa mode sign shifted.1.mantissa shifted.1.accuracy
    refine ⟨rounded, ?_, ?_⟩
    · simp only [Rounding.toInt?, show ¬exponent ≥ 0 from he, ↓reduceIte]
      rfl
    · have hc := shiftToExponent_round_correct mode sign n exponent 0 .exact (n : ℚ) rfl
      have ha : ((0 - exponent).toNat : Int) = -exponent := by
        rw [Int.toNat_of_nonneg (by omega)]
        omega
      have hvalue : (n : ℚ) / (2 : ℚ) ^ (0 - exponent).toNat =
          (n : ℚ) * (2 : ℚ) ^ exponent := by
        rw [← zpow_natCast (2 : ℚ), ha, zpow_neg]
        simp [div_eq_mul_inv]
      rw [hvalue] at hc
      exact hc

end Silmaril.Numeric.Ieee754.Conformance
