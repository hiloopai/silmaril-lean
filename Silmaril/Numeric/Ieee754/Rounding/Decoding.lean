module

public import Silmaril.Numeric.Ieee754.ScalarBridge
public import Silmaril.Numeric.Ieee754.Rounding.UnpackedError

/-! # Exact decoding bridge between scalar storage and unpacked arithmetic -/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Rounding

open Float.Model Float.Model.UnpackedFloat

theorem Magnitude.unique {value : UnpackedFloat} {a b : ℝ}
    (ha : Magnitude value a) (hb : Magnitude value b) : a = b := by
  cases value <;> simp_all [Magnitude]

/-- Exact rational decoding determines the same finite magnitude used by the rounder proof. -/
theorem magnitude_of_unpackedRat {value : UnpackedFloat} {q : ℚ}
    (h : LowPrecision.unpackedRat? value = some q) : Magnitude value |(q : ℝ)| := by
  cases value with
  | notANumber | infinity => simp [LowPrecision.unpackedRat?] at h
  | zero sign =>
    simp only [LowPrecision.unpackedRat?, Option.some.injEq] at h
    subst q
    simp [Magnitude]
  | finite sign m e hm =>
    cases sign <;> simp [LowPrecision.unpackedRat?, LowPrecision.signedRat] at h
    all_goals subst q
    all_goals simp only [Magnitude, Rat.cast_neg, Rat.cast_mul, Rat.cast_natCast, Rat.cast_zpow,
      Rat.cast_ofNat, abs_neg]
    all_goals exact abs_of_nonneg (mul_nonneg (Nat.cast_nonneg m) (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) e)))

end Silmaril.Numeric.Ieee754.Rounding
