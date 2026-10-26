module

public import Silmaril.Numeric.Ieee754.Rounding.PackedError

/-! # Exact arithmetic before destination rounding -/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Rounding

open Float.Model Float.Model.UnpackedFloat LowPrecision

/-- Reuse the independent exact-arithmetic specification through scalar decoding. -/
theorem mulExact_value (x y : UnpackedFloat) (a b : ℚ)
    (hx : unpackedRat? x = some a) (hy : unpackedRat? y = some b) :
    unpackedRat? (mulExact x y) = some (a * b) := by
  simpa only [Conformance.value?_eq_unpackedRat] using Conformance.value?_mulExact
    ((Conformance.value?_eq_unpackedRat x).trans hx) ((Conformance.value?_eq_unpackedRat y).trans hy)

theorem addExact_value (mode : RoundingMode) (x y : UnpackedFloat) (a b : ℚ)
    (hx : unpackedRat? x = some a) (hy : unpackedRat? y = some b) :
    unpackedRat? (addExact mode x y) = some (a + b) := by
  simpa only [Conformance.value?_eq_unpackedRat] using Conformance.value?_addExact mode
    ((Conformance.value?_eq_unpackedRat x).trans hx) ((Conformance.value?_eq_unpackedRat y).trans hy)

/-- Uniform error of the executable packed multiplication. -/
theorem mulRounded_error (format : Format) (x y : UnpackedFloat) (a b : ℚ)
    (hx : unpackedRat? x = some a) (hy : unpackedRat? y = some b)
    (ho : NoOverflow format (roundUnpacked format .nearestTiesToEven (mulExact x y))) :
    ∃ r : ℚ, exactValue? (coreSpec format)
      (mulRounded format .nearestTiesToEven x y).toNat = some r ∧
      |(r : ℝ) - (a : ℝ) * (b : ℝ)| ≤
        unitRoundoff format * |(a : ℝ) * (b : ℝ)| + halfMinSubnormal format := by
  simpa only [mulRounded, Rat.cast_mul] using
    packRounded_error format (mulExact x y) (a * b) (mulExact_value x y a b hx hy) ho

/-- Uniform error of the executable packed addition. -/
theorem addRounded_error (format : Format) (x y : UnpackedFloat) (a b : ℚ)
    (hx : unpackedRat? x = some a) (hy : unpackedRat? y = some b)
    (ho : NoOverflow format (roundUnpacked format .nearestTiesToEven (addExact .nearestTiesToEven x y))) :
    ∃ r : ℚ, exactValue? (coreSpec format)
      (addRounded format .nearestTiesToEven x y).toNat = some r ∧
      |(r : ℝ) - ((a : ℝ) + (b : ℝ))| ≤
        unitRoundoff format * |(a : ℝ) + (b : ℝ)| + halfMinSubnormal format := by
  simpa only [addRounded, Rat.cast_add] using packRounded_error format _ (a + b)
    (addExact_value .nearestTiesToEven x y a b hx hy) ho

end Silmaril.Numeric.Ieee754.Rounding
