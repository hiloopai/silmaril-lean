module

public import Silmaril.Numeric.Ieee754.Rounding.Exact

/-! # Uniform error bounds for scalar add and multiply

These theorems use the default policy: nearest-even rounding with gradual
underflow on both input and output, at the selected computation precision.
-/

@[expose] public section

namespace Silmaril.Numeric.Arithmetic

open Ieee754.Rounding LowPrecision

theorem storage_core_spec (format : ArithmeticFormat) :
    format.storage.spec = coreSpec format.core := by
  cases format <;> rfl

theorem output_toRat (format : ArithmeticFormat) (bits : BitVec format.core.numBits) :
    (output format {} bits).toRat? = exactValue? (coreSpec format.core) bits.toNat := by
  have hw : format.storage.width = format.core.numBits := by cases format <;> rfl
  simp only [output, Scalar.toRat?]
  change exactValue? format.storage.spec (bits.toNat % 2 ^ format.storage.width) = _
  rw [hw, Nat.mod_eq_of_lt bits.isLt, storage_core_spec]

/-- The exact sum, after rounding, remains below the reserved exponent field. -/
def AddNoOverflow (format : ArithmeticFormat) (x y : Value format) : Prop :=
  NoOverflow format.core (roundUnpacked format.core .nearestTiesToEven
    (addExact .nearestTiesToEven x.unpack y.unpack))

/-- The exact product, after rounding, remains below the reserved exponent field. -/
def MulNoOverflow (format : ArithmeticFormat) (x y : Value format) : Prop :=
  NoOverflow format.core (roundUnpacked format.core .nearestTiesToEven (mulExact x.unpack y.unpack))

theorem add_error (format : ArithmeticFormat) (x y : Value format) (a b : ℚ)
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) (ho : AddNoOverflow format x y) :
    ∃ r : ℚ, (add format x y).toRat? = some r ∧
      |(r : ℝ) - ((a : ℝ) + (b : ℝ))| ≤
        unitRoundoff format.core * |(a : ℝ) + (b : ℝ)| + halfMinSubnormal format.core := by
  have hx' : unpackedRat? x.unpack = some a := x.unpack_toRat.trans hx
  have hy' : unpackedRat? y.unpack = some b := y.unpack_toRat.trans hy
  obtain ⟨r, hr, herr⟩ := addRounded_error format.core x.unpack y.unpack a b hx' hy' ho
  refine ⟨r, ?_, herr⟩
  unfold add
  rw [output_toRat]
  exact hr

theorem mul_error (format : ArithmeticFormat) (x y : Value format) (a b : ℚ)
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) (ho : MulNoOverflow format x y) :
    ∃ r : ℚ, (mul format x y).toRat? = some r ∧
      |(r : ℝ) - (a : ℝ) * (b : ℝ)| ≤
        unitRoundoff format.core * |(a : ℝ) * (b : ℝ)| + halfMinSubnormal format.core := by
  have hx' : unpackedRat? x.unpack = some a := x.unpack_toRat.trans hx
  have hy' : unpackedRat? y.unpack = some b := y.unpack_toRat.trans hy
  obtain ⟨r, hr, herr⟩ := mulRounded_error format.core x.unpack y.unpack a b hx' hy' ho
  refine ⟨r, ?_, herr⟩
  unfold mul
  rw [output_toRat]
  exact hr

end Silmaril.Numeric.Arithmetic
