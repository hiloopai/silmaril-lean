module

public import Silmaril.Numeric.Ieee754.ComparisonCorrectness
public import Silmaril.Numeric.Ieee754.ArithmeticCorrectness
public import Silmaril.Numeric.Ieee754.Rounding.ScalarError

/-! # Exact maximum at scalar computation precision

Maximum selects a source value. The conversion lemmas below account for the
implementation's binary64 comparison and repacking into the source precision.
-/

@[expose] public section
namespace Silmaril.Numeric.Ieee754.Rounding
open Float.Model Float.Model.UnpackedFloat LowPrecision

/-- The generic storage decoder and core IEEE decoder agree on every field,
including signed zero, infinity and NaN. -/
theorem unpackBits_core (format : Format) (bits : BitVec format.numBits) :
    unpackBits (coreSpec format) bits.toNat = UnpackedFloat.unpack format bits := by
  have hs : (if signBit (coreSpec format) bits.toNat then Sign.negative else Sign.positive) =
      Sign.ofBitVec (unpackSign bits) := by
    rw [signBit_core]
    by_cases h : unpackSign bits = 0#1
    · simp [h, Sign.ofBitVec]
    · have hnat : (unpackSign bits).toNat = 1 := by
        have hb := (unpackSign bits).isLt
        have hn : (unpackSign bits).toNat ≠ 0 := fun he => h (BitVec.eq_of_toNat_eq he)
        norm_num at hb
        omega
      simp [h, hnat, Sign.ofBitVec]
  have hemax : (unpackExponent (spec := format) bits).toNat =
      2 ^ format.exponentBits - 1 ↔ unpackExponent bits = -1#_ := by
    rw [← BitVec.toNat_inj, BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes]
  have hezero : (unpackExponent (spec := format) bits).toNat = 0 ↔
      unpackExponent bits = 0#_ := by rw [← BitVec.toNat_inj]; rfl
  have hmzero : (unpackMantissa (spec := format) bits).toNat = 0 ↔
      unpackMantissa bits = 0#_ := by rw [← BitVec.toNat_inj]; rfl
  unfold unpackBits isNaNBits isInfinityBits encodingSign
  change (if (exponentField (coreSpec format) bits.toNat == 2 ^ format.exponentBits - 1 &&
      fractionField (coreSpec format) bits.toNat != 0) then UnpackedFloat.notANumber
    else if (exponentField (coreSpec format) bits.toNat == 2 ^ format.exponentBits - 1 &&
      fractionField (coreSpec format) bits.toNat == 0) then _ else _) = _
  simp only [fractionField_core, exponentField_core]
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, hemax, hezero, hmzero]
  rw [hs]
  unfold UnpackedFloat.unpack
  by_cases he : unpackExponent (spec := format) bits = -1#_
  · by_cases hm : unpackMantissa (spec := format) bits = 0#_ <;> simp [he, hm]
  · by_cases hz : unpackExponent (spec := format) bits = 0#_
    · by_cases hm : unpackMantissa (spec := format) bits = 0#_
      · simp [hz, hm]
      · simp [hz, hm, coreSpec]
        have heq : (1 : Int) - format.exponentBias - format.mantissaBitsWithoutImplicit =
            - (format.mantissaBitsWithoutImplicit : Int) + -(format.exponentBias : Int) + 1 := by omega
        simp only [heq]
    · simp [he, hz, coreSpec]
      constructor
      · simpa only [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 1)]
          using (Conformance.normalMantissa_toNat format (unpackMantissa bits)).symm
      · omega

end Silmaril.Numeric.Ieee754.Rounding

namespace Silmaril.Numeric.Ieee754.Conformance
open Float.Model Float.Model.UnpackedFloat

/-- Equal finite rational values have the same overflow status in canonical
form. Signed zeros may differ, and are harmless to the exponent condition. -/
theorem noExponentOverflow_of_value_eq (format : Format) (x y : UnpackedFloat) (q : ℚ)
    (nx : ExponentNormalized format x) (ny : ExponentNormalized format y)
    (hx : value? x = some q) (hy : value? y = some q)
    (ho : NoExponentOverflow format x) : NoExponentOverflow format y := by
  have hc := compare_finite format x y q q nx ny hx hy
  rw [compare_eq_iff_eq.mpr rfl] at hc
  cases y with
  | notANumber | infinity | zero => trivial
  | finite sy my ey py =>
    cases x with
    | notANumber | infinity => simp [value?] at hx
    | zero sx => cases sy <;> simp [UnpackedFloat.compare] at hc
    | finite sx mx ex px =>
      cases sx <;> cases sy <;> simp only [UnpackedFloat.compare] at hc
      all_goals try (cases hc)
      all_goals
        have hcmp : compare ex ey = .eq := by
          cases he : compare ex ey <;> simp_all [Ordering.then, Ordering.swap]
        have he := compare_eq_iff_eq.mp hcmp
        simpa only [NoExponentOverflow, ← he] using ho

/-- Repacking a rational value already representable in the destination is
exact. The input may use a different normalized exponent or precision. -/
theorem packRounded_exact_of_representative (format : Format) (source value : UnpackedFloat)
    (q : ℚ) (normalized : ExponentNormalized format source)
    (inRange : NoExponentOverflow format source)
    (hs : value? source = some q) (hv : value? value = some q) :
    value? (UnpackedFloat.unpack format
      (Rounding.packRounded format .nearestTiesToEven value)) = some q := by
  obtain ⟨r, hr, optimal⟩ := roundUnpacked_rne_optimal_of_value format value q hv
  have hnear := optimal.nearest q (normalized_value_representable format source q normalized hs)
  have heq : r = q := by
    rw [sub_self, abs_zero] at hnear
    exact (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hnear (abs_nonneg _)))).symm
  subst r
  have hn := roundUnpacked_normalized format .nearestTiesToEven value
  have ho := noExponentOverflow_of_value_eq format source _ q normalized hn hs hr inRange
  rw [unpack_packRounded format .nearestTiesToEven value ho]
  exact hr

end Silmaril.Numeric.Ieee754.Conformance

namespace Silmaril.Numeric.Ieee754.F64
open Float.Model Float.Model.UnpackedFloat Conformance

theorem isNaN_eq_false_of_toRat {x : F64} {q : ℚ} (hx : x.toRat? = some q) :
    x.isNaN = false := by
  have he : (decode64 x.bits.toNat).exponent ≠ maxExponentField binary64ExponentBits := by
    intro h
    simp [toRat?, value64?, finiteValue, h] at hx
  unfold isNaN IsNaN classify64 classify
  simp only [beq_iff_eq, he, ite_false]
  split
  · split <;> simp_all
  · rfl

theorem equal_iff_of_toRat {x y : F64} {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) : x.equal y = true ↔ a = b := by
  have hc := compare_finite .binary64 x.model.unpack y.model.unpack a b
    (unpack_exponent_normalized _ _) (unpack_exponent_normalized _ _)
    ((value?_model_unpack64 x).trans hx) ((value?_model_unpack64 y).trans hy)
  change (x.model.unpack.compare y.model.unpack == some .eq) = true ↔ _
  rw [hc]
  simp only [beq_iff_eq, Option.some.injEq, compare_eq_iff_eq]

theorem lessThan_iff_of_toRat {x y : F64} {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) : x.lessThan y = true ↔ a < b := by
  have hc := compare_finite .binary64 x.model.unpack y.model.unpack a b
    (unpack_exponent_normalized _ _) (unpack_exponent_normalized _ _)
    ((value?_model_unpack64 x).trans hx) ((value?_model_unpack64 y).trans hy)
  change decide ((x.model.unpack.compare y.model.unpack == some .lt) = true) = true ↔ _
  rw [hc]
  simp only [decide_eq_true_eq, beq_iff_eq, Option.some.injEq, compare_lt_iff_lt]

/-- NaN-propagating binary64 maximum selects the exact rational maximum.
Its signed-zero preference has no effect on this numerical statement. -/
theorem maximum_toRat {x y : F64} {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) :
    (x.maximum y).toRat? = some (max a b) := by
  unfold maximum
  rw [isNaN_eq_false_of_toRat hx, isNaN_eq_false_of_toRat hy]
  simp only [Bool.false_or, Bool.false_eq_true, ite_false]
  by_cases he : x.equal y = true
  · have hab := (equal_iff_of_toRat hx hy).mp he
    subst b
    rw [ite_eq_left he, max_self]
    split <;> assumption
  · rw [ite_eq_right he]
    by_cases hl : x.lessThan y = true
    · rw [ite_eq_left hl, max_eq_right ((lessThan_iff_of_toRat hx hy).mp hl).le]
      exact hy
    · rw [ite_eq_right hl, max_eq_left (le_of_not_gt (fun h => hl ((lessThan_iff_of_toRat hx hy).mpr h)))]
      exact hx

end Silmaril.Numeric.Ieee754.F64

namespace Silmaril.Numeric.Scalar
open Ieee754 Ieee754.Conformance Float.Model Float.Model.UnpackedFloat

theorem unpack32_core (x : Scalar .f32) :
    x.unpack = UnpackedFloat.unpack .binary32 x.bits :=
  Rounding.unpackBits_core .binary32 x.bits

theorem unpack32_normalized (x : Scalar .f32) : ExponentNormalized .binary32 x.unpack := by
  rw [unpack32_core]
  exact unpack_exponent_normalized _ _

theorem unpack32_upper (x : Scalar .f32) :
    match x.unpack with | .finite _ _ e _ => e ≤ 104 | _ => True := by
  rw [unpack32_core]
  exact unpack32_finite_exponent_le _

theorem unpack32_noOverflow (x : Scalar .f32) : NoExponentOverflow .binary32 x.unpack := by
  have h := x.unpack32_upper
  cases hu : x.unpack with
  | notANumber | infinity | zero => trivial
  | finite s m e hpos =>
    rw [hu] at h
    change e ≤ 104 at h
    change (e + 127 + 23).toNat < 255
    omega

/-- Widening scalar binary32 into the implementation's comparison precision
preserves every finite rational value. -/
theorem toF64_toRat32 (x : Scalar .f32) : x.toF64.toRat? = x.toRat? := by
  rw [← value?_model_unpack64]
  change value? (UnpackedFloat.unpack .binary64
    (UnpackedFloat.pack .binary64 (UnpackedFloat.unpack .binary64
      (Rounding.packRounded .binary64 .nearestTiesToEven x.unpack)))) = _
  rw [value?_unpack_pack_unpack, value?_widen32 _ _ x.unpack32_upper x.unpack32_normalized]
  exact value?_scalar_unpack x

end Silmaril.Numeric.Scalar

namespace Silmaril.Numeric.Arithmetic
open Ieee754 Ieee754.Conformance Float.Model Float.Model.UnpackedFloat

theorem output32_unpack (bits : BitVec Format.binary32.numBits) :
    (output .f32 {} bits).unpack = UnpackedFloat.unpack .binary32 bits := by
  change (⟨BitVec.ofNat 32 bits.toNat⟩ : Scalar .f32).unpack = _
  rw [Scalar.unpack32_core]
  congr 1
  apply BitVec.eq_of_toNat_eq
  change bits.toNat % 2 ^ 32 = bits.toNat
  exact Nat.mod_eq_of_lt bits.isLt

/-- Returning an exactly widened binary32 value to binary32 loses no value. -/
theorem repack32_exact (source : Value .f32) (value : F64) (q : ℚ)
    (hs : source.toRat? = some q) (hv : value.toRat? = some q) :
    (output .f32 {} (Rounding.packRounded .binary32 .nearestTiesToEven value.model.unpack)).toRat? =
      some q := by
  rw [← value?_scalar_unpack, output32_unpack]
  exact packRounded_exact_of_representative .binary32 source.unpack value.model.unpack q
    source.unpack32_normalized source.unpack32_noOverflow
    ((value?_scalar_unpack source).trans hs) ((value?_model_unpack64 value).trans hv)

/-- The actual scalar maximum is exact for finite binary32 operands under the
default gradual-underflow policy. No rounding or overflow premise is needed. -/
theorem maximum32_toRat (x y : Value .f32) (a b : ℚ)
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) :
    (maximum .f32 x y).toRat? = some (max a b) := by
  have hx' : x.toF64.toRat? = some a := x.toF64_toRat32.trans hx
  have hy' : y.toF64.toRat? = some b := y.toF64_toRat32.trans hy
  have hm := F64.maximum_toRat hx' hy'
  change (output .f32 {} (Rounding.packRounded .binary32 .nearestTiesToEven
    (x.toF64.maximum y.toF64).model.unpack)).toRat? = _
  rcases le_total a b with h | h
  · rw [max_eq_right h] at hm ⊢
    exact repack32_exact y _ b hy hm
  · rw [max_eq_left h] at hm ⊢
    exact repack32_exact x _ a hx hm

end Silmaril.Numeric.Arithmetic

namespace Silmaril.Numeric.Ieee754.F64
open Float.Model Float.Model.UnpackedFloat Conformance

/-- The raw binary64 negative infinity used as the maximum identity. -/
def negativeInfinity : F64 := ofBits 0xfff0000000000000

theorem negativeInfinity_unpack : negativeInfinity.model.unpack = .infinity .negative := rfl

theorem negativeInfinity_isNaN : negativeInfinity.isNaN = false := rfl

theorem maximum_negativeInfinity_left {y : F64} {q : ℚ} (hy : y.toRat? = some q) :
    negativeInfinity.maximum y = y := by
  have hv := (value?_model_unpack64 y).trans hy
  have hc : negativeInfinity.model.unpack.compare y.model.unpack = some .lt := by
    rw [negativeInfinity_unpack]
    cases hu : y.model.unpack <;> simp_all [value?, UnpackedFloat.compare]
  have he : negativeInfinity.equal y = false := by
    change (negativeInfinity.model.unpack.compare y.model.unpack == some .eq) = false
    rw [hc]
    rfl
  have hl : negativeInfinity.lessThan y = true := by
    change decide ((negativeInfinity.model.unpack.compare y.model.unpack == some .lt) = true) = true
    rw [hc]
    rfl
  simp only [maximum, negativeInfinity_isNaN, isNaN_eq_false_of_toRat hy,
    Bool.false_or, Bool.false_eq_true, ite_false, he, hl, ite_true]

theorem maximum_negativeInfinity_right {x : F64} {q : ℚ} (hx : x.toRat? = some q) :
    x.maximum negativeInfinity = x := by
  have hv := (value?_model_unpack64 x).trans hx
  have hc : x.model.unpack.compare negativeInfinity.model.unpack = some .gt := by
    rw [negativeInfinity_unpack]
    cases hu : x.model.unpack <;> simp_all [value?, UnpackedFloat.compare]
  have he : x.equal negativeInfinity = false := by
    change (x.model.unpack.compare negativeInfinity.model.unpack == some .eq) = false
    rw [hc]
    rfl
  have hl : x.lessThan negativeInfinity = false := by
    change decide ((x.model.unpack.compare negativeInfinity.model.unpack == some .lt) = true) = false
    rw [hc]
    rfl
  simp only [maximum, negativeInfinity_isNaN, isNaN_eq_false_of_toRat hx,
    Bool.false_or, Bool.false_eq_true, ite_false, he, hl]

theorem maximum_negativeInfinity_self :
    negativeInfinity.maximum negativeInfinity = negativeInfinity := rfl

end Silmaril.Numeric.Ieee754.F64
