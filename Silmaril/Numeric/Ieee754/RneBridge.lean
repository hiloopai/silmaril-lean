module

public import Silmaril.Numeric.Ieee754.Normalization
public import Silmaril.Numeric.Ieee754.EncodingCorrectness

/-!
# Bridges between Lean's RNE model and explicit rounding

The results here connect the existing raw-wrapper arithmetic, backed by Lean's
binary32/binary64 model, to the rounding-mode-parametric definitions. They are
implementation equivalences, not assumptions about IEEE correctness; numerical
correctness of the shared rounding path is established separately.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Conformance

open Float.Model Float.Model.UnpackedFloat

@[simp] theorem roundMantissa_rne (sign : Sign) (mantissa : Nat) (accuracy : Accuracy) :
    Rounding.roundMantissa .nearestTiesToEven sign mantissa accuracy =
      accuracy.roundToNearestEven mantissa := by
  cases accuracy <;> rfl

@[simp] theorem roundWithAccuracy_rne (format : Format) (sign : Sign)
    (mantissa : Nat) (exponent : Int) (accuracy : Accuracy) :
    Rounding.roundWithAccuracy format .nearestTiesToEven sign mantissa exponent accuracy =
      UnpackedFloat.roundWithAccuracy format sign mantissa exponent accuracy := by
  simp only [Rounding.roundWithAccuracy, roundMantissa_rne,
    UnpackedFloat.roundWithAccuracy, ExtendedMantissa.roundedMantissa]
  rfl

@[simp] theorem packNormalized_rne (format : Format) (value : UnpackedFloat) :
    Rounding.packNormalized format .nearestTiesToEven value = value.pack format := by
  cases value <;> simp [Rounding.packNormalized, Rounding.overflowToInfinity]

@[simp] theorem roundUnpacked_rne_finite (format : Format) (sign : Sign)
    (mantissa : Nat) (exponent : Int) (positive : 0 < mantissa) :
    Rounding.roundUnpacked format .nearestTiesToEven (.finite sign mantissa exponent positive) =
      UnpackedFloat.round format sign mantissa exponent := by
  simp only [Rounding.roundUnpacked, roundWithAccuracy_rne, UnpackedFloat.round]

@[simp] theorem packRounded_rne_finite (format : Format) (sign : Sign)
    (mantissa : Nat) (exponent : Int) (positive : 0 < mantissa) :
    Rounding.packRounded format .nearestTiesToEven (.finite sign mantissa exponent positive) =
      (UnpackedFloat.round format sign mantissa exponent).pack format := by
  simp only [Rounding.packRounded, packNormalized_rne, roundUnpacked_rne_finite]

/-- The two definitions of signed exact dyadic normalization coincide under RNE. -/
@[simp] theorem roundUnpacked_ofDyadic_rne (format : Format) (mantissa exponent : Int)
    (zeroSign : Sign) :
    Rounding.roundUnpacked format .nearestTiesToEven (Rounding.ofDyadic mantissa exponent zeroSign) =
      UnpackedFloat.normalize format mantissa exponent zeroSign := by
  by_cases hz : mantissa = 0
  · subst mantissa
    rfl
  by_cases hn : mantissa < 0
  · have hc := Int.compare_eq_lt.mpr hn
    have habs : mantissa.natAbs = (-mantissa).toNat := by omega
    simp [Rounding.ofDyadic, hn, UnpackedFloat.normalize, hc, habs, show ¬0 ≤ mantissa by omega]
  · have hc := Int.compare_eq_gt.mpr (show 0 < mantissa by omega)
    have habs : mantissa.natAbs = mantissa.toNat := by omega
    simp [Rounding.ofDyadic, hn, UnpackedFloat.normalize, hc, habs, show ¬mantissa ≤ 0 by omega]

@[simp] theorem packRounded_ofDyadic_rne (format : Format) (mantissa exponent : Int)
    (zeroSign : Sign) :
    Rounding.packRounded format .nearestTiesToEven (Rounding.ofDyadic mantissa exponent zeroSign) =
      (UnpackedFloat.normalize format mantissa exponent zeroSign).pack format := by
  simp only [Rounding.packRounded, packNormalized_rne, roundUnpacked_ofDyadic_rne]

/-- Already normalized exact operands are unchanged by another RNE normalization. -/
theorem roundUnpacked_rne_eq_self (format : Format) (value : UnpackedFloat)
    (normalized : ExponentNormalized format value) :
    Rounding.roundUnpacked format .nearestTiesToEven value = value := by
  cases value with
  | infinity _ | zero _ | notANumber => rfl
  | finite sign mantissa exponent positive =>
    have hnorm : format.targetExponent (totalExponent mantissa exponent) = exponent := normalized
    have bounds := ExponentNormalized.finite_bounds format sign mantissa exponent positive normalized
    have hs := shiftToTargetExponent_noCarry format mantissa exponent bounds.2.1 bounds.1
    simp only [roundUnpacked_rne_finite, UnpackedFloat.round, hnorm, decreaseExponent,
      sub_self, Int.toNat_zero, Nat.shiftLeft_zero, Int.ofNat_zero, sub_zero]
    simp [UnpackedFloat.roundWithAccuracy, hs, ExtendedMantissa.roundedMantissa,
      ExtendedMantissa.ofMantissaAndAccuracy, ExtendedMantissa.accuracy,
      Accuracy.roundToNearestEven, Nat.ne_of_gt positive]

@[simp] theorem packRounded_rne_eq_pack (format : Format) (value : UnpackedFloat)
    (normalized : ExponentNormalized format value) :
    Rounding.packRounded format .nearestTiesToEven value = value.pack format := by
  simp only [Rounding.packRounded, roundUnpacked_rne_eq_self format value normalized, packNormalized_rne]

/-- Addition agrees on normalized source operands, including exact zero signs. -/
theorem addRounded_rne (format : Format) (x y : UnpackedFloat)
    (hx : ExponentNormalized format x) (hy : ExponentNormalized format y) :
    Rounding.addRounded format .nearestTiesToEven x y =
      (UnpackedFloat.add format x y).pack format := by
  cases x <;> cases y <;>
    simp_all [Rounding.addRounded, Rounding.addExact, UnpackedFloat.add,
      Rounding.cancellationSign, packRounded_rne_eq_pack]
  all_goals first | rfl | split <;> rfl

/-- When no left alignment is necessary, the two core rounding entry points agree. -/
theorem round_eq_roundWithAccuracy_of_ready (format : Format) (sign : Sign)
    (mantissa : Nat) (exponent : Int)
    (ready : exponent ≤ format.targetExponent (totalExponent mantissa exponent)) :
    UnpackedFloat.round format sign mantissa exponent =
      UnpackedFloat.roundWithAccuracy format sign mantissa exponent .exact := by
  have hshift : (exponent - format.targetExponent (totalExponent mantissa exponent)).toNat = 0 :=
    Int.toNat_of_nonpos (by omega)
  simp [UnpackedFloat.round, decreaseExponent, hshift]

/-- Every supported binary format has a nonpositive minimum subnormal exponent. -/
theorem minExponent_nonpos (format : Format) : format.minExponent ≤ 0 := by
  have hp : 2 ≤ format.mantissaBits := by
    have := format.hm
    simp only [Format.mantissaBits]
    omega
  have he : 1 ≤ format.exponentBits - 1 := by have := format.he; omega
  have hpow : 2 ≤ 2 ^ (format.exponentBits - 1) := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) he
  have hpowInt : (2 : Int) ≤ 2 ^ (format.exponentBits - 1) := by exact_mod_cast hpow
  simp only [Format.minExponent]
  omega

/-- Multiplying normalized source significands requires only a right shift:
if both are subnormal their exponent is already below the destination minimum. -/
theorem productExponent_ready (format : Format) (ls rs : Sign) (lm rm : Nat)
    (le re : Int) (lh : 0 < lm) (rh : 0 < rm)
    (hx : ExponentNormalized format (.finite ls lm le lh))
    (hy : ExponentNormalized format (.finite rs rm re rh)) :
    le + re ≤ format.targetExponent (totalExponent (lm * rm) (le + re)) := by
  have left := ExponentNormalized.finite_bounds format ls lm le lh hx
  have right := ExponentNormalized.finite_bounds format rs rm re rh hy
  have hmin := minExponent_nonpos format
  have hp : 0 < format.mantissaBits := by simp [Format.mantissaBits]
  have positive : 0 < lm * rm := Nat.mul_pos lh rh
  have hfull (h : 2 ^ (format.mantissaBits - 1) ≤ lm * rm) :
      le + re ≤ format.targetExponent (totalExponent (lm * rm) (le + re)) := by
    have hlog := (Nat.le_log2 (Nat.ne_of_gt positive)).mpr h
    unfold Format.targetExponent totalExponent
    omega
  rcases left.2.2 with hl | hl
  · rcases right.2.2 with hr | hr
    · unfold Format.targetExponent totalExponent
      omega
    · exact hfull (hr.trans (Nat.le_mul_of_pos_left rm lh))
  · exact hfull (hl.trans (Nat.le_mul_of_pos_right lm rh))

/-- Multiplication agrees on normalized source operands. -/
theorem mulRounded_rne (format : Format) (x y : UnpackedFloat)
    (hx : ExponentNormalized format x) (hy : ExponentNormalized format y) :
    Rounding.mulRounded format .nearestTiesToEven x y =
      (UnpackedFloat.mul format x y).pack format := by
  cases x <;> cases y <;>
    simp only [Rounding.mulRounded, Rounding.mulExact, UnpackedFloat.mul]
  all_goals first | rfl | skip
  rw [packRounded_rne_finite, round_eq_roundWithAccuracy_of_ready]
  exact productExponent_ready format _ _ _ _ _ _ _ _ hx hy

/-- Negation preserves the canonical-exponent invariant. -/
theorem ExponentNormalized.neg (format : Format) (value : UnpackedFloat)
    (normalized : ExponentNormalized format value) :
    ExponentNormalized format value.neg := by
  cases value <;> exact normalized

/-- Subtraction shares the addition bridge after exact sign inversion. -/
theorem subRounded_rne (format : Format) (x y : UnpackedFloat)
    (hx : ExponentNormalized format x) (hy : ExponentNormalized format y) :
    Rounding.subRounded format .nearestTiesToEven x y =
      (UnpackedFloat.sub format x y).pack format := by
  rw [Rounding.subRounded, addRounded_rne format x y.neg hx (hy.neg format y)]
  congr 1
  cases x <;> cases y <;> simp [UnpackedFloat.add, UnpackedFloat.sub, UnpackedFloat.neg]
  rename_i left lm le lh right rm re rh
  cases left <;> cases right <;> simp [Sign.apply, sub_eq_add_neg]

/-- FMA agrees with Lean's fused operation, including the unrounded exact
product in the finite, nonzero addend case. -/
theorem fmaRounded_rne (format : Format) (x y z : UnpackedFloat)
    (hx : ExponentNormalized format x) (hy : ExponentNormalized format y)
    (hz : ExponentNormalized format z) :
    Rounding.fmaRounded format .nearestTiesToEven x y z =
      (UnpackedFloat.fma format x y z).pack format := by
  cases x <;> cases y <;> cases z <;>
    simp_all [Rounding.fmaRounded, Rounding.mulExact, Rounding.addExact,
      UnpackedFloat.fma, Rounding.cancellationSign, packRounded_rne_eq_pack]
  all_goals first | rfl | skip
  all_goals try (split <;> rfl)
  rw [round_eq_roundWithAccuracy_of_ready]
  exact productExponent_ready format _ _ _ _ _ _ _ _ hx hy

/-- Division reuses exactly Lean's quotient and residual calculation under RNE. -/
theorem divRounded_rne (format : Format) (x y : UnpackedFloat) :
    Rounding.divRounded format .nearestTiesToEven x y =
      (UnpackedFloat.div format x y).pack format := by
  cases x <;> cases y <;>
    simp only [Rounding.divRounded, UnpackedFloat.div, roundWithAccuracy_rne, packNormalized_rne]

/-- Square root reuses exactly Lean's root and residual calculation under RNE. -/
theorem sqrtRounded_rne (format : Format) (x : UnpackedFloat) :
    Rounding.sqrtRounded format .nearestTiesToEven x =
      (UnpackedFloat.sqrt format x).pack format := by
  cases x with
  | infinity sign => cases sign <;> simp [Rounding.sqrtRounded, UnpackedFloat.sqrt]
  | zero sign => simp [Rounding.sqrtRounded, UnpackedFloat.sqrt]
  | notANumber => simp [Rounding.sqrtRounded, UnpackedFloat.sqrt]
  | finite sign mantissa exponent positive =>
    cases sign <;> simp [Rounding.sqrtRounded, UnpackedFloat.sqrt]

end Silmaril.Numeric.Ieee754.Conformance

namespace Silmaril.Numeric.Ieee754

namespace F32

/-- The raw model decoder satisfies the source-operand exponent invariant. -/
theorem model_unpack_normalized (x : F32) :
    Conformance.ExponentNormalized Float.Model.Format.binary32 x.model.unpack :=
  Conformance.unpack_exponent_normalized _ _

@[simp] theorem addWith_rne (x y : F32) : addWith .nearestTiesToEven x y = add x y := by
  simp only [addWith, Conformance.addRounded_rne _ _ _
    (model_unpack_normalized x) (model_unpack_normalized y)]
  rfl

@[simp] theorem subWith_rne (x y : F32) : subWith .nearestTiesToEven x y = sub x y := by
  simp only [subWith, Conformance.subRounded_rne _ _ _
    (model_unpack_normalized x) (model_unpack_normalized y)]
  rfl

@[simp] theorem mulWith_rne (x y : F32) : mulWith .nearestTiesToEven x y = mul x y := by
  simp only [mulWith, Conformance.mulRounded_rne _ _ _
    (model_unpack_normalized x) (model_unpack_normalized y)]
  rfl

@[simp] theorem fmaWith_rne (x y z : F32) :
    fmaWith .nearestTiesToEven x y z = fma x y z := by
  simp only [fmaWith, Conformance.fmaRounded_rne _ _ _ _
    (model_unpack_normalized x) (model_unpack_normalized y) (model_unpack_normalized z)]
  rfl

@[simp] theorem divWith_rne (x y : F32) : divWith .nearestTiesToEven x y = div x y := by
  simp only [divWith, Conformance.divRounded_rne]
  rfl

@[simp] theorem sqrtWith_rne (x : F32) : sqrtWith .nearestTiesToEven x = sqrt x := by
  simp only [sqrtWith, Conformance.sqrtRounded_rne]
  rfl

end F32

namespace F64

/-- The raw model decoder satisfies the source-operand exponent invariant. -/
theorem model_unpack_normalized (x : F64) :
    Conformance.ExponentNormalized Float.Model.Format.binary64 x.model.unpack :=
  Conformance.unpack_exponent_normalized _ _

@[simp] theorem addWith_rne (x y : F64) : addWith .nearestTiesToEven x y = add x y := by
  simp only [addWith, Conformance.addRounded_rne _ _ _
    (model_unpack_normalized x) (model_unpack_normalized y)]
  rfl

@[simp] theorem subWith_rne (x y : F64) : subWith .nearestTiesToEven x y = sub x y := by
  simp only [subWith, Conformance.subRounded_rne _ _ _
    (model_unpack_normalized x) (model_unpack_normalized y)]
  rfl

@[simp] theorem mulWith_rne (x y : F64) : mulWith .nearestTiesToEven x y = mul x y := by
  simp only [mulWith, Conformance.mulRounded_rne _ _ _
    (model_unpack_normalized x) (model_unpack_normalized y)]
  rfl

@[simp] theorem fmaWith_rne (x y z : F64) :
    fmaWith .nearestTiesToEven x y z = fma x y z := by
  simp only [fmaWith, Conformance.fmaRounded_rne _ _ _ _
    (model_unpack_normalized x) (model_unpack_normalized y) (model_unpack_normalized z)]
  rfl

@[simp] theorem divWith_rne (x y : F64) : divWith .nearestTiesToEven x y = div x y := by
  simp only [divWith, Conformance.divRounded_rne]
  rfl

@[simp] theorem sqrtWith_rne (x : F64) : sqrtWith .nearestTiesToEven x = sqrt x := by
  simp only [sqrtWith, Conformance.sqrtRounded_rne]
  rfl

end F64

end Silmaril.Numeric.Ieee754
