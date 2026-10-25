module

public import Silmaril.Numeric.Ieee754.Operations

/-!
# Deterministic results belong to the permitted NaN relations

The core float models carry a validity proof forcing their NaN encoding to the
positive canonical quiet NaN. The lemmas below connect that invariant to the
raw wrappers' decidable NaN classes and prove that the deterministic evaluators
are members of their corresponding result relations.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754

open Float.Model Float.Model.UnpackedFloat

private theorem nan_fields {w t : Nat} {d : Decoded} (h : classify w t d = .nan) :
    d.exponent = maxExponentField w ∧ d.trailingSignificand ≠ 0 := by
  unfold classify at h
  split at h
  · split at h <;> contradiction
  · split at h
    · split at h
      · contradiction
      · simp_all
    · contradiction

namespace F32

/-- A model-derived NaN is exactly the positive canonical quiet encoding. -/
theorem ofModel_nan_eq (x : Float32.Model) (h : (ofModel x).IsNaN) :
    ofModel x = canonicalNaN := by
  have fields := nan_fields h
  have hexp : unpackExponent (spec := Format.binary32) x.toBits.toBitVec = (-1#_) := by
    apply BitVec.eq_of_toNat_eq
    simpa [unpackExponent, decode32, decode, field, maxExponentField,
      binary32ExponentBits, binary32SignificandBits, Nat.shiftRight_eq_div_pow,
      ofModel] using fields.1
  have hmant : unpackMantissa (spec := Format.binary32) x.toBits.toBitVec ≠ 0#_ := by
    intro hm
    apply fields.2
    have hn := congrArg BitVec.toNat hm
    simpa [unpackMantissa, decode32, decode, field, binary32ExponentBits,
      binary32SignificandBits, Nat.shiftRight_eq_div_pow, ofModel] using hn
  have hbits := x.valid.eq_packedNaN hexp hmant
  have hu : x.toBits = Float32.Model.nan.toBits := UInt32.eq_of_toBitVec_eq hbits
  change (⟨x.toBits⟩ : F32) = ⟨Float32.Model.nan.toBits⟩
  rw [hu]

/-- Every model-derived result has no noncanonical NaN payload. -/
theorem ofModel_isCanonicalized (x : Float32.Model) : (ofModel x).IsNonNaNOrCanonicalNaN := by
  by_cases h : (ofModel x).IsNaN
  · exact Or.inr (by rw [ofModel_nan_eq x h]; exact canonicalNaN_isCanonical)
  · exact Or.inl h

/-- A canonical NaN, of either sign, is also an arithmetic NaN. -/
theorem IsCanonicalNaN.isArithmeticNaN {x : F32} (h : x.IsCanonicalNaN) :
    x.IsArithmeticNaN := by
  rcases h with ⟨hnan, hbits⟩
  refine ⟨hnan, ?_⟩
  change x.bits.toNat % 2 ^ 23 ≥ 2 ^ 22
  have hb := congrArg UInt32.toNat hbits
  change x.bits.toNat &&& (2 ^ 31 - 1) = 2143289344 at hb
  rw [Nat.and_two_pow_sub_one_eq_mod] at hb
  have hr := congrArg (fun n => n % 2 ^ 23) hb
  rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 23 ∣ 2 ^ 31)] at hr
  omega

/-- A deterministic binary result is permitted whenever its NaNs are canonical. -/
theorem binaryResult_self (eval : F32 → F32 → F32) (x y : F32)
    (h : (eval x y).IsNonNaNOrCanonicalNaN) : binaryResult eval x y (eval x y) := by
  unfold binaryResult
  split
  next hn =>
    have hc := h.resolve_left (not_not_intro hn)
    split
    · exact hc
    · exact hc.isArithmeticNaN
  next => rfl

/-- A deterministic unary result is permitted whenever its NaNs are canonical. -/
theorem unaryResult_self (eval : F32 → F32) (x : F32)
    (h : (eval x).IsNonNaNOrCanonicalNaN) : unaryResult eval x (eval x) := by
  unfold unaryResult
  split
  next hn =>
    have hc := h.resolve_left (not_not_intro hn)
    split
    · exact hc
    · exact hc.isArithmeticNaN
  next => rfl

/-- A deterministic FMA result is permitted by the analogous NaN policy. -/
theorem fmaNaNResult_self (eval : F32 → F32 → F32 → F32) (x y z : F32)
    (h : (eval x y z).IsNonNaNOrCanonicalNaN) : fmaNaNResult eval x y z (eval x y z) := by
  unfold fmaNaNResult
  split
  next hn =>
    have hc := h.resolve_left (not_not_intro hn)
    split
    · exact hc
    · exact hc.isArithmeticNaN
  next => rfl

theorem addRel_self (x y : F32) : addRel x y (add x y) :=
  binaryResult_self add x y (ofModel_isCanonicalized _)

theorem subRel_self (x y : F32) : subRel x y (sub x y) :=
  binaryResult_self sub x y (ofModel_isCanonicalized _)

theorem mulRel_self (x y : F32) : mulRel x y (mul x y) :=
  binaryResult_self mul x y (ofModel_isCanonicalized _)

theorem divRel_self (x y : F32) : divRel x y (div x y) :=
  binaryResult_self div x y (ofModel_isCanonicalized _)

theorem sqrtRel_self (x : F32) : sqrtRel x (sqrt x) :=
  unaryResult_self sqrt x (ofModel_isCanonicalized _)

theorem fmaNaNRel_self (x y z : F32) : fmaNaNRel x y z (fma x y z) :=
  fmaNaNResult_self fma x y z (ofModel_isCanonicalized _)


/-- Packing respects the canonical-NaN invariant even under directed overflow. -/
theorem packNormalized_isCanonicalized (mode : RoundingMode) (value : UnpackedFloat) :
    (⟨UInt32.ofBitVec (Rounding.packNormalized Format.binary32 mode value)⟩ : F32).IsNonNaNOrCanonicalNaN := by
  cases value with
  | finite sign mantissa exponent hpos =>
    simp only [Rounding.packNormalized]
    split
    · cases sign <;> exact Or.inl (by decide)
    · exact ofModel_isCanonicalized (Float32.Model.pack (.finite sign mantissa exponent hpos))
  | notANumber => exact ofModel_isCanonicalized (Float32.Model.pack .notANumber)
  | infinity sign => exact ofModel_isCanonicalized (Float32.Model.pack (.infinity sign))
  | zero sign => exact ofModel_isCanonicalized (Float32.Model.pack (.zero sign))

/-- Any directly rounded result has a canonical NaN payload if it is NaN. -/
theorem packRounded_isCanonicalized (mode : RoundingMode) (value : UnpackedFloat) :
    (⟨UInt32.ofBitVec (Rounding.packRounded Format.binary32 mode value)⟩ : F32).IsNonNaNOrCanonicalNaN :=
  packNormalized_isCanonicalized mode _

/-- Integral rounding produces only canonical NaNs. -/
theorem roundIntegral_isCanonicalized (mode : RoundingMode) (x : F32) :
    (roundIntegral mode x).IsNonNaNOrCanonicalNaN := by
  unfold roundIntegral
  generalize x.model.unpack = value
  cases value with
  | finite sign mantissa exponent hpos =>
    simp only [Rounding.integralRounded]
    split
    · exact packRounded_isCanonicalized mode _
    · exact Or.inr canonicalNaN_isCanonical
  | notANumber => exact packRounded_isCanonicalized mode _
  | infinity sign => exact packRounded_isCanonicalized mode _
  | zero sign => exact packRounded_isCanonicalized mode _

theorem roundIntegralRel_self (mode : RoundingMode) (x : F32) :
    roundIntegralRel mode x (roundIntegral mode x) :=
  unaryResult_self (roundIntegral mode) x (roundIntegral_isCanonicalized mode x)

theorem minimum_isCanonicalized (x y : F32) : (minimum x y).IsNonNaNOrCanonicalNaN := by
  unfold minimum
  split
  · exact Or.inr canonicalNaN_isCanonical
  next h =>
    have hx : ¬ x.IsNaN := by simp [isNaN] at h; exact h.1
    have hy : ¬ y.IsNaN := by simp [isNaN] at h; exact h.2
    split
    · split
      · exact Or.inl hx
      · exact Or.inl hy
    · split
      · exact Or.inl hx
      · exact Or.inl hy

theorem minimumRel_self (x y : F32) : minimumRel x y (minimum x y) :=
  binaryResult_self minimum x y (minimum_isCanonicalized x y)

theorem maximum_isCanonicalized (x y : F32) : (maximum x y).IsNonNaNOrCanonicalNaN := by
  unfold maximum
  split
  · exact Or.inr canonicalNaN_isCanonical
  next h =>
    have hx : ¬ x.IsNaN := by simp [isNaN] at h; exact h.1
    have hy : ¬ y.IsNaN := by simp [isNaN] at h; exact h.2
    split
    · split
      · exact Or.inl hy
      · exact Or.inl hx
    · split
      · exact Or.inl hy
      · exact Or.inl hx

theorem maximumRel_self (x y : F32) : maximumRel x y (maximum x y) :=
  binaryResult_self maximum x y (maximum_isCanonicalized x y)

end F32

namespace F64

/-- A model-derived NaN is exactly the positive canonical quiet encoding. -/
theorem ofModel_nan_eq (x : Float.Model) (h : (ofModel x).IsNaN) :
    ofModel x = canonicalNaN := by
  have fields := nan_fields h
  have hexp : unpackExponent (spec := Format.binary64) x.toBits.toBitVec = (-1#_) := by
    apply BitVec.eq_of_toNat_eq
    simpa [unpackExponent, decode64, decode, field, maxExponentField,
      binary64ExponentBits, binary64SignificandBits, Nat.shiftRight_eq_div_pow,
      ofModel] using fields.1
  have hmant : unpackMantissa (spec := Format.binary64) x.toBits.toBitVec ≠ 0#_ := by
    intro hm
    apply fields.2
    have hn := congrArg BitVec.toNat hm
    simpa [unpackMantissa, decode64, decode, field, binary64ExponentBits,
      binary64SignificandBits, Nat.shiftRight_eq_div_pow, ofModel] using hn
  have hbits := x.valid.eq_packedNaN hexp hmant
  have hu : x.toBits = Float.Model.nan.toBits := UInt64.eq_of_toBitVec_eq hbits
  change (⟨x.toBits⟩ : F64) = ⟨Float.Model.nan.toBits⟩
  rw [hu]

/-- Every model-derived result has no noncanonical NaN payload. -/
theorem ofModel_isCanonicalized (x : Float.Model) : (ofModel x).IsNonNaNOrCanonicalNaN := by
  by_cases h : (ofModel x).IsNaN
  · exact Or.inr (by rw [ofModel_nan_eq x h]; exact canonicalNaN_isCanonical)
  · exact Or.inl h

/-- A canonical NaN, of either sign, is also an arithmetic NaN. -/
theorem IsCanonicalNaN.isArithmeticNaN {x : F64} (h : x.IsCanonicalNaN) :
    x.IsArithmeticNaN := by
  rcases h with ⟨hnan, hbits⟩
  refine ⟨hnan, ?_⟩
  change x.bits.toNat % 2 ^ 52 ≥ 2 ^ 51
  have hb := congrArg UInt64.toNat hbits
  change x.bits.toNat &&& (2 ^ 63 - 1) = 9221120237041090560 at hb
  rw [Nat.and_two_pow_sub_one_eq_mod] at hb
  have hr := congrArg (fun n => n % 2 ^ 52) hb
  rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 52 ∣ 2 ^ 63)] at hr
  omega

/-- A deterministic binary result is permitted whenever its NaNs are canonical. -/
theorem binaryResult_self (eval : F64 → F64 → F64) (x y : F64)
    (h : (eval x y).IsNonNaNOrCanonicalNaN) : binaryResult eval x y (eval x y) := by
  unfold binaryResult
  split
  next hn =>
    have hc := h.resolve_left (not_not_intro hn)
    split
    · exact hc
    · exact hc.isArithmeticNaN
  next => rfl

/-- A deterministic unary result is permitted whenever its NaNs are canonical. -/
theorem unaryResult_self (eval : F64 → F64) (x : F64)
    (h : (eval x).IsNonNaNOrCanonicalNaN) : unaryResult eval x (eval x) := by
  unfold unaryResult
  split
  next hn =>
    have hc := h.resolve_left (not_not_intro hn)
    split
    · exact hc
    · exact hc.isArithmeticNaN
  next => rfl

/-- A deterministic FMA result is permitted by the analogous NaN policy. -/
theorem fmaNaNResult_self (eval : F64 → F64 → F64 → F64) (x y z : F64)
    (h : (eval x y z).IsNonNaNOrCanonicalNaN) : fmaNaNResult eval x y z (eval x y z) := by
  unfold fmaNaNResult
  split
  next hn =>
    have hc := h.resolve_left (not_not_intro hn)
    split
    · exact hc
    · exact hc.isArithmeticNaN
  next => rfl

theorem addRel_self (x y : F64) : addRel x y (add x y) :=
  binaryResult_self add x y (ofModel_isCanonicalized _)

theorem subRel_self (x y : F64) : subRel x y (sub x y) :=
  binaryResult_self sub x y (ofModel_isCanonicalized _)

theorem mulRel_self (x y : F64) : mulRel x y (mul x y) :=
  binaryResult_self mul x y (ofModel_isCanonicalized _)

theorem divRel_self (x y : F64) : divRel x y (div x y) :=
  binaryResult_self div x y (ofModel_isCanonicalized _)

theorem sqrtRel_self (x : F64) : sqrtRel x (sqrt x) :=
  unaryResult_self sqrt x (ofModel_isCanonicalized _)

theorem fmaNaNRel_self (x y z : F64) : fmaNaNRel x y z (fma x y z) :=
  fmaNaNResult_self fma x y z (ofModel_isCanonicalized _)


/-- Packing respects the canonical-NaN invariant even under directed overflow. -/
theorem packNormalized_isCanonicalized (mode : RoundingMode) (value : UnpackedFloat) :
    (⟨UInt64.ofBitVec (Rounding.packNormalized Format.binary64 mode value)⟩ : F64).IsNonNaNOrCanonicalNaN := by
  cases value with
  | finite sign mantissa exponent hpos =>
    simp only [Rounding.packNormalized]
    split
    · cases sign <;> exact Or.inl (by decide)
    · exact ofModel_isCanonicalized (Float.Model.pack (.finite sign mantissa exponent hpos))
  | notANumber => exact ofModel_isCanonicalized (Float.Model.pack .notANumber)
  | infinity sign => exact ofModel_isCanonicalized (Float.Model.pack (.infinity sign))
  | zero sign => exact ofModel_isCanonicalized (Float.Model.pack (.zero sign))

/-- Any directly rounded result has a canonical NaN payload if it is NaN. -/
theorem packRounded_isCanonicalized (mode : RoundingMode) (value : UnpackedFloat) :
    (⟨UInt64.ofBitVec (Rounding.packRounded Format.binary64 mode value)⟩ : F64).IsNonNaNOrCanonicalNaN :=
  packNormalized_isCanonicalized mode _

/-- Integral rounding produces only canonical NaNs. -/
theorem roundIntegral_isCanonicalized (mode : RoundingMode) (x : F64) :
    (roundIntegral mode x).IsNonNaNOrCanonicalNaN := by
  unfold roundIntegral
  generalize x.model.unpack = value
  cases value with
  | finite sign mantissa exponent hpos =>
    simp only [Rounding.integralRounded]
    split
    · exact packRounded_isCanonicalized mode _
    · exact Or.inr canonicalNaN_isCanonical
  | notANumber => exact packRounded_isCanonicalized mode _
  | infinity sign => exact packRounded_isCanonicalized mode _
  | zero sign => exact packRounded_isCanonicalized mode _

theorem roundIntegralRel_self (mode : RoundingMode) (x : F64) :
    roundIntegralRel mode x (roundIntegral mode x) :=
  unaryResult_self (roundIntegral mode) x (roundIntegral_isCanonicalized mode x)

theorem minimum_isCanonicalized (x y : F64) : (minimum x y).IsNonNaNOrCanonicalNaN := by
  unfold minimum
  split
  · exact Or.inr canonicalNaN_isCanonical
  next h =>
    have hx : ¬ x.IsNaN := by simp [isNaN] at h; exact h.1
    have hy : ¬ y.IsNaN := by simp [isNaN] at h; exact h.2
    split
    · split
      · exact Or.inl hx
      · exact Or.inl hy
    · split
      · exact Or.inl hx
      · exact Or.inl hy

theorem minimumRel_self (x y : F64) : minimumRel x y (minimum x y) :=
  binaryResult_self minimum x y (minimum_isCanonicalized x y)

theorem maximum_isCanonicalized (x y : F64) : (maximum x y).IsNonNaNOrCanonicalNaN := by
  unfold maximum
  split
  · exact Or.inr canonicalNaN_isCanonical
  next h =>
    have hx : ¬ x.IsNaN := by simp [isNaN] at h; exact h.1
    have hy : ¬ y.IsNaN := by simp [isNaN] at h; exact h.2
    split
    · split
      · exact Or.inl hy
      · exact Or.inl hx
    · split
      · exact Or.inl hy
      · exact Or.inl hx

theorem maximumRel_self (x y : F64) : maximumRel x y (maximum x y) :=
  binaryResult_self maximum x y (maximum_isCanonicalized x y)

end F64

namespace F32

/-- Numeric widening uses a canonical NaN whenever the result is NaN. -/
theorem toF64_isCanonicalized (x : F32) : x.toF64.IsNonNaNOrCanonicalNaN :=
  F64.packRounded_isCanonicalized .nearestTiesToEven _

theorem toF64_isCanonicalNaN (x : F32) (h : x.toF64.IsNaN) : x.toF64.IsCanonicalNaN :=
  x.toF64_isCanonicalized.resolve_left (not_not_intro h)

end F32

namespace F64

/-- Numeric narrowing uses a canonical NaN in every rounding direction. -/
theorem toF32_isCanonicalized (x : F64) (mode : RoundingMode := .nearestTiesToEven) :
    (x.toF32 mode).IsNonNaNOrCanonicalNaN :=
  F32.packRounded_isCanonicalized mode _

theorem toF32_isCanonicalNaN (x : F64) (mode : RoundingMode := .nearestTiesToEven)
    (h : (x.toF32 mode).IsNaN) : (x.toF32 mode).IsCanonicalNaN :=
  (x.toF32_isCanonicalized mode).resolve_left (not_not_intro h)

end F64

end Silmaril.Numeric.Ieee754
