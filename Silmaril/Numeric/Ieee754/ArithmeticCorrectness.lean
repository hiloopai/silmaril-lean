module

public import Silmaril.Numeric.Ieee754.FloatRounding
public import Silmaril.Numeric.Ieee754.RneBridge

/-!
# Rational certificates for binary32 and binary64 arithmetic

The result predicate is independent of the arithmetic implementation. It
asserts global nearest magnitude among all values at the destination precision
and minimum subnormal exponent, and preserves the sign of a nonzero exact
result. The upper exponent bound is an explicit premise on the rounded
intermediate; gradual underflow and exact cancellation are included.

The certificates connect the existing default operations to the exact rational
sum, product, or fused product-plus-sum, as required by IEEE 754-2019 §§4.3.1 and 5.4.1.
Nearest midpoint choices are additionally certified on the selected grid by
`roundUnpacked_finite_correct`; the optimality predicate below alone does not
distinguish ties-to-even from ties-to-away. Rational semantics identifies the
two zeros; `addExact_finite_cancel` and `fmaExact_finite_cancel` separately
establish the exact cancellation sign required by §6.3.

Reference: <https://standards.ieee.org/ieee/754/6210/>.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Conformance

open Float.Model Float.Model.UnpackedFloat

/-- Independent nearest-value specification, with the sign of the exact
rational result. Its magnitude candidate set has no maximum exponent, so this
predicate is stronger than nearest optimality among finite encodings alone.
Midpoint preference and the distinction between signed zeros are separate. -/
def RneOptimal (format : Format) (exact result : ℚ) : Prop :=
  BinaryOptimal format .nearestTiesToEven .positive |exact| |result| ∧
    (0 ≤ exact → 0 ≤ result) ∧ (exact ≤ 0 → result ≤ 0)

/-- The magnitude-and-sign specification implies global nearest optimality
among signed rational candidates as well. -/
theorem RneOptimal.nearest {format : Format} {q result : ℚ}
    (h : RneOptimal format q result) (candidate : ℚ)
    (hc : BinaryRepresentable format |candidate|) :
    |q - result| ≤ |q - candidate| := by
  have hd : |q - result| = abs (|q| - |result|) := by
    by_cases hq : 0 ≤ q
    · rw [abs_of_nonneg hq, abs_of_nonneg (h.2.1 hq)]
    · have hq : q ≤ 0 := le_of_lt (lt_of_not_ge hq)
      rw [abs_of_nonpos hq, abs_of_nonpos (h.2.2 hq)]
      rw [neg_sub_neg, abs_sub_comm]
  calc
    |q - result| = abs (|q| - |result|) := hd
    _ ≤ abs (|q| - |candidate|) := h.1.2 _ hc
    _ ≤ |q - candidate| := abs_abs_sub_abs_le_abs_sub q candidate

/-- Exact cancellation has rational result zero; the zero's bit sign is
intentionally handled by the separate IEEE §6.3 theorems. -/
theorem RneOptimal.exact_zero {format : Format} {result : ℚ}
    (h : RneOptimal format 0 result) : result = 0 :=
  le_antisymm (h.2.2 le_rfl) (h.2.1 le_rfl)

/-- Every destination precision represents the zero magnitude exactly. -/
theorem binaryRepresentable_zero (format : Format) : BinaryRepresentable format 0 := by
  refine ⟨0, format.minExponent, Nat.pow_pos (by decide), le_rfl, ?_⟩
  simp

/-- The independent magnitude candidate set contains only nonnegative values. -/
theorem BinaryRepresentable.nonneg {format : Format} {q : ℚ}
    (h : BinaryRepresentable format q) : 0 ≤ q := by
  obtain ⟨mantissa, exponent, _, _, rfl⟩ := h
  positivity

@[simp] theorem rneOptimal_zero (format : Format) : RneOptimal format 0 0 := by
  refine ⟨⟨?_, ?_⟩, by simp, by simp⟩
  · simpa using binaryRepresentable_zero format
  · intro candidate _
    simp

/-- Converting the nonnegative magnitude certificate back to its signed
rational value preserves nearest optimality and the sign of a nonzero input. -/
theorem rneOptimal_signed (format : Format) (sign : Sign) (q result : ℚ)
    (hq : 0 < q)
    (optimal : BinaryOptimal format .nearestTiesToEven sign q result) :
    RneOptimal format (signed (sign == .negative) q)
      (signed (sign == .negative) result) := by
  have hr := optimal.1.nonneg
  cases sign with
  | positive =>
    change RneOptimal format q result
    simp only [RneOptimal, abs_of_nonneg hq.le, abs_of_nonneg hr]
    exact ⟨optimal, by intros; linarith, by intros; linarith⟩
  | negative =>
    change RneOptimal format (-q) (-result)
    simp only [RneOptimal, abs_neg, abs_of_nonneg hq.le, abs_of_nonneg hr]
    exact ⟨optimal, by intros; linarith, by intros; linarith⟩

/-- RNE rounding is globally nearest for every input with a rational value,
including either exact zero and any finite dyadic representation. -/
theorem roundUnpacked_rne_optimal_of_value (format : Format) (value : UnpackedFloat)
    (q : ℚ) (hq : value? value = some q) :
    ∃ result : ℚ,
      value? (Rounding.roundUnpacked format .nearestTiesToEven value) = some result ∧
      RneOptimal format q result := by
  cases value with
  | notANumber | infinity _ => simp [value?] at hq
  | zero sign =>
    have hq : q = 0 := by simpa [value?] using hq.symm
    subst q
    exact ⟨0, rfl, rneOptimal_zero format⟩
  | finite sign mantissa exponent hm =>
    have hq : q = dyadic (sign.apply mantissa) exponent := by simpa [value?] using hq.symm
    subst q
    obtain ⟨result, optimal, hv⟩ :=
      roundUnpacked_finite_optimal format .nearestTiesToEven sign mantissa exponent hm
    refine ⟨signed (sign == .negative) result, hv, ?_⟩
    have hpositive : 0 < (mantissa : ℚ) * (2 : ℚ) ^ exponent := by positivity
    have hs := rneOptimal_signed format sign _ result hpositive optimal
    cases sign <;> simpa [dyadic, Sign.apply, signed] using hs

/-- The complete encoder/decoder path preserves nearest-value correctness when
the rounded exponent fits. This hypothesis admits both exact and inexact tiny
results, including results rounded to signed zero. -/
theorem packRounded_rne_optimal_of_value (format : Format) (value : UnpackedFloat)
    (q : ℚ) (hq : value? value = some q)
    (inRange : NoExponentOverflow format (Rounding.roundUnpacked format .nearestTiesToEven value)) :
    ∃ result : ℚ,
      value? (UnpackedFloat.unpack format (Rounding.packRounded format .nearestTiesToEven value)) =
        some result ∧ RneOptimal format q result := by
  rw [unpack_packRounded format .nearestTiesToEven value inRange]
  exact roundUnpacked_rne_optimal_of_value format value q hq

end Silmaril.Numeric.Ieee754.Conformance

namespace Silmaril.Numeric.Ieee754

open Float.Model Float.Model.UnpackedFloat Conformance

namespace F32

/-- Independent value of the raw binary32 decoder, without model normalization. -/
theorem value?_unpack_bits (x : F32) :
    value? (UnpackedFloat.unpack .binary32 x.bits.toBitVec) = x.toRat? := by
  rw [value?_unpack]
  rfl

/-- The final rounded FMA exponent fits in binary32. The unrounded product
may overflow the format or lie below its minimum subnormal magnitude. -/
def FmaNoOverflow (x y z : F32) : Prop :=
  NoExponentOverflow .binary32 (Rounding.roundUnpacked .binary32 .nearestTiesToEven
    (Rounding.addExact .nearestTiesToEven (Rounding.mulExact x.model.unpack y.model.unpack) z.model.unpack))

instance (x y z : F32) : Decidable (FmaNoOverflow x y z) := by
  unfold FmaNoOverflow
  infer_instance

/-- The existing binary32 FMA is nearest to the exact rational `a * b + c`,
with one rounding, provided its final rounded exponent fits. -/
theorem fma_optimal {x y z : F32} {a b c : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) (hz : z.toRat? = some c)
    (inRange : FmaNoOverflow x y z) :
    ∃ result : ℚ, (fma x y z).toRat? = some result ∧
      RneOptimal .binary32 (a * b + c) result := by
  have hx' : value? x.model.unpack = some a := (value?_model_unpack32 x).trans hx
  have hy' : value? y.model.unpack = some b := (value?_model_unpack32 y).trans hy
  have hz' : value? z.model.unpack = some c := (value?_model_unpack32 z).trans hz
  obtain ⟨result, hv, optimal⟩ := packRounded_rne_optimal_of_value .binary32 _ _
    (value?_fmaExact .nearestTiesToEven hx' hy' hz') inRange
  refine ⟨result, ?_, optimal⟩
  rw [← fmaWith_rne, ← value?_unpack_bits]
  exact hv

/-- The final rounded addition exponent fits in binary32. -/
def AddNoOverflow (x y : F32) : Prop :=
  NoExponentOverflow .binary32 (Rounding.roundUnpacked .binary32 .nearestTiesToEven
    (Rounding.addExact .nearestTiesToEven x.model.unpack y.model.unpack))

instance (x y : F32) : Decidable (AddNoOverflow x y) := by
  unfold AddNoOverflow
  infer_instance

/-- The existing binary32 addition is nearest to the exact rational `a + b`
when the final rounded exponent fits. -/
theorem add_optimal {x y : F32} {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (inRange : AddNoOverflow x y) :
    ∃ result : ℚ, (add x y).toRat? = some result ∧
      RneOptimal .binary32 (a + b) result := by
  have hx' : value? x.model.unpack = some a := (value?_model_unpack32 x).trans hx
  have hy' : value? y.model.unpack = some b := (value?_model_unpack32 y).trans hy
  obtain ⟨result, hv, optimal⟩ := packRounded_rne_optimal_of_value .binary32 _ _
    (value?_addExact .nearestTiesToEven hx' hy') inRange
  refine ⟨result, ?_, optimal⟩
  rw [← addWith_rne, ← value?_unpack_bits]
  exact hv

/-- The final rounded subtraction exponent fits in binary32. -/
def SubNoOverflow (x y : F32) : Prop :=
  NoExponentOverflow .binary32 (Rounding.roundUnpacked .binary32 .nearestTiesToEven
    (Rounding.addExact .nearestTiesToEven x.model.unpack y.model.unpack.neg))

instance (x y : F32) : Decidable (SubNoOverflow x y) := by
  unfold SubNoOverflow
  infer_instance

/-- The existing binary32 subtraction is nearest to the exact rational `a - b`
when the final rounded exponent fits. -/
theorem sub_optimal {x y : F32} {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (inRange : SubNoOverflow x y) :
    ∃ result : ℚ, (sub x y).toRat? = some result ∧
      RneOptimal .binary32 (a - b) result := by
  have hx' : value? x.model.unpack = some a := (value?_model_unpack32 x).trans hx
  have hy' : value? y.model.unpack = some b := (value?_model_unpack32 y).trans hy
  obtain ⟨result, hv, optimal⟩ := packRounded_rne_optimal_of_value .binary32 _ _
    (value?_subExact .nearestTiesToEven hx' hy') inRange
  refine ⟨result, ?_, optimal⟩
  rw [← subWith_rne, ← value?_unpack_bits]
  exact hv

/-- The final rounded multiplication exponent fits in binary32. -/
def MulNoOverflow (x y : F32) : Prop :=
  NoExponentOverflow .binary32 (Rounding.roundUnpacked .binary32 .nearestTiesToEven
    (Rounding.mulExact x.model.unpack y.model.unpack))

instance (x y : F32) : Decidable (MulNoOverflow x y) := by
  unfold MulNoOverflow
  infer_instance

/-- The existing binary32 multiplication is nearest to the exact rational `a * b`
when the final rounded exponent fits. -/
theorem mul_optimal {x y : F32} {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (inRange : MulNoOverflow x y) :
    ∃ result : ℚ, (mul x y).toRat? = some result ∧
      RneOptimal .binary32 (a * b) result := by
  have hx' : value? x.model.unpack = some a := (value?_model_unpack32 x).trans hx
  have hy' : value? y.model.unpack = some b := (value?_model_unpack32 y).trans hy
  obtain ⟨result, hv, optimal⟩ := packRounded_rne_optimal_of_value .binary32 _ _
    (value?_mulExact hx' hy') inRange
  refine ⟨result, ?_, optimal⟩
  rw [← mulWith_rne, ← value?_unpack_bits]
  exact hv

end F32

namespace F64

/-- Independent value of the raw binary64 decoder, without model normalization. -/
theorem value?_unpack_bits (x : F64) :
    value? (UnpackedFloat.unpack .binary64 x.bits.toBitVec) = x.toRat? := by
  rw [value?_unpack]
  rfl

/-- The final rounded FMA exponent fits in binary64. The unrounded product
may overflow the format or lie below its minimum subnormal magnitude. -/
def FmaNoOverflow (x y z : F64) : Prop :=
  NoExponentOverflow .binary64 (Rounding.roundUnpacked .binary64 .nearestTiesToEven
    (Rounding.addExact .nearestTiesToEven (Rounding.mulExact x.model.unpack y.model.unpack) z.model.unpack))

instance (x y z : F64) : Decidable (FmaNoOverflow x y z) := by
  unfold FmaNoOverflow
  infer_instance

/-- The existing binary64 FMA is nearest to the exact rational `a * b + c`,
with one rounding, provided its final rounded exponent fits. -/
theorem fma_optimal {x y z : F64} {a b c : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b) (hz : z.toRat? = some c)
    (inRange : FmaNoOverflow x y z) :
    ∃ result : ℚ, (fma x y z).toRat? = some result ∧
      RneOptimal .binary64 (a * b + c) result := by
  have hx' : value? x.model.unpack = some a := (value?_model_unpack64 x).trans hx
  have hy' : value? y.model.unpack = some b := (value?_model_unpack64 y).trans hy
  have hz' : value? z.model.unpack = some c := (value?_model_unpack64 z).trans hz
  obtain ⟨result, hv, optimal⟩ := packRounded_rne_optimal_of_value .binary64 _ _
    (value?_fmaExact .nearestTiesToEven hx' hy' hz') inRange
  refine ⟨result, ?_, optimal⟩
  rw [← fmaWith_rne, ← value?_unpack_bits]
  exact hv

/-- The final rounded addition exponent fits in binary64. -/
def AddNoOverflow (x y : F64) : Prop :=
  NoExponentOverflow .binary64 (Rounding.roundUnpacked .binary64 .nearestTiesToEven
    (Rounding.addExact .nearestTiesToEven x.model.unpack y.model.unpack))

instance (x y : F64) : Decidable (AddNoOverflow x y) := by
  unfold AddNoOverflow
  infer_instance

/-- The existing binary64 addition is nearest to the exact rational `a + b`
when the final rounded exponent fits. -/
theorem add_optimal {x y : F64} {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (inRange : AddNoOverflow x y) :
    ∃ result : ℚ, (add x y).toRat? = some result ∧
      RneOptimal .binary64 (a + b) result := by
  have hx' : value? x.model.unpack = some a := (value?_model_unpack64 x).trans hx
  have hy' : value? y.model.unpack = some b := (value?_model_unpack64 y).trans hy
  obtain ⟨result, hv, optimal⟩ := packRounded_rne_optimal_of_value .binary64 _ _
    (value?_addExact .nearestTiesToEven hx' hy') inRange
  refine ⟨result, ?_, optimal⟩
  rw [← addWith_rne, ← value?_unpack_bits]
  exact hv

/-- The final rounded subtraction exponent fits in binary64. -/
def SubNoOverflow (x y : F64) : Prop :=
  NoExponentOverflow .binary64 (Rounding.roundUnpacked .binary64 .nearestTiesToEven
    (Rounding.addExact .nearestTiesToEven x.model.unpack y.model.unpack.neg))

instance (x y : F64) : Decidable (SubNoOverflow x y) := by
  unfold SubNoOverflow
  infer_instance

/-- The existing binary64 subtraction is nearest to the exact rational `a - b`
when the final rounded exponent fits. -/
theorem sub_optimal {x y : F64} {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (inRange : SubNoOverflow x y) :
    ∃ result : ℚ, (sub x y).toRat? = some result ∧
      RneOptimal .binary64 (a - b) result := by
  have hx' : value? x.model.unpack = some a := (value?_model_unpack64 x).trans hx
  have hy' : value? y.model.unpack = some b := (value?_model_unpack64 y).trans hy
  obtain ⟨result, hv, optimal⟩ := packRounded_rne_optimal_of_value .binary64 _ _
    (value?_subExact .nearestTiesToEven hx' hy') inRange
  refine ⟨result, ?_, optimal⟩
  rw [← subWith_rne, ← value?_unpack_bits]
  exact hv

/-- The final rounded multiplication exponent fits in binary64. -/
def MulNoOverflow (x y : F64) : Prop :=
  NoExponentOverflow .binary64 (Rounding.roundUnpacked .binary64 .nearestTiesToEven
    (Rounding.mulExact x.model.unpack y.model.unpack))

instance (x y : F64) : Decidable (MulNoOverflow x y) := by
  unfold MulNoOverflow
  infer_instance

/-- The existing binary64 multiplication is nearest to the exact rational `a * b`
when the final rounded exponent fits. -/
theorem mul_optimal {x y : F64} {a b : ℚ}
    (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (inRange : MulNoOverflow x y) :
    ∃ result : ℚ, (mul x y).toRat? = some result ∧
      RneOptimal .binary64 (a * b) result := by
  have hx' : value? x.model.unpack = some a := (value?_model_unpack64 x).trans hx
  have hy' : value? y.model.unpack = some b := (value?_model_unpack64 y).trans hy
  obtain ⟨result, hv, optimal⟩ := packRounded_rne_optimal_of_value .binary64 _ _
    (value?_mulExact hx' hy') inRange
  refine ⟨result, ?_, optimal⟩
  rw [← mulWith_rne, ← value?_unpack_bits]
  exact hv

end F64

end Silmaril.Numeric.Ieee754
