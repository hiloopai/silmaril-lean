module

public import Silmaril.Numeric.Ieee754.Operations

/-!
# Kernel-checked scalar arithmetic regressions

These concrete bit-pattern facts cover IEEE 754-2019 §5.4.1 single-rounding
FMA, including cancellation across product overflow and subnormal boundaries.
They also guard IEEE §6.3 zero signs, ties-to-even integral rounding, remainder
quotient selection, minimum/maximum NaN policy, and refinement rejection.
They are regression proofs, not a general proof of IEEE compliance.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Tests

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

/-- `(1 + 2⁻²³) * (1 - 2⁻²³) - 1 = -2⁻⁴⁶` with one rounding. -/
theorem f32_fma_retains_product_error :
    F32.fma ⟨0x3f800001⟩ ⟨0x3f7ffffe⟩ ⟨0xbf800000⟩ = ⟨0xa8800000⟩ := by decide

/-- Separately rounded multiplication loses that product error. -/
theorem f32_mul_add_loses_product_error :
    F32.add (F32.mul ⟨0x3f800001⟩ ⟨0x3f7ffffe⟩) ⟨0xbf800000⟩ = F32.zero := by decide

/-- `(1 + 2⁻⁵²) * (1 - 2⁻⁵²) - 1 = -2⁻¹⁰⁴` in binary64. -/
theorem f64_fma_retains_product_error :
    F64.fma ⟨0x3ff0000000000001⟩ ⟨0x3feffffffffffffe⟩ ⟨0xbff0000000000000⟩ =
      ⟨0xb970000000000000⟩ := by decide

theorem f64_mul_add_loses_product_error :
    F64.add (F64.mul ⟨0x3ff0000000000001⟩ ⟨0x3feffffffffffffe⟩) ⟨0xbff0000000000000⟩ =
      F64.zero := by decide

/-- The exact product may exceed the finite range while the fused result does not. -/
theorem f32_fma_cancels_product_overflow :
    F32.fma F32.maxFinite ⟨0x40000000⟩ (-F32.maxFinite) = F32.maxFinite := by decide

theorem f64_fma_cancels_product_overflow :
    F64.fma F64.maxFinite ⟨0x4000000000000000⟩ (-F64.maxFinite) = F64.maxFinite := by decide

/-- Half of the least subnormal contributes before the only rounding. -/
theorem f32_fma_subnormal_tie_even :
    F32.fma F32.minSubnormal ⟨0x3f000000⟩ F32.minSubnormal = ⟨2⟩ := by decide

theorem f64_fma_subnormal_tie_even :
    F64.fma F64.minSubnormal ⟨0x3fe0000000000000⟩ F64.minSubnormal = ⟨2⟩ := by decide

theorem f32_fma_negative_zero :
    F32.fma F32.negativeZero F32.one F32.negativeZero = F32.negativeZero := by decide

theorem f64_fma_negative_zero :
    F64.fma F64.negativeZero F64.one F64.negativeZero = F64.negativeZero := by decide

theorem f32_fma_cancellation_positive_zero :
    F32.fma F32.one F32.one (-F32.one) = F32.zero := by decide

theorem f32_fma_zero_times_infinity :
    F32.fma F32.zero F32.infinity F32.one = F32.canonicalNaN := by decide

theorem f64_fma_opposite_infinities :
    F64.fma F64.infinity F64.one (-F64.infinity) = F64.canonicalNaN := by decide

theorem bit_equality_distinguishes_zero_signs :
    (F32.zero == F32.negativeZero) = false := by decide

theorem numeric_equality_identifies_zero_signs :
    F32.equal F32.zero F32.negativeZero = true := by decide

theorem nan_is_unordered :
    F64.compare F64.canonicalNaN F64.one = none := by decide

theorem minimum_negative_zero :
    F32.minimum F32.zero F32.negativeZero = F32.negativeZero := by decide

theorem maximum_positive_zero :
    F64.maximum F64.negativeZero F64.zero = F64.zero := by decide

theorem minimum_propagates_nan :
    F32.minimum F32.one ⟨0x7f800001⟩ = F32.canonicalNaN := by decide

theorem minimumNumber_ignores_nan :
    F32.minimumNumber F32.one ⟨0x7f800001⟩ = F32.one := by decide

theorem nearest_tie_even_down :
    F32.nearest ⟨0x40200000⟩ = ⟨0x40000000⟩ := by decide

theorem nearest_tie_even_up :
    F32.nearest ⟨0x40600000⟩ = ⟨0x40800000⟩ := by decide

theorem trunc_preserves_negative_zero :
    F32.trunc ⟨0xbe800000⟩ = F32.negativeZero := by decide

theorem ceil_negative_fraction :
    F64.ceil ⟨0xbfe0000000000000⟩ = F64.negativeZero := by decide

theorem floor_negative_fraction :
    F64.floor ⟨0xbfe0000000000000⟩ = -F64.one := by decide

/-- IEEE remainder uses the nearest even integer quotient: `7 - 4 * 2 = -1`. -/
theorem remainder_nearest_quotient :
    F32.remainder ⟨0x40e00000⟩ ⟨0x40000000⟩ = -F32.one := by decide

/-- fmod truncates the quotient instead: `7 - 3 * 2 = 1`. -/
theorem fmod_truncating_quotient :
    F32.fmod ⟨0x40e00000⟩ ⟨0x40000000⟩ = F32.one := by decide

theorem fmod_negative_exact_zero :
    F64.fmod ⟨0xc010000000000000⟩ ⟨0x4000000000000000⟩ = F64.negativeZero := by decide

theorem scaleB_gradual_underflow :
    F32.scaleB F32.minNormal (-1) = ⟨0x00400000⟩ := by decide

theorem nextUp_negative_zero :
    F32.nextUp F32.negativeZero = F32.minSubnormal := by decide

theorem nextDown_infinity :
    F64.nextDown F64.infinity = F64.maxFinite := by decide

theorem finite_constructor_rejects_infinity :
    (F32.Finite.ofRaw? F32.infinity).isNone = true := by decide

theorem nonNaN_constructor_rejects_nan :
    (F64.NonNaN.ofRaw? F64.canonicalNaN).isNone = true := by decide

theorem canonical_inputs_decidable :
    decide (F32.canonicalNaNInputs ⟨0xffc00000⟩ F32.one) = true := by decide

theorem add_relation_allows_negative_canonical_nan :
    F32.addRel F32.infinity (-F32.infinity) ⟨0xffc00000⟩ := by decide

theorem add_relation_rejects_payload_without_nan_input :
    ¬F32.addRel F32.infinity (-F32.infinity) ⟨0x7fc00001⟩ := by decide

theorem totalOrder_orders_zero_signs :
    F32.totalOrder F32.negativeZero F32.zero = true ∧
    F32.totalOrder F32.zero F32.negativeZero = false := by decide

theorem totalOrder_orders_nan_payloads :
    F64.totalOrder ⟨0x7ff8000000000001⟩ ⟨0x7ff8000000000002⟩ = true ∧
    F64.totalOrder ⟨0xfff8000000000001⟩ ⟨0xfff8000000000002⟩ = false := by decide

theorem canonicalized_neg_preserves_nan_sign :
    (-(F32.canonicalize F32.canonicalNaN)).val = ⟨0xffc00000⟩ := by decide

theorem nextDown_canonicalizes_nan :
    F32.nextDown ⟨0xff800001⟩ = F32.canonicalNaN := by decide

end Silmaril.Numeric.Ieee754.Tests
