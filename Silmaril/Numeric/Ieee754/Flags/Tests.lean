module

import Silmaril.Numeric.Ieee754.Flags.Binary

/-!
# Exception-flag regression vectors

Kernel-checked examples on raw binary32 and binary64 encodings. They exercise
each exception, both tininess conventions, the FMA quiet-NaN policy, the
`Exact` and non-`Exact` forms of integral rounding and integer conversion, the
flushing hooks, and sticky accumulation. They are regressions, not substitutes
for the general theorems.
-/

namespace Silmaril.Numeric.Ieee754.FlagTests

open Silmaril.Numeric Float.Model FlagSpec

set_option maxRecDepth 20000

private def rne : RoundingMode := .nearestTiesToEven
private def after : Tininess := .afterRounding
private def before : Tininess := .beforeRounding

/-! ## Inexact, overflow and underflow -/

-- 0.1f + 0.2f is inexact.
example : F32.addFlags rne after ⟨0x3dcccccd⟩ ⟨0x3e4ccccd⟩ = { inexact := true } := by decide +kernel
-- 1 + 1 is exact.
example : F32.addFlags rne after ⟨0x3f800000⟩ ⟨0x3f800000⟩ = {} := by decide +kernel
-- 1 + 2^-24 is a midpoint: inexact in every direction.
example : [RoundingMode.nearestTiesToEven, .towardZero, .towardPositive, .towardNegative,
    .nearestTiesToAway].map (fun mode => F32.addFlags mode after ⟨0x3f800000⟩ ⟨0x33800000⟩) =
    List.replicate 5 { inexact := true } := by decide +kernel

-- The largest finite binary32 times two overflows in every direction, even when
-- the delivered result is the largest finite number.
example : [RoundingMode.nearestTiesToEven, .towardZero, .towardPositive, .towardNegative,
    .nearestTiesToAway].map (fun mode => F32.mulFlags mode after ⟨0x7f7fffff⟩ ⟨0x40000000⟩) =
    List.replicate 5 { overflow := true, inexact := true } := by decide +kernel
-- Adding half an ulp at the top: overflow only for round-to-nearest and upward.
example : [RoundingMode.nearestTiesToEven, .towardZero, .towardPositive, .towardNegative,
    .nearestTiesToAway].map (fun mode => F32.addFlags mode after ⟨0x7f7fffff⟩ ⟨0x73000000⟩) =
    [{ overflow := true, inexact := true }, { inexact := true },
      { overflow := true, inexact := true }, { inexact := true },
      { overflow := true, inexact := true }] := by decide +kernel
-- binary64 to binary32 narrowing overflow.
example : F64.toF32Flags rne after ⟨0x7e37e43c8800759c⟩ = { overflow := true, inexact := true } := by
  decide +kernel

-- The smallest normal divided by two is an exact subnormal: no underflow.
example : F32.divFlags rne after ⟨0x00800000⟩ ⟨0x40000000⟩ = {} := by decide +kernel
-- The smallest subnormal divided by two is tiny and inexact.
example : F32.divFlags rne after ⟨0x00000001⟩ ⟨0x40000000⟩ =
    { underflow := true, inexact := true } := by decide +kernel
example : F64.mulFlags rne after ⟨0x0000000000000001⟩ ⟨0x3fe0000000000000⟩ =
    { underflow := true, inexact := true } := by decide +kernel

-- `2^-126 - 2^-151` rounds to `2^-126` with unbounded exponent: tiny before
-- rounding but not after, and inexact in both cases.
example : F64.toF32Flags rne after ⟨0x380FFFFFF0000000⟩ = { inexact := true } := by decide +kernel
example : F64.toF32Flags rne before ⟨0x380FFFFFF0000000⟩ =
    { underflow := true, inexact := true } := by decide +kernel
-- Toward zero it stays below `2^-126`, so both conventions report underflow.
example : F64.toF32Flags .towardZero after ⟨0x380FFFFFF0000000⟩ =
    { underflow := true, inexact := true } := by decide +kernel

/-! ## Invalid operation and division by zero -/

-- A signaling NaN raises invalid; a quiet NaN raises nothing.
example : F32.addFlags rne after ⟨0x7f800001⟩ ⟨0x3f800000⟩ = invalid := by decide +kernel
example : F32.addFlags rne after ⟨0x7fc00000⟩ ⟨0x3f800000⟩ = {} := by decide +kernel
example : F64.sqrtFlags rne after ⟨0x7ff0000000000001⟩ = invalid := by decide +kernel
example : F64.sqrtFlags rne after ⟨0x7ff8000000000000⟩ = {} := by decide +kernel
example : F32.toF64Flags rne after ⟨0xff800001⟩ = invalid := by decide +kernel
-- ∞ - ∞ is invalid, ∞ + ∞ is exact.
example : F32.subFlags rne after ⟨0x7f800000⟩ ⟨0x7f800000⟩ = invalid := by decide +kernel
example : F32.addFlags rne after ⟨0x7f800000⟩ ⟨0x7f800000⟩ = {} := by decide +kernel
-- 0 × ∞ is invalid.
example : F64.mulFlags rne after ⟨0x8000000000000000⟩ ⟨0x7ff0000000000000⟩ = invalid := by
  decide +kernel
-- 1 / 0 divides by zero, 0 / 0 and ∞ / ∞ are invalid, ∞ / 0 is exact.
example : F32.divFlags rne after ⟨0x3f800000⟩ ⟨0x80000000⟩ = divideByZero := by decide +kernel
example : F32.divFlags rne after ⟨0x00000000⟩ ⟨0x80000000⟩ = invalid := by decide +kernel
example : F32.divFlags rne after ⟨0x7f800000⟩ ⟨0xff800000⟩ = invalid := by decide +kernel
example : F32.divFlags rne after ⟨0x7f800000⟩ ⟨0x00000000⟩ = {} := by decide +kernel
-- Square roots: of -1 invalid, of -0 exact, of 2 inexact, of 4 exact.
example : F32.sqrtFlags rne after ⟨0xbf800000⟩ = invalid := by decide +kernel
example : F32.sqrtFlags rne after ⟨0x80000000⟩ = {} := by decide +kernel
example : F32.sqrtFlags rne after ⟨0x40000000⟩ = { inexact := true } := by decide +kernel
example : F32.sqrtFlags rne after ⟨0x40800000⟩ = {} := by decide +kernel
example : F64.sqrtFlags rne after ⟨0x4000000000000000⟩ = { inexact := true } := by decide +kernel
-- The square root of the smallest binary32 subnormal, `2^-149`, is irrational.
example : F32.sqrtFlags rne after ⟨0x00000001⟩ = { inexact := true } := by decide +kernel
-- The square root of `2^-148` is `2^-74`, exactly.
example : F32.sqrtFlags rne after ⟨0x00000002⟩ = {} := by decide +kernel

/-! ## Fused multiply-add -/

-- fma(0, ∞, qNaN): the §7.2(c) choice is visible.
example : F32.fmaFlags .signalInvalid rne after ⟨0⟩ ⟨0x7f800000⟩ ⟨0x7fc00000⟩ = invalid := by
  decide +kernel
example : F32.fmaFlags .noSignal rne after ⟨0⟩ ⟨0x7f800000⟩ ⟨0x7fc00000⟩ = {} := by decide +kernel
-- fma(0, ∞, 1) is invalid under both policies.
example : F32.fmaFlags .noSignal rne after ⟨0⟩ ⟨0x7f800000⟩ ⟨0x3f800000⟩ = invalid := by
  decide +kernel
-- fma(∞, 1, -∞) is invalid; fma(∞, -1, -∞) is exact.
example : F32.fmaFlags .noSignal rne after ⟨0x7f800000⟩ ⟨0x3f800000⟩ ⟨0xff800000⟩ = invalid := by
  decide +kernel
example : F32.fmaFlags .noSignal rne after ⟨0x7f800000⟩ ⟨0xbf800000⟩ ⟨0xff800000⟩ = {} := by
  decide +kernel
-- One rounding: (1 + 2^-12)^2 - 1 = 2^-11 + 2^-24 is exact in binary32.
example : F32.fmaFlags .noSignal rne after ⟨0x3f800800⟩ ⟨0x3f800800⟩ ⟨0xbf800000⟩ = {} := by
  decide +kernel
-- A product below the subnormal range does not underflow the intermediate:
-- 2^-149 · 2^-1 + 1 is only inexact.
example : F32.fmaFlags .noSignal rne after ⟨0x00000001⟩ ⟨0x3f000000⟩ ⟨0x3f800000⟩ =
    { inexact := true } := by decide +kernel

/-! ## Integer conversions and integral rounding -/

-- 2.5 to i32: the `Exact` form is inexact, the other form raises nothing.
example : F32.toIntFlags IntFormat.i32 rne true ⟨0x40200000⟩ = inexactOnly := by decide +kernel
example : F32.toIntFlags IntFormat.i32 rne false ⟨0x40200000⟩ = {} := by decide +kernel
-- 2^31 is out of range for i32 and in range for u32.
example : F32.toIntFlags IntFormat.i32 .towardZero true ⟨0x4f000000⟩ = invalid := by decide +kernel
example : F32.toIntFlags IntFormat.u32 .towardZero true ⟨0x4f000000⟩ = {} := by decide +kernel
-- -0.5 toward zero is 0, which is in range for u32; -1 is not.
example : F32.toIntFlags IntFormat.u32 .towardZero true ⟨0xbf000000⟩ = inexactOnly := by
  decide +kernel
example : F32.toIntFlags IntFormat.u32 .towardZero true ⟨0xbf800000⟩ = invalid := by decide +kernel
-- Every NaN, including a quiet NaN, is invalid.
example : F64.toIntFlags IntFormat.i64 rne false ⟨0x7ff8000000000000⟩ = invalid := by
  decide +kernel
-- The largest i64 rounds to 2^63 in binary64.
example : F64.ofIntFlags rne after (2 ^ 63 - 1) = { inexact := true } := by decide +kernel
example : F32.ofIntFlags rne after (2 ^ 24 + 1) = { inexact := true } := by decide +kernel
example : F32.ofIntFlags rne after (2 ^ 24) = {} := by decide +kernel
-- roundToIntegralExact signals inexact; other integral roundings do not.
example : F32.roundToIntegralFlags rne true ⟨0x40200000⟩ = inexactOnly := by decide +kernel
example : F32.roundToIntegralFlags rne false ⟨0x40200000⟩ = {} := by decide +kernel
example : F32.roundToIntegralFlags rne true ⟨0x7f800001⟩ = invalid := by decide +kernel

/-! ## Other formats -/

private def binary16 : Format := ⟨10, by decide, 5, by decide⟩
private def bfloat16 : Format := ⟨7, by decide, 8, by decide⟩

-- binary16: 65504 is the largest finite value; adding half an ulp (16) overflows
-- under round-to-nearest and not toward zero.
example : FlagSpec.add binary16 rne after (Datum.decode binary16 0x7bff)
    (Datum.decode binary16 0x4c00) = { overflow := true, inexact := true } := by decide +kernel
example : FlagSpec.add binary16 .towardZero after (Datum.decode binary16 0x7bff)
    (Datum.decode binary16 0x4c00) = { inexact := true } := by decide +kernel
-- binary16 and bfloat16 signaling NaNs.
example : Datum.decode binary16 0x7c01 = .nan true := by decide +kernel
example : Datum.decode binary16 0x7e00 = .nan false := by decide +kernel
example : Datum.decode bfloat16 0x7f81 = .nan true := by decide +kernel
-- binary32 to bfloat16 narrowing of 1 + 2^-8 is a midpoint, hence inexact.
example : FlagSpec.convert bfloat16 rne after (F32.ofBits 0x3f808000).datum =
    { inexact := true } := by decide +kernel

/-! ## Denormal hooks -/

-- With denormals-are-zero, 1 / 2^-149 divides by zero.
example : FlagSpec.div Format.binary32 rne after (F32.ofBits 0x3f800000).datum
    (flushInput Format.binary32 (F32.ofBits 0x00000001).datum) = divideByZero := by decide +kernel
-- Flush-to-zero turns the exact subnormal 2^-127 into underflow and inexact,
-- and only when underflow is masked.
example : roundingFlagsFlushed .maskedUnderflowInexact true Format.binary32 rne after
    ((2 : ℚ) ^ (-127 : ℤ)) = { underflow := true, inexact := true } := by decide +kernel
example : roundingFlagsFlushed .maskedUnderflowInexact false Format.binary32 rne after
    ((2 : ℚ) ^ (-127 : ℤ)) = {} := by decide +kernel

/-! ## Sticky accumulation -/

example :
    let env : Environment := { rounding := .towardZero }
    let env := env.signal (fun mode tininess =>
      F32.addFlags mode tininess ⟨0x3dcccccd⟩ ⟨0x3e4ccccd⟩)
    let env := env.signal (fun mode tininess =>
      F32.mulFlags mode tininess ⟨0x7f7fffff⟩ ⟨0x40000000⟩)
    let env := env.signal (fun mode tininess =>
      F32.addFlags mode tininess ⟨0x3f800000⟩ ⟨0x3f800000⟩)
    env.flags = { overflow := true, inexact := true } := by decide +kernel

end Silmaril.Numeric.Ieee754.FlagTests
