module

import Silmaril.Numeric.Ieee754.Rounding

/-!
Kernel-checked regression vectors for IEEE rounding boundaries. These cases
distinguish single-rounding FMA from separate multiplication and addition,
exercise directed overflow and gradual underflow, and check integer rounding.
-/

namespace Silmaril.Numeric.Ieee754.Tests

open Float.Model Float.Model.UnpackedFloat

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private def modes : List RoundingMode :=
  [.nearestTiesToEven, .towardZero, .towardPositive, .towardNegative, .nearestTiesToAway]

-- 1 + half an ulp: nearest-even keeps the even significand, ties-away increments.
example : modes.map (fun mode =>
    (F32.addWith mode ⟨0x3f800000⟩ ⟨0x33800000⟩).bits) =
    [0x3f800000, 0x3f800000, 0x3f800001, 0x3f800000, 0x3f800001] := by decide

example : modes.map (fun mode =>
    (F32.addWith mode ⟨0xbf800000⟩ ⟨0xb3800000⟩).bits) =
    [0xbf800000, 0xbf800000, 0xbf800000, 0xbf800001, 0xbf800001] := by decide

-- Exact cancellation is -0 only under round-toward-negative.
example : modes.map (fun mode => (F32.addWith mode ⟨0x3f800000⟩ ⟨0xbf800000⟩).bits) =
    [0, 0, 0, 0x80000000, 0] := by decide

example : (F32.addWith .towardNegative ⟨0⟩ ⟨0x80000000⟩).bits = 0x80000000 := by decide
example : (F32.addWith .towardPositive ⟨0x80000000⟩ ⟨0x80000000⟩).bits = 0x80000000 := by decide

-- Finite overflow depends on rounding direction and sign.
example : modes.map (fun mode => (F32.mulWith mode ⟨0x7f7fffff⟩ ⟨0x40000000⟩).bits) =
    [0x7f800000, 0x7f7fffff, 0x7f800000, 0x7f7fffff, 0x7f800000] := by decide

example : modes.map (fun mode => (F32.mulWith mode ⟨0xff7fffff⟩ ⟨0x40000000⟩).bits) =
    [0xff800000, 0xff7fffff, 0xff7fffff, 0xff800000, 0xff800000] := by decide

-- Actual infinity is not changed to max-finite by directed rounding.
example : (F32.mulWith .towardZero ⟨0x7f800000⟩ ⟨0x40000000⟩).bits = 0x7f800000 := by decide

-- Half of the least subnormal, including the sign of rounded zero.
example : modes.map (fun mode => (F32.divWith mode ⟨1⟩ ⟨0x40000000⟩).bits) =
    [0, 0, 1, 0, 1] := by decide

example : modes.map (fun mode => (F32.divWith mode ⟨0x80000001⟩ ⟨0x40000000⟩).bits) =
    [0x80000000, 0x80000000, 0x80000000, 0x80000001, 0x80000001] := by decide

-- FMA retains the low product bits that separate multiplication would discard.
example : (F32.fmaWith .nearestTiesToEven
    ⟨0x3f800001⟩ ⟨0x3f7ffffe⟩ ⟨0xbf800000⟩).bits = 0xa8800000 := by decide

example : (F32.addWith .nearestTiesToEven
    (F32.mulWith .nearestTiesToEven ⟨0x3f800001⟩ ⟨0x3f7ffffe⟩) ⟨0xbf800000⟩).bits = 0 := by decide

-- The product overflows if rounded separately, but the fused result is finite.
example : (F32.fmaWith .nearestTiesToEven
    ⟨0x7f7fffff⟩ ⟨0x40000000⟩ ⟨0xff7fffff⟩).bits = 0x7f7fffff := by decide

-- The exact product is half a subnormal, making the fused sum a midpoint.
example : (F32.fmaWith .nearestTiesToEven ⟨1⟩ ⟨0x3f000000⟩ ⟨1⟩).bits = 2 := by decide

example : (F32.fmaWith .towardNegative
    ⟨0x3f800000⟩ ⟨0x3f800000⟩ ⟨0xbf800000⟩).bits = 0x80000000 := by decide

-- Invalid multiplication remains invalid in FMA, including with an infinite addend.
example : (F32.fmaWith .nearestTiesToEven ⟨0⟩ ⟨0x7f800000⟩ ⟨0x7f800000⟩).bits =
    0x7fc00000 := by decide

example : (F64.fmaWith .nearestTiesToEven
    ⟨0x3ff0000000000001⟩ ⟨0x3feffffffffffffe⟩ ⟨0xbff0000000000000⟩).bits =
    0xb970000000000000 := by decide

example : (F64.fmaWith .nearestTiesToEven
    ⟨0x7fefffffffffffff⟩ ⟨0x4000000000000000⟩ ⟨0xffefffffffffffff⟩).bits =
    0x7fefffffffffffff := by decide

example : (F64.fmaWith .nearestTiesToEven ⟨1⟩ ⟨0x3fe0000000000000⟩ ⟨1⟩).bits = 2 := by decide

-- Irrational square roots and non-dyadic quotients retain an exact residual class.
example : modes.map (fun mode => (F32.sqrtWith mode ⟨0x40000000⟩).bits) =
    [0x3fb504f3, 0x3fb504f3, 0x3fb504f4, 0x3fb504f3, 0x3fb504f3] := by decide +kernel

example : modes.map (fun mode => (F32.divWith mode ⟨0x3f800000⟩ ⟨0x40400000⟩).bits) =
    [0x3eaaaaab, 0x3eaaaaaa, 0x3eaaaaab, 0x3eaaaaaa, 0x3eaaaaab] := by decide

-- Integer ties, signed zero, and exact integer inputs.
example : modes.map (fun mode => (F32.ofBits 0x40200000).toInt? mode) =
    [some 2, some 2, some 3, some 2, some 3] := by decide

example : modes.map (fun mode => (F32.ofBits 0xc0200000).toInt? mode) =
    [some (-2), some (-2), some (-2), some (-3), some (-3)] := by decide

example : (F32.ofBits 0x7fc00000).toInt? = none := by decide
example : (F32.ofBits 0x7f800000).toInt? = none := by decide
example : (F32.roundIntegral .towardZero ⟨0xbf000000⟩).bits = 0x80000000 := by decide
example : (F32.ofInt 16777217 .nearestTiesToEven).bits = 0x4b800000 := by decide
example : (F32.ofInt 16777217 .nearestTiesToAway).bits = 0x4b800001 := by decide
example : (F64.ofInt 9007199254740993 .nearestTiesToEven).bits = 0x4340000000000000 := by decide
example : (F64.ofInt 9007199254740993 .towardPositive).bits = 0x4340000000000001 := by decide

-- Direct narrowing: this binary64 value lies immediately above a binary32 midpoint.
example : (F64.toF32 ⟨0x3ff0000010000001⟩).bits = 0x3f800001 := by decide
example : (F64.toF32 ⟨0x3ff0000010000000⟩).bits = 0x3f800000 := by decide

end Silmaril.Numeric.Ieee754.Tests
