module

public import Silmaril.Numeric.Float.Spec

/-!
# Concrete profile vectors

Kernel-checked examples (`decide +kernel`) for each profile. Expected values and
flags are taken from the cited manual rules (`Silmaril.Numeric.Float.Instances`)
and IEEE 754-2019 §7, not from executing hardware. The exception-flag vectors at
the end include a binary64 product on which before-rounding and after-rounding
tininess disagree, so the x86 and AArch64 profiles report different flags, and
with flushing enabled different results.
-/

@[expose] public section

namespace Silmaril.Numeric.Float.Tests

open Float.Model Silmaril.Numeric Silmaril.Numeric.Ieee754

private abbrev x86 : Profile := Profile.x86SSE
private abbrev rv : Profile := Profile.riscvFD
private abbrev arm : Profile := Profile.aarch64
private abbrev armDN : Profile := Profile.aarch64 { defaultNaN := true }

private abbrev one32 : BitVec 32 := 0x3f800000#32
private abbrev qnan32 : BitVec 32 := 0x7fc00000#32
private abbrev snan32 : BitVec 32 := 0x7f800001#32
private abbrev inf32 : BitVec 32 := 0x7f800000#32
private abbrev ninf32 : BitVec 32 := 0xff800000#32
private abbrev one64 : BitVec 64 := 0x3ff0000000000000#64
private abbrev qnan64 : BitVec 64 := 0x7ff8000000000000#64
private abbrev pz64 : BitVec 64 := 0#64
private abbrev nz64 : BitVec 64 := 0x8000000000000000#64

/-! ## Default NaNs -/

example : x86.defaultNaN .binary32 = 0xffc00000#32 := by decide +kernel
example : x86.defaultNaN .binary64 = 0xfff8000000000000#64 := by decide +kernel
example : rv.defaultNaN .binary32 = 0x7fc00000#32 := by decide +kernel
example : rv.defaultNaN .binary64 = 0x7ff8000000000000#64 := by decide +kernel
example : arm.defaultNaN .binary32 = 0x7fc00000#32 := by decide +kernel

-- Invalid on non-NaN operands: ∞ + (−∞) yields each profile's default NaN.
example : (x86.add .binary32 .nearestTiesToEven inf32 ninf32).value = 0xffc00000#32 := by
  decide +kernel
example : (rv.add .binary32 .nearestTiesToEven inf32 ninf32).value = 0x7fc00000#32 := by
  decide +kernel
example : (arm.add .binary32 .nearestTiesToEven inf32 ninf32).value = 0x7fc00000#32 := by
  decide +kernel

/-! ## NaN propagation -/

-- x86: first NaN operand, quieted; invalid for the signaling operand.
example : x86.add .binary32 .nearestTiesToEven snan32 0x7fc00005#32 =
    { value := 0x7fc00001#32, flags := { invalidOperation := true } } := by decide +kernel
example : (x86.add .binary32 .nearestTiesToEven 0x7fc00005#32 snan32).value =
    0x7fc00005#32 := by decide +kernel
-- AArch64 with DN = 0: a signaling NaN takes precedence over an earlier quiet NaN.
example : (arm.add .binary32 .nearestTiesToEven 0x7fc00005#32 snan32).value =
    0x7fc00001#32 := by decide +kernel
-- AArch64 with DN = 1 and RISC-V: the default NaN.
example : (armDN.add .binary32 .nearestTiesToEven 0x7fc00005#32 snan32).value = qnan32 := by
  decide +kernel
example : (rv.mul .binary32 .nearestTiesToEven 0xffc12345#32 one32).value = qnan32 := by
  decide +kernel

/-! ## Minimum and maximum -/

-- x86 `MINSD`: the second operand when either is a NaN or both are zeros.
example : (x86.minMaxBase (fmt := .binary64) false qnan64 one64).value = one64 := by decide +kernel
example : (x86.minMaxBase (fmt := .binary64) false one64 qnan64).value = qnan64 := by decide +kernel
example : (x86.minMaxBase (fmt := .binary64) false pz64 nz64).value = nz64 := by decide +kernel
example : (x86.minMaxBase (fmt := .binary64) false nz64 pz64).value = pz64 := by decide +kernel
example : (x86.minMaxBase (fmt := .binary64) false qnan64 one64).flags =
    { invalidOperation := true } := by decide +kernel
-- RISC-V `FMIN`: the number when one operand is a NaN; -0 < +0.
example : (rv.minMaxBase (fmt := .binary32) false qnan32 one32).value = one32 := by decide +kernel
example : (rv.minMaxBase (fmt := .binary32) false 0#32 0x80000000#32).value = 0x80000000#32 := by
  decide +kernel
example : (rv.minMaxBase (fmt := .binary32) false qnan32 qnan32).value = qnan32 := by decide +kernel
-- AArch64 `FMIN` propagates NaNs; `FMINNM` ignores a single quiet NaN.
example : (arm.minMaxBase (fmt := .binary32) false qnan32 one32).value = qnan32 := by decide +kernel
example : (arm.minMaxWith (fmt := .binary32) aarch64FMinNMRule false qnan32 one32).value =
    one32 := by decide +kernel
example : (arm.minMaxWith (fmt := .binary32) aarch64FMinNMRule false snan32 one32).value =
    0x7fc00001#32 := by decide +kernel

-- Agreement with WebAssembly `fmin`: x86 disagrees exactly on (-0, +0) and NaN cases.
example : MinMaxRule.agreesWithWasm (fmt := .binary64) .x86 false nz64 pz64 = false := by decide +kernel
example : MinMaxRule.agreesWithWasm (fmt := .binary64) .x86 false pz64 nz64 = true := by decide +kernel
example : MinMaxRule.agreesWithWasm (fmt := .binary64) .x86 false qnan64 one64 = false := by decide +kernel
example :
    MinMaxRule.agreesWithWasm (fmt := .binary32) .minimumNumber false qnan32 one32 = false := by
  decide +kernel

/-! ## Float to integer -/

-- x86 `CVTTSD2SI` of a NaN: the integer indefinite, with invalid.
example : x86.toInt .binary64 IntFormat.i64 .towardZero qnan64 =
    { value := 0x8000000000000000#64, flags := { invalidOperation := true } } := by decide +kernel
example : (x86.toInt .binary32 IntFormat.i32 .towardZero 0x4f000000#32).value =
    0x80000000#32 := by decide +kernel
-- AVX-512 unsigned indefinite.
example : (x86.toInt .binary32 IntFormat.u32 .towardZero ninf32).value = 0xffffffff#32 := by
  decide +kernel
-- RISC-V `FCVT.W.S`: NaN converts to the maximum, overflow saturates.
example : (rv.toInt .binary32 IntFormat.i32 .towardZero qnan32).value = 0x7fffffff#32 := by
  decide +kernel
example : (rv.toInt .binary32 IntFormat.i32 .towardZero ninf32).value = 0x80000000#32 := by
  decide +kernel
example : (rv.toInt .binary32 IntFormat.u32 .towardZero 0xbf800000#32).value = 0#32 := by
  decide +kernel
-- AArch64 `FCVTZS`: NaN converts to zero.
example : (arm.toInt .binary32 IntFormat.i32 .towardZero qnan32).value = 0#32 := by decide +kernel
-- In range, every profile truncates exactly: -1.5 → -1.
example : (x86.toInt .binary32 IntFormat.i32 .towardZero 0xbfc00000#32).value =
    0xffffffff#32 := by decide +kernel

/-! ## Conversions between formats -/

-- NaN payloads keep their high bits and are quieted (x86, AArch64 with DN = 0).
example : (x86.convert .binary32 .binary64 .nearestTiesToEven snan32).value =
    0x7ff8000020000000#64 := by decide +kernel
example : (x86.convert .binary64 .binary32 .nearestTiesToEven 0x7ff0000000000001#64).value =
    qnan32 := by decide +kernel
example : (rv.convert .binary32 .binary64 .nearestTiesToEven snan32).value = qnan64 := by
  decide +kernel

/-! ## Subnormal flushing -/

private abbrev x86FTZ : Profile := Profile.x86SSE { flushToZero := true }
private abbrev x86DAZ : Profile := Profile.x86SSE { denormalsAreZeros := true }
private abbrev armFZ : Profile := Profile.aarch64 { flushToZero := true }

-- An exact subnormal difference: kept without FTZ, flushed with PE and UE on x86 FTZ,
-- flushed with UFC only on AArch64 FZ.
example : (x86.sub .binary32 .nearestTiesToEven 0x00800001#32 0x00800000#32).value =
    1#32 := by decide +kernel
example : x86FTZ.sub .binary32 .nearestTiesToEven 0x00800001#32 0x00800000#32 =
    { value := 0#32, flags := { underflow := true, inexact := true } } := by decide +kernel
example : armFZ.sub .binary32 .nearestTiesToEven 0x00800001#32 0x00800000#32 =
    { value := 0#32, flags := { underflow := true } } := by decide +kernel
-- DAZ: a subnormal operand is read as zero and reported as a subnormal operand.
example : x86DAZ.add .binary32 .nearestTiesToEven 1#32 0#32 =
    { value := 0#32, subnormalOperand := true } := by decide +kernel
example : x86.add .binary32 .nearestTiesToEven 1#32 0#32 =
    { value := 1#32, subnormalOperand := true } := by decide +kernel

/-! ## Comparisons -/

-- `UCOMISS` is quiet and `COMISS` signaling on a quiet NaN.
example : (x86.compare (fmt := .binary32) false qnan32 one32).flags = Flags.empty := by decide +kernel
example : (x86.compare (fmt := .binary32) true qnan32 one32).flags =
    { invalidOperation := true } := by decide +kernel
example : x86ComisFlags (x86.compare (fmt := .binary32) false qnan32 one32).value =
    (true, true, true) := by decide +kernel
example : x86ComisFlags (x86.compare (fmt := .binary32) false one32 qnan32).value =
    (true, true, true) := by decide +kernel
example : x86ComisFlags (x86.compare (fmt := .binary32) false 0#32 0x80000000#32).value =
    (true, false, false) := by decide +kernel
-- `CMPSS` predicate 1 (LT_OS) and 17 (LT_OQ).
example : x86ComparePredicate 1 = Predicate.ltSignaling := by decide +kernel
example : x86ComparePredicate 17 = { Predicate.ltSignaling with signaling := false } := by decide +kernel
example : (x86.comparePredicate (fmt := .binary32) (x86ComparePredicate 4) qnan32 qnan32).value =
    true := by decide +kernel
-- RISC-V `FLT` signals on a quiet NaN; `FEQ` does not.
example : (rv.comparePredicate (fmt := .binary32) riscvFlt qnan32 one32).flags =
    { invalidOperation := true } := by decide +kernel
example : (rv.comparePredicate (fmt := .binary32) riscvFeq qnan32 one32).flags = Flags.empty := by
  decide +kernel
example :
    aarch64CompareNZCV (arm.compare (fmt := .binary32) false one32 inf32).value = 0b1000#4 := by
  decide +kernel

/-! ## Control-register decoding -/

example : MXCSRControl.ofBits 0x1f80#32 = {} := by decide +kernel
example : MXCSRControl.ofBits 0x9fc0#32 =
    { denormalsAreZeros := true, flushToZero := true } := by decide +kernel
example : MXCSRControl.ofBits 0x7f80#32 = { rounding := .towardZero } := by decide +kernel
-- FZ set with underflow unmasked (UM, bit 11, clear): FZ is ignored (SDM Vol. 1
-- §10.2.3.3).
example : MXCSRControl.ofBits 0x9780#32 = {} := by decide +kernel
example : riscvRoundingMode? 4#3 = some .nearestTiesToAway := by decide +kernel
example : riscvRoundingMode? 7#3 = none := by decide +kernel
example : riscvRoundingSelect? 7#3 = some .dynamic := by decide +kernel
example : riscvRoundingSelect? 1#3 = some (.static .towardZero) := by decide +kernel
example : riscvRoundingSelect? 5#3 = none := by decide +kernel
example : FPCRControl.ofBits 0x03000000#64 = { defaultNaN := true, flushToZero := true } := by
  decide +kernel

/-! ## Directed rounding and FMA -/

-- 1 + 2^-24 in binary32: nearest-even gives 1, toward +∞ the next value.
example : (rv.add .binary32 .nearestTiesToEven one32 0x33800000#32).value = one32 := by decide +kernel
example : (rv.add .binary32 .towardPositive one32 0x33800000#32).value = 0x3f800001#32 := by
  decide +kernel
-- (±∞ × 0) + qNaN: default NaN and invalid on RISC-V and AArch64.
example : rv.fmaWith .binary32 riscvFmaNaNRule .nearestTiesToEven inf32 0#32 0x7fc00005#32 =
    { value := qnan32, flags := { invalidOperation := true } } := by decide +kernel
example : arm.fmaWith .binary32 aarch64FmaNaNRule .nearestTiesToEven inf32 0#32
    0x7fc00005#32 = { value := qnan32, flags := { invalidOperation := true } } := by decide +kernel
-- AArch64 examines the addend first.
example : (arm.fmaWith .binary32 aarch64FmaNaNRule .nearestTiesToEven 0x7fc00001#32 one32
    0x7fc00002#32).value = 0x7fc00002#32 := by decide +kernel

/-! ## Exception flags

Binary64 constants: `1e308` is 7FE1CCF385EBC8A0H, `10` is 4024000000000000H,
`0.1`, `0.2` and `0.1 + 0.2` are 3FB999999999999AH, 3FC999999999999AH and
3FD3333333333334H. -/

private abbrev rne : RoundingMode := .nearestTiesToEven
private abbrev inf64 : BitVec 64 := 0x7ff0000000000000#64

-- 1 / 0: divide-by-zero and an exact infinity (x86 `DIVSS`).
example : x86.div .binary32 rne one32 0#32 =
    { value := inf32, flags := { divisionByZero := true } } := by decide +kernel
-- -1 / -0 is +∞ as well.
example : x86.div .binary32 rne 0xbf800000#32 0x80000000#32 =
    { value := inf32, flags := { divisionByZero := true } } := by decide +kernel
-- 0 / 0: invalid, x86 default NaN.
example : x86.div .binary32 rne 0#32 0#32 =
    { value := 0xffc00000#32, flags := { invalidOperation := true } } := by decide +kernel

-- 1e308 * 10: overflow and inexact; the result is +∞ to nearest and the largest
-- finite number toward zero.
example : x86.mul .binary64 rne 0x7fe1ccf385ebc8a0#64 0x4024000000000000#64 =
    { value := inf64, flags := { overflow := true, inexact := true } } := by decide +kernel
example : x86.mul .binary64 .towardZero 0x7fe1ccf385ebc8a0#64 0x4024000000000000#64 =
    { value := 0x7fefffffffffffff#64, flags := { overflow := true, inexact := true } } := by
  decide +kernel

-- sqrt(-1): invalid, with each profile's default NaN (x86 `SQRTSD`, RISC-V `FSQRT.D`).
example : x86.sqrt .binary64 rne 0xbff0000000000000#64 =
    { value := 0xfff8000000000000#64, flags := { invalidOperation := true } } := by decide +kernel
example : rv.sqrt .binary64 rne 0xbff0000000000000#64 =
    { value := qnan64, flags := { invalidOperation := true } } := by decide +kernel
-- sqrt(-0) is -0 and raises nothing; sqrt(2) is inexact.
example : x86.sqrt .binary64 rne nz64 = { value := nz64 } := by decide +kernel
example : (x86.sqrt .binary64 rne 0x4000000000000000#64).flags = { inexact := true } := by
  decide +kernel

-- 0.1 + 0.2 is inexact.
example : x86.add .binary64 rne 0x3fb999999999999a#64 0x3fc999999999999a#64 =
    { value := 0x3fd3333333333334#64, flags := { inexact := true } } := by decide +kernel
-- A signaling NaN operand raises invalid and nothing else, even with an
-- otherwise inexact computation.
example : (x86.add .binary64 rne 0x7ff0000000000001#64 0x3fb999999999999a#64).flags =
    { invalidOperation := true } := by decide +kernel

-- The smallest binary64 subnormal times 0.5: tiny and inexact under both tininess
-- conventions; the result rounds to +0 (ties to even).
example : x86.mul .binary64 rne 1#64 0x3fe0000000000000#64 =
    { value := pz64, flags := { underflow := true, inexact := true },
      subnormalOperand := true } := by decide +kernel
example : arm.mul .binary64 rne 1#64 0x3fe0000000000000#64 =
    { value := pz64, flags := { underflow := true, inexact := true },
      subnormalOperand := true } := by decide +kernel

/-! ### Tininess before and after rounding

`(1 - 2^-52) × (2^-1022 · (1 + 2^-52))` = `2^-1022 - 2^-1126` exactly
(`(2^53 - 2)(2^52 + 1) = 2^105 - 2`). It lies below `2^-1022`, so it is tiny
before rounding; rounding it to 53 bits with unbounded exponent gives `2^-1022`,
so it is not tiny after rounding. It is inexact, and rounds to `2^-1022`
(0010000000000000H) in the bounded format. -/

private abbrev justBelowOne : BitVec 64 := 0x3feffffffffffffe#64
private abbrev minNormalUp : BitVec 64 := 0x0010000000000001#64
private abbrev minNormal : BitVec 64 := 0x0010000000000000#64

-- The specification itself: underflow depends on the convention.
example : FlagSpec.mul .binary64 rne .afterRounding (Bits.datum (fmt := .binary64) justBelowOne)
    (Bits.datum (fmt := .binary64) minNormalUp) = { inexact := true } := by decide +kernel
example : FlagSpec.mul .binary64 rne .beforeRounding (Bits.datum (fmt := .binary64) justBelowOne)
    (Bits.datum (fmt := .binary64) minNormalUp) = { underflow := true, inexact := true } := by
  decide +kernel
-- x86 (`MULSD`, after rounding) and RISC-V (`FMUL.D`, after rounding): inexact only.
example : x86.mul .binary64 rne justBelowOne minNormalUp =
    { value := minNormal, flags := { inexact := true } } := by decide +kernel
example : rv.mul .binary64 rne justBelowOne minNormalUp =
    { value := minNormal, flags := { inexact := true } } := by decide +kernel
-- AArch64 (`FMUL`, before rounding): underflow and inexact, same result.
example : arm.mul .binary64 rne justBelowOne minNormalUp =
    { value := minNormal, flags := { underflow := true, inexact := true } } := by decide +kernel
-- With flushing: x86 FZ does not flush (not tiny after rounding); AArch64 FZ
-- flushes to +0 and raises Underflow alone.
example : x86FTZ.mul .binary64 rne justBelowOne minNormalUp =
    { value := minNormal, flags := { inexact := true } } := by decide +kernel
example : armFZ.mul .binary64 rne justBelowOne minNormalUp =
    { value := pz64, flags := { underflow := true } } := by decide +kernel
-- The same product negated flushes to -0 on AArch64.
example : armFZ.mul .binary64 rne 0xbfeffffffffffffe#64 minNormalUp =
    { value := nz64, flags := { underflow := true } } := by decide +kernel

/-! ### Input flushing -/

-- 1 / (smallest binary32 subnormal) overflows; with DAZ the divisor is +0, so the
-- division raises divide-by-zero instead, and the operand is reported as subnormal.
example : x86.div .binary32 rne one32 1#32 =
    { value := inf32, flags := { overflow := true, inexact := true }, subnormalOperand := true } := by
  decide +kernel
example : x86DAZ.div .binary32 rne one32 1#32 =
    { value := inf32, flags := { divisionByZero := true }, subnormalOperand := true } := by
  decide +kernel

/-! ### Comparisons and minimum/maximum -/

-- `UCOMISD` signals invalid for a signaling NaN only; `COMISD` for any NaN.
example : (x86.compare (fmt := .binary64) false 0x7ff0000000000001#64 one64).flags =
    { invalidOperation := true } := by decide +kernel
example : (x86.compare (fmt := .binary64) true qnan64 one64).flags =
    { invalidOperation := true } := by decide +kernel
example : (x86.compare (fmt := .binary64) false qnan64 one64).flags = {} := by decide +kernel
-- `MINSD` with a quiet NaN signals invalid; AArch64 `FMIN` and RISC-V `FMIN.D` do not.
example : (x86.minMaxBase (fmt := .binary64) false one64 qnan64).flags =
    { invalidOperation := true } := by decide +kernel
example : (arm.minMaxBase (fmt := .binary64) false one64 qnan64).flags = {} := by decide +kernel
example : (rv.minMaxBase (fmt := .binary64) false one64 qnan64).flags = {} := by decide +kernel

/-! ### Conversions -/

-- `CVTTSD2SI` of 3e9 into a 32-bit register: invalid and the integer indefinite.
example : x86.toInt .binary64 IntFormat.i32 .towardZero 0x41e65a0bc0000000#64 =
    { value := 0x80000000#32, flags := { invalidOperation := true } } := by decide +kernel
-- `CVTTSD2SI` of 1.5 truncates to 1 and raises precision; `CVTSD2SI` rounds to 2.
example : x86.toInt .binary64 IntFormat.i32 .towardZero 0x3ff8000000000000#64 =
    { value := 1#32, flags := { inexact := true } } := by decide +kernel
example : x86.toInt .binary64 IntFormat.i32 rne 0x3ff8000000000000#64 =
    { value := 2#32, flags := { inexact := true } } := by decide +kernel
-- `ROUNDSD` of 1.5: precision only when imm8[3] = 0.
example : x86.roundToIntegral .binary64 .towardZero true 0x3ff8000000000000#64 =
    { value := one64, flags := { inexact := true } } := by decide +kernel
example : x86.roundToIntegral .binary64 .towardZero false 0x3ff8000000000000#64 =
    { value := one64 } := by decide +kernel
-- DAZ on conversions and integral rounding, a reading of SDM Vol. 1 §10.2.3.4 not
-- confirmed on hardware. `ROUNDSS` of 2^-149 toward +∞ gives 1.0 with precision;
-- with DAZ the operand is +0, so the result is +0 without precision.
example : x86.roundToIntegral .binary32 .towardPositive true 1#32 =
    { value := one32, flags := { inexact := true }, subnormalOperand := true } := by
  decide +kernel
example : x86DAZ.roundToIntegral .binary32 .towardPositive true 1#32 =
    { value := 0#32, subnormalOperand := true } := by decide +kernel
-- `CVTTSS2SI` of 2^-149: 0 with precision; with DAZ, 0 without precision.
example : x86.toInt .binary32 IntFormat.i32 .towardZero 1#32 =
    { value := 0#32, flags := { inexact := true }, subnormalOperand := true } := by
  decide +kernel
example : x86DAZ.toInt .binary32 IntFormat.i32 .towardZero 1#32 =
    { value := 0#32, subnormalOperand := true } := by decide +kernel
-- `CVTSI2SD` of 2^53 + 1 rounds to 2^53 and is inexact.
example : x86.ofInt .binary64 rne (2 ^ 53 + 1) =
    { value := 0x4340000000000000#64, flags := { inexact := true } } := by decide +kernel
-- `CVTSD2SS` of 1e300 overflows.
example : x86.convert .binary64 .binary32 rne 0x7e37e43c8800759c#64 =
    { value := inf32, flags := { overflow := true, inexact := true } } := by decide +kernel
-- `CVTSS2SD` of a signaling NaN: invalid, quieted payload.
example : x86.convert .binary32 .binary64 rne snan32 =
    { value := 0x7ff8000020000000#64, flags := { invalidOperation := true } } := by
  decide +kernel

/-! ## The reference implementation -/

example : FloatImpl.Correct x86 (FloatImpl.reference x86 .binary64) :=
  FloatImpl.reference_correct x86 .binary64

end Silmaril.Numeric.Float.Tests
