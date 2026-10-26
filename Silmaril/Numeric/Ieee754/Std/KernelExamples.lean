module

public import Silmaril.Numeric.Ieee754.Std.Isa

/-!
# Kernel-checked samples

Concrete results of the executable `Std` profiles, checked by `decide +kernel`
(the kernel evaluates the rational arithmetic itself; no compiled code is
trusted). Expected values are those of SoftFloat 3e and of x86 hardware.
-/

namespace Silmaril.Numeric.Ieee754.Std.KernelExamples

open Silmaril.Numeric.Ieee754 Silmaril.Numeric.Ieee754.Std

abbrev E16 := Interchange.binary16.encoding
abbrev E32 := Interchange.binary32.encoding
abbrev E64 := Interchange.binary64.encoding
abbrev X80 := X87.encoding .hardware

def b32 (n : ℕ) : Fields := Fields.ofNat E32 n
def b64 (n : ℕ) : Fields := Fields.ofNat E64 n

-- binary16: 1 + 1 = 2
example : Isa.x86SSE.add E16 .nearestTiesToEven ⟨false, 15, 0⟩ ⟨false, 15, 0⟩ =
    (⟨false, 16, 0⟩, {}) := by decide +kernel

-- binary32: 1 / 3, inexact, in two directions
example : Isa.x86SSE.div E32 .nearestTiesToEven (b32 0x3F800000) (b32 0x40400000) =
    (b32 0x3EAAAAAB, { inexact := true }) := by decide +kernel
example : Isa.x86SSE.div E32 .towardZero (b32 0x3F800000) (b32 0x40400000) =
    (b32 0x3EAAAAAA, { inexact := true }) := by decide +kernel

-- binary32: √2 (irrational) rounds to 0x3FB504F3
example : Isa.riscv.sqrt E32 .nearestTiesToEven (b32 0x40000000) =
    (b32 0x3FB504F3, { inexact := true }) := by decide +kernel

-- signaling NaN + 1: x86 quiets the operand, RISC-V gives the canonical NaN
example : Isa.x86SSE.add E32 .nearestTiesToEven (b32 0x7F800001) (b32 0x3F800000) =
    (b32 0x7FC00001, { invalidOperation := true }) := by decide +kernel
example : Isa.riscv.add E32 .nearestTiesToEven (b32 0x7F800001) (b32 0x3F800000) =
    (b32 0x7FC00000, { invalidOperation := true }) := by decide +kernel

-- ∞ - ∞: x86 default NaN is negative, RISC-V canonical NaN positive
example : Isa.x86SSE.sub E32 .nearestTiesToEven (b32 0x7F800000) (b32 0x7F800000) =
    (b32 0xFFC00000, { invalidOperation := true }) := by decide +kernel
example : Isa.riscv.sub E32 .nearestTiesToEven (b32 0x7F800000) (b32 0x7F800000) =
    (b32 0x7FC00000, { invalidOperation := true }) := by decide +kernel

-- exact cancellation: +0, but -0 rounding toward negative (IEEE 754-2019 §6.3)
example : Isa.x86SSE.sub E32 .nearestTiesToEven (b32 0x3F800000) (b32 0x3F800000) =
    (b32 0x00000000, {}) := by decide +kernel
example : Isa.x86SSE.sub E32 .towardNegative (b32 0x3F800000) (b32 0x3F800000) =
    (b32 0x80000000, {}) := by decide +kernel

-- overflow: to infinity when rounding to nearest, to the largest finite toward zero
example : Isa.x86SSE.mul E32 .nearestTiesToEven (b32 0x7F7FFFFF) (b32 0x40000000) =
    (b32 0x7F800000, { overflow := true, inexact := true }) := by decide +kernel
example : Isa.x86SSE.mul E32 .towardZero (b32 0x7F7FFFFF) (b32 0x40000000) =
    (b32 0x7F7FFFFF, { overflow := true, inexact := true }) := by decide +kernel

-- gradual underflow: the least normal halved is an exact subnormal (no flags)
example : Isa.x86SSE.mul E32 .nearestTiesToEven (b32 0x00800000) (b32 0x3F000000) =
    (b32 0x00400000, {}) := by decide +kernel

-- binary64 ties to even and ties to away: 1 + 2^-53
example : Isa.x86SSE.add E64 .nearestTiesToEven (b64 0x3FF0000000000000) (b64 0x3CA0000000000000) =
    (b64 0x3FF0000000000000, { inexact := true }) := by decide +kernel
example : Isa.x86SSE.add E64 .nearestTiesToAway (b64 0x3FF0000000000000) (b64 0x3CA0000000000000) =
    (b64 0x3FF0000000000001, { inexact := true }) := by decide +kernel

-- fma(∞, 0, qNaN): x86 hardware propagates the addend quietly; SoftFloat signals
example : Isa.x86SSE.fma E32 .nearestTiesToEven (b32 0x7F800000) (b32 0) (b32 0x7FC12345) =
    (b32 0x7FC12345, {}) := by decide +kernel
example : Isa.softfloat8086SSE.fma E32 .nearestTiesToEven (b32 0x7F800000) (b32 0) (b32 0x7FC12345) =
    (b32 0xFFC00000, { invalidOperation := true }) := by decide +kernel

-- conversion out of range: x86 integer indefinite, RISC-V saturation
example : Isa.x86SSE.toInt E32 (IntFormat.signed 32) .towardZero true (b32 0x4F000000) =
    (-2147483648, { invalidOperation := true }) := by decide +kernel
example : Isa.riscv.toInt E32 (IntFormat.signed 32) .towardZero true (b32 0x4F000000) =
    (2147483647, { invalidOperation := true }) := by decide +kernel

-- x87: an unnormal operand is invalid on the hardware (result: real indefinite)
example : Isa.x87.add X80 .nearestTiesToEven ⟨false, 0x3FFF, 0x4000000000000000⟩
    ⟨false, 0x3FFF, 0x8000000000000000⟩ =
    (⟨true, 0x7FFF, 0xC000000000000000⟩, { invalidOperation := true }) := by decide +kernel

-- minimum/maximum variants on binary32 (`sse` is the x86 NaN rule, `rv` the RISC-V one)
def sse : List Fields → Fields := Isa.x86SSE.nan E32
def rv : List Fields → Fields := Isa.riscv.nan E32

-- x86 MINSS returns the second operand for equal zeros and for any NaN, signaling invalid on a NaN
example : minMax E32 sse .x86 false (b32 0x80000000) (b32 0x00000000) = (b32 0x00000000, {}) := by
  decide +kernel
example : minMax E32 sse .x86 false (b32 0x7FC00000) (b32 0x3F800000) =
    (b32 0x3F800000, { invalidOperation := true }) := by decide +kernel
example : minMax E32 sse .x86 false (b32 0x3F800000) (b32 0x7FC00000) =
    (b32 0x7FC00000, { invalidOperation := true }) := by decide +kernel
-- RISC-V FMIN.S (minimumNumber): -0 < +0, a quiet NaN is ignored without flags,
-- a signaling NaN is ignored but signals invalid, two NaNs give the canonical NaN
example : minMax E32 rv .minimumNumber2019 false (b32 0x00000000) (b32 0x80000000) =
    (b32 0x80000000, {}) := by decide +kernel
example : minMax E32 rv .minimumNumber2019 false (b32 0x7FC00000) (b32 0x3F800000) =
    (b32 0x3F800000, {}) := by decide +kernel
example : minMax E32 rv .minimumNumber2019 false (b32 0x7F800001) (b32 0x3F800000) =
    (b32 0x3F800000, { invalidOperation := true }) := by decide +kernel
example : minMax E32 rv .minimumNumber2019 true (b32 0x7FC00001) (b32 0xFF800001) =
    (b32 0x7FC00000, { invalidOperation := true }) := by decide +kernel
-- IEEE 754-2008 minNum: a signaling NaN gives a NaN; 2019 minimum: any NaN gives a NaN
example : minMax E32 rv .minNum2008 false (b32 0x7F800001) (b32 0x3F800000) =
    (b32 0x7FC00000, { invalidOperation := true }) := by decide +kernel
example : minMax E32 rv .minimum2019 false (b32 0x7FC00000) (b32 0x3F800000) =
    (b32 0x7FC00000, {}) := by decide +kernel

end Silmaril.Numeric.Ieee754.Std.KernelExamples
