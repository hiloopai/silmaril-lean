module

public import Silmaril.Numeric.Ieee754.EncodingCorrectness

/-!
# Format-generic interchange encodings for architecture profiles

Architecture floating-point units operate on raw interchange encodings, so the
profile layer works on `Bits fmt`, the bit vectors of a Lean core
`Float.Model.Format`. Every definition here is generic in the format, so binary16
(x86 F16C and AVX-512 FP16, RISC-V Zfh, AArch64 half precision) can reuse it.

The field layout, NaN encodings and the quiet bit follow IEEE 754-2019 §3.4
(binary interchange encoding) and §6.2.1 (a quiet NaN has the first bit of the
trailing significand set; a signaling NaN has it clear and some other trailing
bit set). Architectures agree on this quiet-bit convention:

* x86: Intel SDM Vol. 1 §4.8.3.4 "NaNs" (the most significant fraction bit
  distinguishes QNaN from SNaN) and §4.8.3.5 (an SNaN operand is converted to a
  QNaN by setting that bit).
* RISC-V: Unprivileged ISA, "F" extension, section "NaN Generation and
  Propagation" (canonical NaN has only the quiet bit set).
* AArch64: Arm ARM (DDI 0487) pseudocode `FPProcessNaN` (quieting sets
  `result<topfrac>`) and `FPDefaultNaN`.

`quiet`, `defaultNaN`, `convertNaN` and `flushSubnormal` are the shared bit-level
building blocks; which one an operation applies is chosen by a `Profile`.
-/

@[expose] public section

namespace Silmaril.Numeric.Float

open Float.Model Float.Model.UnpackedFloat

/-- A raw interchange encoding of the format `fmt`. -/
abbrev Bits (fmt : Float.Model.Format) := BitVec fmt.numBits

namespace Bits

variable {fmt : Format}

/-- The trailing-significand mask of the quiet bit (IEEE 754-2019 §6.2.1). -/
def quietMask (fmt : Format) : BitVec fmt.mantissaBitsWithoutImplicit :=
  BitVec.twoPow _ (fmt.mantissaBitsWithoutImplicit - 1)

/-- The sign field as the core model's sign. -/
def sign (b : Bits fmt) : Sign := Sign.ofBitVec (unpackSign b)

/-- The raw sign bit. -/
def signBit (b : Bits fmt) : Bool := unpackSign b == 1#1

/-- Any NaN encoding: all-ones exponent and nonzero trailing significand. -/
def isNaN (b : Bits fmt) : Bool := unpackExponent b == -1#_ && unpackMantissa b != 0#_

/-- A quiet NaN: a NaN with the quiet bit set. This is also WebAssembly's
"arithmetic NaN" class. -/
def isQuietNaN (b : Bits fmt) : Bool :=
  isNaN b && (unpackMantissa b).getLsbD (fmt.mantissaBitsWithoutImplicit - 1)

/-- A signaling NaN: a NaN with the quiet bit clear. -/
def isSignalingNaN (b : Bits fmt) : Bool :=
  isNaN b && !(unpackMantissa b).getLsbD (fmt.mantissaBitsWithoutImplicit - 1)

/-- A NaN whose trailing significand is exactly the quiet bit, with either sign.
This is WebAssembly's canonical-NaN class and the payload of every
architecture default NaN modeled here. -/
def isCanonicalNaN (b : Bits fmt) : Bool := isNaN b && unpackMantissa b == quietMask fmt

/-- Either not a NaN or a canonical NaN. -/
def isNonNaNOrCanonicalNaN (b : Bits fmt) : Bool := !isNaN b || isCanonicalNaN b

/-- A nonzero value with a zero exponent field. -/
def isSubnormal (b : Bits fmt) : Bool := unpackExponent b == 0#_ && unpackMantissa b != 0#_

/-- Either signed zero. -/
def isZero (b : Bits fmt) : Bool := unpackExponent b == 0#_ && unpackMantissa b == 0#_

/-- Either infinity. -/
def isInfinite (b : Bits fmt) : Bool := unpackExponent b == -1#_ && unpackMantissa b == 0#_

/-- Set the quiet bit, preserving sign and the remaining payload bits. Applied to
a signaling NaN this is the quieting rule of all three architectures; applied to
a quiet NaN it is the identity. -/
def quiet (b : Bits fmt) : Bits fmt :=
  packComponents fmt (sign b) (unpackExponent b) (unpackMantissa b ||| quietMask fmt)

/-- A NaN whose only trailing-significand bit is the quiet bit, with the given
sign. `defaultNaN fmt false` is the core model's `packedNaN`. -/
def defaultNaN (fmt : Format) (negative : Bool) : Bits fmt :=
  packComponents fmt (if negative then .negative else .positive) (-1#_) (quietMask fmt)

/-- Replace a subnormal encoding by the zero of the same sign; other encodings
are unchanged. This is the input half of x86 DAZ and AArch64 `FPCR.FZ`. -/
def flushSubnormal (b : Bits fmt) : Bits fmt :=
  if isSubnormal b then packedZero fmt (sign b) else b

/-- Convert a NaN between formats while keeping its sign and the most significant
payload bits, then set the quiet bit: widening appends zero payload bits and
narrowing drops the least significant ones. This is the payload rule of Arm
`FPConvertNaN` and of the x86 SSE conversions `CVTSS2SD`/`CVTSD2SS` for NaN
operands (Intel SDM Vol. 1 §4.8.3.5 and Table 4-7). -/
def convertNaN (src dst : Format) (b : Bits src) : Bits dst :=
  let payload := (unpackMantissa b).toNat
  let moved :=
    if src.mantissaBitsWithoutImplicit ≤ dst.mantissaBitsWithoutImplicit then
      payload <<< (dst.mantissaBitsWithoutImplicit - src.mantissaBitsWithoutImplicit)
    else payload >>> (src.mantissaBitsWithoutImplicit - dst.mantissaBitsWithoutImplicit)
  packComponents dst (sign b) (-1#_) (BitVec.ofNat _ moved ||| quietMask dst)

/-- The decoded value, using the core model's decoder. -/
def value (b : Bits fmt) : UnpackedFloat := unpack fmt b

/-! ## Basic facts -/

theorem mantissaBits_pos (fmt : Format) : 0 < fmt.mantissaBitsWithoutImplicit := fmt.hm

theorem quietMask_getLsbD_eq (fmt : Format) (i : Nat) :
    (quietMask fmt).getLsbD i = decide (i = fmt.mantissaBitsWithoutImplicit - 1) := by
  have := fmt.hm
  simp only [quietMask, BitVec.getLsbD_twoPow]
  by_cases h : i = fmt.mantissaBitsWithoutImplicit - 1
  · subst h
    simp
    omega
  · simp [h, Ne.symm h]

@[simp] theorem quietMask_getLsbD (fmt : Format) :
    (quietMask fmt).getLsbD (fmt.mantissaBitsWithoutImplicit - 1) = true := by
  simp [quietMask_getLsbD_eq]

theorem quietMask_toNat (fmt : Format) :
    (quietMask fmt).toNat = 2 ^ (fmt.mantissaBitsWithoutImplicit - 1) := by
  have := fmt.hm
  rw [quietMask, BitVec.toNat_twoPow]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))

theorem ne_zero_of_getLsbD {w : Nat} {v : BitVec w} {i : Nat} (h : v.getLsbD i = true) :
    v ≠ 0#w := by
  intro hv
  subst hv
  simp at h

theorem quietMask_ne_zero (fmt : Format) : quietMask fmt ≠ 0#_ :=
  ne_zero_of_getLsbD (quietMask_getLsbD fmt)

/-- The all-ones exponent is not the zero exponent. -/
theorem allOnes_exponent_ne_zero (fmt : Format) : (-1#fmt.exponentBits) ≠ 0#_ := by
  intro h0
  have h := congrArg BitVec.toNat h0
  rw [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes] at h
  have := fmt.he
  have hp : 1 < 2 ^ fmt.exponentBits := Nat.one_lt_two_pow_iff.mpr (by omega)
  simp at h
  omega

@[simp] theorem unpackExponent_quiet (b : Bits fmt) :
    unpackExponent (quiet b) = unpackExponent b := by
  simp [quiet]

@[simp] theorem unpackMantissa_quiet (b : Bits fmt) :
    unpackMantissa (quiet b) = unpackMantissa b ||| quietMask fmt := by
  simp [quiet]

@[simp] theorem unpackExponent_defaultNaN (fmt : Format) (negative : Bool) :
    unpackExponent (defaultNaN fmt negative) = -1#_ := by
  simp [defaultNaN]

@[simp] theorem unpackMantissa_defaultNaN (fmt : Format) (negative : Bool) :
    unpackMantissa (defaultNaN fmt negative) = quietMask fmt := by
  simp [defaultNaN]

theorem defaultNaN_false (fmt : Format) : defaultNaN fmt false = packedNaN fmt := rfl

/-- Quieting any NaN produces a quiet NaN. -/
theorem isQuietNaN_quiet {b : Bits fmt} (h : isNaN b = true) : isQuietNaN (quiet b) = true := by
  simp only [isNaN, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  have hq : (unpackMantissa b ||| quietMask fmt).getLsbD
      (fmt.mantissaBitsWithoutImplicit - 1) = true := by
    simp [BitVec.getLsbD_or]
  simp [isQuietNaN, isNaN, h.1, hq, ne_zero_of_getLsbD hq]

/-- A quiet NaN is unchanged by quieting. -/
theorem quiet_of_isQuietNaN {b : Bits fmt} (h : isQuietNaN b = true) : quiet b = b := by
  simp only [isQuietNaN, Bool.and_eq_true] at h
  have hor : unpackMantissa b ||| quietMask fmt = unpackMantissa b := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_or, quietMask_getLsbD_eq]
    by_cases hi' : i = fmt.mantissaBitsWithoutImplicit - 1
    · subst hi'
      simp [h.2]
    · simp only [Bool.or_eq_left_iff_imp, decide_eq_true_eq]
      intro hc
      omega
  simp only [quiet, hor]
  exact Ieee754.Conformance.packComponents_unpack fmt b

theorem isQuietNaN_of_isCanonicalNaN {b : Bits fmt} (h : isCanonicalNaN b = true) :
    isQuietNaN b = true := by
  simp only [isCanonicalNaN, Bool.and_eq_true, beq_iff_eq] at h
  simp [isQuietNaN, h.1, h.2]

theorem isNaN_of_isQuietNaN {b : Bits fmt} (h : isQuietNaN b = true) : isNaN b = true := by
  simp only [isQuietNaN, Bool.and_eq_true] at h
  exact h.1

theorem isNaN_of_isCanonicalNaN {b : Bits fmt} (h : isCanonicalNaN b = true) : isNaN b = true := by
  simp only [isCanonicalNaN, Bool.and_eq_true] at h
  exact h.1

/-- Quieting leaves a canonical NaN unchanged. -/
theorem quiet_of_isCanonicalNaN {b : Bits fmt} (h : isCanonicalNaN b = true) : quiet b = b :=
  quiet_of_isQuietNaN (isQuietNaN_of_isCanonicalNaN h)

/-- Every default NaN is canonical. -/
theorem isCanonicalNaN_defaultNaN (fmt : Format) (negative : Bool) :
    isCanonicalNaN (defaultNaN fmt negative) = true := by
  simp [isCanonicalNaN, isNaN, quietMask_ne_zero]

theorem isNaN_defaultNaN (fmt : Format) (negative : Bool) : isNaN (defaultNaN fmt negative) = true
    :=
  isNaN_of_isCanonicalNaN (isCanonicalNaN_defaultNaN fmt negative)

theorem isNaN_packedNaN (fmt : Format) : isNaN (packedNaN fmt) = true :=
  isNaN_defaultNaN fmt false

/-- Converting a NaN between formats yields a quiet NaN. -/
theorem isQuietNaN_convertNaN (src dst : Format) (b : Bits src) :
    isQuietNaN (convertNaN src dst b) = true := by
  have hq : (BitVec.ofNat dst.mantissaBitsWithoutImplicit
      (if src.mantissaBitsWithoutImplicit ≤ dst.mantissaBitsWithoutImplicit then
        (unpackMantissa b).toNat <<< (dst.mantissaBitsWithoutImplicit -
            src.mantissaBitsWithoutImplicit)
      else (unpackMantissa b).toNat >>> (src.mantissaBitsWithoutImplicit -
        dst.mantissaBitsWithoutImplicit)) ||| quietMask dst).getLsbD
      (dst.mantissaBitsWithoutImplicit - 1) = true := by
    simp [BitVec.getLsbD_or]
  simp [convertNaN, isQuietNaN, isNaN, hq, ne_zero_of_getLsbD hq]

/-- Converting a canonical NaN between formats yields a canonical NaN. -/
theorem isCanonicalNaN_convertNaN (src dst : Format) {b : Bits src}
    (h : isCanonicalNaN b = true) : isCanonicalNaN (convertNaN src dst b) = true := by
  simp only [isCanonicalNaN, Bool.and_eq_true, beq_iff_eq] at h
  have hsrc := src.hm
  have hdst := dst.hm
  have hpayload : (unpackMantissa b).toNat = 2 ^ (src.mantissaBitsWithoutImplicit - 1) := by
    rw [h.2, quietMask_toNat]
  have hmoved : BitVec.ofNat dst.mantissaBitsWithoutImplicit
      (if src.mantissaBitsWithoutImplicit ≤ dst.mantissaBitsWithoutImplicit then
        (unpackMantissa b).toNat <<< (dst.mantissaBitsWithoutImplicit -
            src.mantissaBitsWithoutImplicit)
      else (unpackMantissa b).toNat >>> (src.mantissaBitsWithoutImplicit -
        dst.mantissaBitsWithoutImplicit)) = quietMask dst := by
    apply BitVec.eq_of_toNat_eq
    rw [quietMask_toNat, BitVec.toNat_ofNat, hpayload]
    split
    · rw [Nat.shiftLeft_eq, ← Nat.pow_add]
      have : src.mantissaBitsWithoutImplicit - 1 +
          (dst.mantissaBitsWithoutImplicit - src.mantissaBitsWithoutImplicit) =
          dst.mantissaBitsWithoutImplicit - 1 := by omega
      rw [this]
      exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
    · rw [Nat.shiftRight_eq_div_pow, Nat.pow_div (by omega) (by decide)]
      have : src.mantissaBitsWithoutImplicit - 1 -
          (src.mantissaBitsWithoutImplicit - dst.mantissaBitsWithoutImplicit) =
          dst.mantissaBitsWithoutImplicit - 1 := by omega
      rw [this]
      exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  simp [convertNaN, isCanonicalNaN, isNaN, hmoved, quietMask_ne_zero]

/-- The decoder yields `notANumber` exactly for NaN encodings. -/
theorem value_eq_notANumber_iff (b : Bits fmt) : value b = .notANumber ↔ isNaN b = true := by
  unfold value UnpackedFloat.unpack
  simp only [isNaN, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  by_cases he : unpackExponent b = -1#_
  · by_cases hm : unpackMantissa b = 0#_ <;> simp [he, hm]
  · simp only [he, ↓reduceIte, false_and, iff_false]
    split
    · split <;> simp
    · simp

theorem value_isNaN (b : Bits fmt) : (value b).isNaN = isNaN b := by
  cases h : isNaN b
  · have : value b ≠ .notANumber := fun hv => by simp [(value_eq_notANumber_iff b).mp hv] at h
    cases hv : value b <;> simp_all [UnpackedFloat.isNaN]
  · rw [(value_eq_notANumber_iff b).mpr h]
    rfl

theorem isNaN_eq_false_of_isSubnormal {b : Bits fmt} (h : isSubnormal b = true) :
    isNaN b = false := by
  simp only [isSubnormal, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  simp [isNaN, h.1, Ne.symm (allOnes_exponent_ne_zero fmt)]

@[simp] theorem isNaN_packedZero (fmt : Format) (s : Sign) : isNaN (packedZero fmt s) = false := by
  simp [isNaN, packedZero]

/-- Flushing never creates or removes a NaN. -/
@[simp] theorem isNaN_flushSubnormal (b : Bits fmt) : isNaN (flushSubnormal b) = isNaN b := by
  unfold flushSubnormal
  split
  next h => rw [isNaN_packedZero, isNaN_eq_false_of_isSubnormal h]
  next => rfl

@[simp] theorem isSignalingNaN_flushSubnormal (b : Bits fmt) :
    isSignalingNaN (flushSubnormal b) = isSignalingNaN b := by
  unfold flushSubnormal
  split
  next h =>
    simp only [isSignalingNaN, isNaN_packedZero, isNaN_eq_false_of_isSubnormal h, Bool.false_and]
  next => rfl

end Bits

end Silmaril.Numeric.Float
