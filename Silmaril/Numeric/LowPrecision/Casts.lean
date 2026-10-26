module

public import Silmaril.Numeric.LowPrecision.Formats
public import Silmaril.Numeric.Ieee754.Rounding

/-!
# Low-precision casts

Casts round once from the exact source value, including direct binary64
narrowing. Low-precision widening is exact for finite values and signed zero;
NaNs are canonicalized. IEEE-like targets use IEEE overflow behavior.
E4M3FN, FNUZ, and E2M1 conversions use the explicitly saturating profile:
overflow and infinity map to the largest finite magnitude. NaNs map to the
target's canonical NaN, or `none` for E2M1, which cannot represent NaN.

`DowncastRounding` names Triton's `rtne`/`rtz` choices; the generic
`quantizeBits?` API supports all five IEEE rounding directions. See
IEEE Std 754-2019 §§4.3, 5.4.2, and Triton's cast documentation:
<https://triton-lang.org/main/python-api/generated/triton.language.cast.html>.
`quantizeSaturatingBits?` selects finite saturation for IEEE-like targets too,
including E5M2. For binary16, bfloat16, E4M3FN, and E5M2 this follows the
NVIDIA PTX `cvt.satfinite` result policy (§9.7.10.24):
<https://docs.nvidia.com/cuda/parallel-thread-execution/#data-movement-and-conversion-instructions-cvt>.
E2M1 retains the explicit `none` result for NaN; PTX instead chooses its
positive largest finite value for that case.
The finite saturation profile follows OCP MX v1.0 §§5.3.1, 5.3.3, 6.3;
FNUZ uses the same explicitly chosen policy:
<https://www.opencompute.org/documents/ocp-microscaling-formats-mx-v1-0-spec-final-pdf>.
-/

@[expose] public section

namespace Silmaril.Numeric.LowPrecision

open Float.Model
open Float.Model.UnpackedFloat
open Silmaril.Numeric.Ieee754

/-- The floating-point downcast rounding modes exposed by Triton. -/
inductive DowncastRounding where
  | rtne
  | rtz
  deriving DecidableEq, Repr, Inhabited

def DowncastRounding.toRoundingMode : DowncastRounding → RoundingMode
  | .rtne => .nearestTiesToEven
  | .rtz => .towardZero

/-- The overflow behavior of a numeric conversion, independent of rounding. -/
inductive OverflowPolicy where
  /-- IEEE overflow for IEEE-like targets; finite saturation for the other formats. -/
  | formatDefault
  /-- Clamp overflowing magnitudes and infinities to the target's largest finite value. -/
  | saturateFinite
  deriving DecidableEq, Repr, Inhabited

def binary16CoreFormat : Format where
  mantissaBitsWithoutImplicit := 10
  exponentBits := 5

def bfloat16CoreFormat : Format where
  mantissaBitsWithoutImplicit := 7
  exponentBits := 8

def e5m2CoreFormat : Format where
  mantissaBitsWithoutImplicit := 2
  exponentBits := 5

/-- Round exactly once and pack an IEEE binary format. -/
def packCore (format : Format) (mode : DowncastRounding)
    (value : UnpackedFloat) : BitVec format.numBits :=
  Rounding.packRounded format mode.toRoundingMode value

/-- Widen a low IEEE binary format to binary32; finite values are exact. -/
def expandCore (format : Format) (bits : BitVec format.numBits) : Float32.Model :=
  Float32.Model.ofBits (UInt32.ofBitVec
    (Rounding.packRounded Format.binary32 .nearestTiesToEven (UnpackedFloat.unpack format bits)))

/-- Enumerate exact finite encodings. Used only for the small FP8/FP4 formats. -/
def finiteEncodings (format : FormatSpec) : List (Nat × ℚ) :=
  (List.range (2 ^ format.width)).filterMap fun bits =>
    (exactValue? format bits).map (fun value => (bits, value))

abbrev encodingSign := signBit

def distance (x y : ℚ) : ℚ := if x ≤ y then y - x else x - y

/-- Select the closest candidate, resolving midpoint ties in the selected mode. -/
def preferable (mode : RoundingMode) (source : ℚ)
    (best candidate : Nat × ℚ) : Nat × ℚ :=
  let bestDistance := distance source best.2
  let candidateDistance := distance source candidate.2
  if candidateDistance < bestDistance then candidate
  else if candidateDistance == bestDistance then
    match mode with
    | .nearestTiesToEven =>
      if best.1 % 2 == 1 && candidate.1 % 2 == 0 then candidate else best
    | .nearestTiesToAway =>
      if distance 0 best.2 < distance 0 candidate.2 then candidate else best
    | _ => best
  else best

/-- Round a finite rational to a small format with finite saturation.
Signed zero is preserved where available; FNUZ underflow uses its unique zero.
Directed modes restrict candidates to the requested side of the exact value.
If no candidate exists on that side, the result saturates at the boundary. -/
def roundFiniteBitsMode (format : FormatSpec) (rounding : RoundingMode)
    (negative : Bool) (source : ℚ) : Nat :=
  let candidates := (finiteEncodings format).filter fun (bits, value) =>
    encodingSign format bits == negative || (format.special == .fnuz && value == 0)
  let directedCandidates := candidates.filter fun (_, value) =>
    match rounding with
    | .towardZero => distance 0 value ≤ distance 0 source
    | .towardPositive => source ≤ value
    | .towardNegative => value ≤ source
    | _ => true
  let candidates := if directedCandidates.isEmpty then candidates else directedCandidates
  match candidates with
  | [] => 0
  | first :: rest => (rest.foldl (preferable rounding source) first).1

/-- Triton RTNE/RTZ convenience wrapper for finite saturation. -/
def roundFiniteBits (format : FormatSpec) (rounding : DowncastRounding)
    (negative : Bool) (source : ℚ) : Nat :=
  roundFiniteBitsMode format rounding.toRoundingMode negative source

/-- Exact unpacking, including each non-IEEE special-value encoding. -/
def unpackBits (format : FormatSpec) (bits : Nat) : UnpackedFloat :=
  let sign := if encodingSign format bits then Sign.negative else Sign.positive
  let exponent := exponentField format bits
  let fraction := fractionField format bits
  if isNaNBits format bits then .notANumber
  else if isInfinityBits format bits then .infinity sign
  else if hExponent : exponent = 0 then
    if hFraction : fraction = 0 then .zero sign
    else .finite sign fraction (1 - format.bias - format.fractionBits : Int) (by omega)
  else
    .finite sign (2 ^ format.fractionBits + fraction)
      ((exponent : Int) - format.bias - format.fractionBits) (by
        have hp : 0 < 2 ^ format.fractionBits := Nat.pow_pos (by decide)
        omega)

/-- Exact rational interpretation of an unpacked finite value. -/
def unpackedRat? : UnpackedFloat → Option ℚ
  | .zero _ => some 0
  | .finite sign mantissa exponent _ =>
    some (signedRat (sign == .negative) ((mantissa : ℚ) * (2 : ℚ) ^ exponent))
  | _ => none

/-- Largest finite magnitude with the requested sign. -/
def maxFiniteBits (format : FormatSpec) (negative : Bool) : Nat :=
  let magnitude := match format.special with
    | .ieee => format.signMask - 2 ^ format.fractionBits - 1
    | .e4m3fn => format.signMask - 2
    | .fnuz | .finiteOnly => format.signMask - 1
  magnitude + if negative then format.signMask else 0

/-- A fixed positive quiet NaN for IEEE encodings, the positive NaN for
E4M3FN, and the unique NaN for FNUZ. E2M1 has no NaN representation. -/
def canonicalNaNBits? (format : FormatSpec) : Option Nat :=
  match format.special with
  | .ieee => some (format.maxExponent * 2 ^ format.fractionBits + 2 ^ (format.fractionBits - 1))
  | .e4m3fn => some (format.signMask - 1)
  | .fnuz => some format.signMask
  | .finiteOnly => none

/-- Recover a core IEEE format only when the entire layout and bias agree. -/
def FormatSpec.ieeeCoreFormat? (format : FormatSpec) : Option Format :=
  if hm : 0 < format.fractionBits then
    if he : 2 ≤ format.exponentBits then
      let core : Format := ⟨format.fractionBits, hm, format.exponentBits, he⟩
      if format.width == core.numBits && format.bias == (core.exponentBias : Int) then some core
      else none
    else none
  else none

/-- Convert an exact unpacked value with one final rounding.
IEEE targets use IEEE overflow and canonical NaNs. For E4M3FN, FNUZ, and
E2M1, finite overflow and infinities saturate; NaNs canonicalize when the
target supports them and otherwise return `none`. Malformed generic IEEE
specifications also return `none`. All provided format specifications are valid. -/
def quantizeBits? (format : FormatSpec) (rounding : RoundingMode)
    (value : UnpackedFloat) : Option Nat := do
  if format.special == .ieee then
    let core ← format.ieeeCoreFormat?
    pure (Rounding.packRounded core rounding value).toNat
  else
    match value with
    | .notANumber => canonicalNaNBits? format
    | .infinity sign => some (maxFiniteBits format (sign == .negative))
    | .zero sign =>
      some (if sign == .negative && format.special != .fnuz then format.signMask else 0)
    | .finite sign mantissa exponent _ =>
      let q := signedRat (sign == .negative) ((mantissa : ℚ) * (2 : ℚ) ^ exponent)
      some (roundFiniteBitsMode format rounding (sign == .negative) q)

/-- Round once, with finite saturation for every target, including IEEE-like
formats. Only an infinite rounded result is replaced; directed rounding may
already have selected the largest finite value. NaNs and signed zeros retain
the behavior of `quantizeBits?`, as do unsupported or malformed targets.
This does not enumerate the encodings of IEEE-like formats. -/
def quantizeSaturatingBits? (format : FormatSpec) (rounding : RoundingMode)
    (value : UnpackedFloat) : Option Nat :=
  (quantizeBits? format rounding value).map fun bits =>
    if isInfinityBits format bits then maxFiniteBits format (signBit format bits) else bits

/-- Select an overflow policy while retaining a single final rounding. -/
def quantizeBitsWith? (format : FormatSpec) (rounding : RoundingMode)
    (overflow : OverflowPolicy) (value : UnpackedFloat) : Option Nat :=
  match overflow with
  | .formatDefault => quantizeBits? format rounding value
  | .saturateFinite => quantizeSaturatingBits? format rounding value

/-- Finite saturation leaves every non-infinite rounded result unchanged. -/
theorem quantizeSaturatingBits?_eq_of_not_infinity
    (format : FormatSpec) (rounding : RoundingMode) (value : UnpackedFloat) (bits : Nat)
    (hResult : quantizeBits? format rounding value = some bits)
    (hFinite : isInfinityBits format bits = false) :
    quantizeSaturatingBits? format rounding value = some bits := by
  simp [quantizeSaturatingBits?, hResult, hFinite]

/-- Formats without infinity already use finite saturation by default. -/
theorem quantizeSaturatingBits?_eq_of_non_ieee
    (format : FormatSpec) (rounding : RoundingMode) (value : UnpackedFloat)
    (hSpecial : format.special ≠ .ieee) :
    quantizeSaturatingBits? format rounding value = quantizeBits? format rounding value := by
  have hInfinity (bits : Nat) : isInfinityBits format bits = false := by
    cases hEncoding : format.special <;> simp_all [isInfinityBits]
  simp [quantizeSaturatingBits?, hInfinity]

/-- Saturation preserves precisely the conversion failures of the default policy. -/
@[simp] theorem quantizeSaturatingBits?_eq_none_iff
    (format : FormatSpec) (rounding : RoundingMode) (value : UnpackedFloat) :
    quantizeSaturatingBits? format rounding value = none ↔
      quantizeBits? format rounding value = none := by
  simp [quantizeSaturatingBits?]

@[simp] theorem quantizeBitsWith?_formatDefault
    (format : FormatSpec) (rounding : RoundingMode) (value : UnpackedFloat) :
    quantizeBitsWith? format rounding .formatDefault value =
      quantizeBits? format rounding value := rfl

@[simp] theorem quantizeBitsWith?_saturateFinite
    (format : FormatSpec) (rounding : RoundingMode) (value : UnpackedFloat) :
    quantizeBitsWith? format rounding .saturateFinite value =
      quantizeSaturatingBits? format rounding value := rfl

/-- Selecting an overflow policy does not change whether conversion is supported. -/
@[simp] theorem quantizeBitsWith?_eq_none_iff
    (format : FormatSpec) (rounding : RoundingMode) (overflow : OverflowPolicy)
    (value : UnpackedFloat) :
    quantizeBitsWith? format rounding overflow value = none ↔
      quantizeBits? format rounding value = none := by
  cases overflow <;> simp

/-- Round an exact value directly into binary16. -/
def F16.ofUnpacked (value : UnpackedFloat) (rounding : DowncastRounding := .rtne) : F16 :=
  ⟨UInt16.ofBitVec (packCore binary16CoreFormat rounding value)⟩

/-- Round an exact value directly into bfloat16. -/
def BF16.ofUnpacked (value : UnpackedFloat) (rounding : DowncastRounding := .rtne) : BF16 :=
  ⟨UInt16.ofBitVec (packCore bfloat16CoreFormat rounding value)⟩

/-- Convert to an FP8 element with the target-dependent overflow policy of `quantizeBits?`. -/
def F8.ofUnpacked? {format : F8Format} (value : UnpackedFloat)
    (rounding : RoundingMode := .nearestTiesToEven) : Option (F8 format) :=
  (quantizeBits? format.spec rounding value).map (fun bits => ⟨UInt8.ofNat bits⟩)

/-- Convert to FP8 with finite saturation, including E5M2 overflow and infinity.
NaNs canonicalize to the selected FP8 format's NaN. -/
def F8.ofUnpackedSaturating? {format : F8Format} (value : UnpackedFloat)
    (rounding : RoundingMode := .nearestTiesToEven) : Option (F8 format) :=
  (quantizeSaturatingBits? format.spec rounding value).map (fun bits => ⟨UInt8.ofNat bits⟩)

/-- Convert to an FP4 element with finite saturation; NaN returns `none`. -/
def F4.ofUnpacked? {format : F4Format} (value : UnpackedFloat)
    (rounding : RoundingMode := .nearestTiesToEven) : Option (F4 format) :=
  (quantizeBits? format.spec rounding value).map (fun bits => ⟨BitVec.ofNat 4 bits⟩)

namespace CastFromF32

/-- Round directly from F32 to F16, without an intermediate format. -/
def toF16 (x : F32) (rounding : DowncastRounding := .rtne) : F16 :=
  ⟨UInt16.ofBitVec (packCore binary16CoreFormat rounding x.model.unpack)⟩

/-- Round directly from F32 to BF16, without an intermediate format. -/
def toBF16 (x : F32) (rounding : DowncastRounding := .rtne) : BF16 :=
  ⟨UInt16.ofBitVec (packCore bfloat16CoreFormat rounding x.model.unpack)⟩

/-- Round directly from F32 to F8E5M2, without an intermediate format. -/
def toF8E5M2 (x : F32) (rounding : DowncastRounding := .rtne) : F8E5M2 :=
  ⟨UInt8.ofBitVec (packCore e5m2CoreFormat rounding x.model.unpack)⟩

/-- Saturating conversion to F8E4M3FN. Infinity saturates; NaN is preserved
as the target's canonical NaN when available, and otherwise returns `none`. -/
def toF8E4M3FNSaturating? (x : F32) (rounding : DowncastRounding := .rtne) : Option F8E4M3FN :=
  (quantizeBits? e4m3fnSpec rounding.toRoundingMode x.model.unpack).map
    (fun bits => ⟨UInt8.ofNat bits⟩)

/-- Compatibility name for `toF8E4M3FNSaturating?`. -/
abbrev toF8E4M3FN? := toF8E4M3FNSaturating?

/-- Saturating conversion to F8E4M3FNUZ. Infinity saturates; NaN is preserved
as the target's canonical NaN when available, and otherwise returns `none`. -/
def toF8E4M3FNUZSaturating? (x : F32) (rounding : DowncastRounding := .rtne) : Option F8E4M3FNUZ :=
  (quantizeBits? e4m3fnuzSpec rounding.toRoundingMode x.model.unpack).map
    (fun bits => ⟨UInt8.ofNat bits⟩)

/-- Compatibility name for `toF8E4M3FNUZSaturating?`. -/
abbrev toF8E4M3FNUZ? := toF8E4M3FNUZSaturating?

/-- Saturating conversion to F8E5M2FNUZ. Infinity saturates; NaN is preserved
as the target's canonical NaN when available, and otherwise returns `none`. -/
def toF8E5M2FNUZSaturating? (x : F32) (rounding : DowncastRounding := .rtne) : Option F8E5M2FNUZ :=
  (quantizeBits? e5m2fnuzSpec rounding.toRoundingMode x.model.unpack).map
    (fun bits => ⟨UInt8.ofNat bits⟩)

/-- Compatibility name for `toF8E5M2FNUZSaturating?`. -/
abbrev toF8E5M2FNUZ? := toF8E5M2FNUZSaturating?

/-- Saturating conversion to F4E2M1. Infinity saturates; NaN is preserved
as the target's canonical NaN when available, and otherwise returns `none`. -/
def toF4E2M1Saturating? (x : F32) (rounding : DowncastRounding := .rtne) : Option F4E2M1 :=
  (quantizeBits? e2m1Spec rounding.toRoundingMode x.model.unpack).map
    (fun bits => ⟨BitVec.ofNat 4 bits⟩)

/-- Compatibility name for `toF4E2M1Saturating?`. -/
abbrev toF4E2M1? := toF4E2M1Saturating?

end CastFromF32

namespace CastFromF64

/-- Round directly from F64 to F16, without an intermediate format. -/
def toF16 (x : F64) (rounding : DowncastRounding := .rtne) : F16 :=
  ⟨UInt16.ofBitVec (packCore binary16CoreFormat rounding x.model.unpack)⟩

/-- Round directly from F64 to BF16, without an intermediate format. -/
def toBF16 (x : F64) (rounding : DowncastRounding := .rtne) : BF16 :=
  ⟨UInt16.ofBitVec (packCore bfloat16CoreFormat rounding x.model.unpack)⟩

/-- Round directly from F64 to F8E5M2, without an intermediate format. -/
def toF8E5M2 (x : F64) (rounding : DowncastRounding := .rtne) : F8E5M2 :=
  ⟨UInt8.ofBitVec (packCore e5m2CoreFormat rounding x.model.unpack)⟩

/-- Saturating conversion to F8E4M3FN. Infinity saturates; NaN is preserved
as the target's canonical NaN when available, and otherwise returns `none`. -/
def toF8E4M3FNSaturating? (x : F64) (rounding : DowncastRounding := .rtne) : Option F8E4M3FN :=
  (quantizeBits? e4m3fnSpec rounding.toRoundingMode x.model.unpack).map
    (fun bits => ⟨UInt8.ofNat bits⟩)

/-- Compatibility name for `toF8E4M3FNSaturating?`. -/
abbrev toF8E4M3FN? := toF8E4M3FNSaturating?

/-- Saturating conversion to F8E4M3FNUZ. Infinity saturates; NaN is preserved
as the target's canonical NaN when available, and otherwise returns `none`. -/
def toF8E4M3FNUZSaturating? (x : F64) (rounding : DowncastRounding := .rtne) : Option F8E4M3FNUZ :=
  (quantizeBits? e4m3fnuzSpec rounding.toRoundingMode x.model.unpack).map
    (fun bits => ⟨UInt8.ofNat bits⟩)

/-- Compatibility name for `toF8E4M3FNUZSaturating?`. -/
abbrev toF8E4M3FNUZ? := toF8E4M3FNUZSaturating?

/-- Saturating conversion to F8E5M2FNUZ. Infinity saturates; NaN is preserved
as the target's canonical NaN when available, and otherwise returns `none`. -/
def toF8E5M2FNUZSaturating? (x : F64) (rounding : DowncastRounding := .rtne) : Option F8E5M2FNUZ :=
  (quantizeBits? e5m2fnuzSpec rounding.toRoundingMode x.model.unpack).map
    (fun bits => ⟨UInt8.ofNat bits⟩)

/-- Compatibility name for `toF8E5M2FNUZSaturating?`. -/
abbrev toF8E5M2FNUZ? := toF8E5M2FNUZSaturating?

/-- Saturating conversion to F4E2M1. Infinity saturates; NaN is preserved
as the target's canonical NaN when available, and otherwise returns `none`. -/
def toF4E2M1Saturating? (x : F64) (rounding : DowncastRounding := .rtne) : Option F4E2M1 :=
  (quantizeBits? e2m1Spec rounding.toRoundingMode x.model.unpack).map
    (fun bits => ⟨BitVec.ofNat 4 bits⟩)

/-- Compatibility name for `toF4E2M1Saturating?`. -/
abbrev toF4E2M1? := toF4E2M1Saturating?

end CastFromF64

namespace F16

/-- Exact unpacked interpretation; NaN payloads are canonicalized. -/
def unpack (x : F16) : UnpackedFloat := unpackBits binary16Spec x.bits.toNat

/-- Widen exactly to binary32 (canonicalizing NaNs). -/
def toF32 (x : F16) : F32 :=
  ⟨UInt32.ofBitVec (Rounding.packRounded Format.binary32 .nearestTiesToEven x.unpack)⟩

/-- Widen exactly to binary64 (canonicalizing NaNs). -/
def toF64 (x : F16) : F64 :=
  ⟨UInt64.ofBitVec (Rounding.packRounded Format.binary64 .nearestTiesToEven x.unpack)⟩

def toBF16 (x : F16) (rounding : DowncastRounding := .rtne) : BF16 :=
  CastFromF32.toBF16 x.toF32 rounding

def toF8E5M2 (x : F16) (rounding : DowncastRounding := .rtne) : F8E5M2 :=
  CastFromF32.toF8E5M2 x.toF32 rounding

def toF8E4M3FNSaturating? (x : F16) (rounding : DowncastRounding := .rtne) : Option F8E4M3FN :=
  CastFromF32.toF8E4M3FNSaturating? x.toF32 rounding

abbrev toF8E4M3FN? := @toF8E4M3FNSaturating?

def toF8E4M3FNUZSaturating? (x : F16) (rounding : DowncastRounding := .rtne) : Option F8E4M3FNUZ :=
  CastFromF32.toF8E4M3FNUZSaturating? x.toF32 rounding

abbrev toF8E4M3FNUZ? := @toF8E4M3FNUZSaturating?

def toF8E5M2FNUZSaturating? (x : F16) (rounding : DowncastRounding := .rtne) : Option F8E5M2FNUZ :=
  CastFromF32.toF8E5M2FNUZSaturating? x.toF32 rounding

abbrev toF8E5M2FNUZ? := @toF8E5M2FNUZSaturating?

def toF4E2M1Saturating? (x : F16) (rounding : DowncastRounding := .rtne) : Option F4E2M1 :=
  CastFromF32.toF4E2M1Saturating? x.toF32 rounding

abbrev toF4E2M1? := @toF4E2M1Saturating?

end F16

namespace BF16

/-- Exact unpacked interpretation; NaN payloads are canonicalized. -/
def unpack (x : BF16) : UnpackedFloat := unpackBits bfloat16Spec x.bits.toNat

/-- Widen exactly to binary32 (canonicalizing NaNs). -/
def toF32 (x : BF16) : F32 :=
  ⟨UInt32.ofBitVec (Rounding.packRounded Format.binary32 .nearestTiesToEven x.unpack)⟩

/-- Widen exactly to binary64 (canonicalizing NaNs). -/
def toF64 (x : BF16) : F64 :=
  ⟨UInt64.ofBitVec (Rounding.packRounded Format.binary64 .nearestTiesToEven x.unpack)⟩

def toF16 (x : BF16) (rounding : DowncastRounding := .rtne) : F16 :=
  CastFromF32.toF16 x.toF32 rounding

def toF8E5M2 (x : BF16) (rounding : DowncastRounding := .rtne) : F8E5M2 :=
  CastFromF32.toF8E5M2 x.toF32 rounding

def toF8E4M3FNSaturating? (x : BF16) (rounding : DowncastRounding := .rtne) : Option F8E4M3FN :=
  CastFromF32.toF8E4M3FNSaturating? x.toF32 rounding

abbrev toF8E4M3FN? := @toF8E4M3FNSaturating?

def toF8E4M3FNUZSaturating? (x : BF16) (rounding : DowncastRounding := .rtne) : Option F8E4M3FNUZ :=
  CastFromF32.toF8E4M3FNUZSaturating? x.toF32 rounding

abbrev toF8E4M3FNUZ? := @toF8E4M3FNUZSaturating?

def toF8E5M2FNUZSaturating? (x : BF16) (rounding : DowncastRounding := .rtne) : Option F8E5M2FNUZ :=
  CastFromF32.toF8E5M2FNUZSaturating? x.toF32 rounding

abbrev toF8E5M2FNUZ? := @toF8E5M2FNUZSaturating?

def toF4E2M1Saturating? (x : BF16) (rounding : DowncastRounding := .rtne) : Option F4E2M1 :=
  CastFromF32.toF4E2M1Saturating? x.toF32 rounding

abbrev toF4E2M1? := @toF4E2M1Saturating?

end BF16

namespace F8

/-- Exact unpacked interpretation; NaN payloads are canonicalized. -/
def unpack {format : F8Format} (x : F8 format) : UnpackedFloat := unpackBits format.spec x.bits.toNat

/-- Widen exactly to binary32 (canonicalizing NaNs). -/
def toF32 {format : F8Format} (x : F8 format) : F32 :=
  ⟨UInt32.ofBitVec (Rounding.packRounded Format.binary32 .nearestTiesToEven x.unpack)⟩

/-- Widen exactly to binary64 (canonicalizing NaNs). -/
def toF64 {format : F8Format} (x : F8 format) : F64 :=
  ⟨UInt64.ofBitVec (Rounding.packRounded Format.binary64 .nearestTiesToEven x.unpack)⟩

def toF16 {format : F8Format} (x : F8 format) (rounding : DowncastRounding := .rtne) : F16 :=
  CastFromF32.toF16 x.toF32 rounding

def toBF16 {format : F8Format} (x : F8 format) (rounding : DowncastRounding := .rtne) : BF16 :=
  CastFromF32.toBF16 x.toF32 rounding

def toF8E5M2 {format : F8Format} (x : F8 format) (rounding : DowncastRounding := .rtne) : F8E5M2 :=
  CastFromF32.toF8E5M2 x.toF32 rounding

def toF8E4M3FNSaturating? {format : F8Format} (x : F8 format) (rounding : DowncastRounding := .rtne) : Option F8E4M3FN :=
  CastFromF32.toF8E4M3FNSaturating? x.toF32 rounding

abbrev toF8E4M3FN? {format : F8Format} := @toF8E4M3FNSaturating? format

def toF8E4M3FNUZSaturating? {format : F8Format} (x : F8 format) (rounding : DowncastRounding := .rtne) : Option F8E4M3FNUZ :=
  CastFromF32.toF8E4M3FNUZSaturating? x.toF32 rounding

abbrev toF8E4M3FNUZ? {format : F8Format} := @toF8E4M3FNUZSaturating? format

def toF8E5M2FNUZSaturating? {format : F8Format} (x : F8 format) (rounding : DowncastRounding := .rtne) : Option F8E5M2FNUZ :=
  CastFromF32.toF8E5M2FNUZSaturating? x.toF32 rounding

abbrev toF8E5M2FNUZ? {format : F8Format} := @toF8E5M2FNUZSaturating? format

def toF4E2M1Saturating? {format : F8Format} (x : F8 format) (rounding : DowncastRounding := .rtne) : Option F4E2M1 :=
  CastFromF32.toF4E2M1Saturating? x.toF32 rounding

abbrev toF4E2M1? {format : F8Format} := @toF4E2M1Saturating? format

end F8

namespace F4

/-- Exact unpacked interpretation; NaN payloads are canonicalized. -/
def unpack {format : F4Format} (x : F4 format) : UnpackedFloat := unpackBits format.spec x.bits.toNat

/-- Widen exactly to binary32 (canonicalizing NaNs). -/
def toF32 {format : F4Format} (x : F4 format) : F32 :=
  ⟨UInt32.ofBitVec (Rounding.packRounded Format.binary32 .nearestTiesToEven x.unpack)⟩

/-- Widen exactly to binary64 (canonicalizing NaNs). -/
def toF64 {format : F4Format} (x : F4 format) : F64 :=
  ⟨UInt64.ofBitVec (Rounding.packRounded Format.binary64 .nearestTiesToEven x.unpack)⟩

def toF16 {format : F4Format} (x : F4 format) (rounding : DowncastRounding := .rtne) : F16 :=
  CastFromF32.toF16 x.toF32 rounding

def toBF16 {format : F4Format} (x : F4 format) (rounding : DowncastRounding := .rtne) : BF16 :=
  CastFromF32.toBF16 x.toF32 rounding

def toF8E5M2 {format : F4Format} (x : F4 format) (rounding : DowncastRounding := .rtne) : F8E5M2 :=
  CastFromF32.toF8E5M2 x.toF32 rounding

def toF8E4M3FNSaturating? {format : F4Format} (x : F4 format) (rounding : DowncastRounding := .rtne) : Option F8E4M3FN :=
  CastFromF32.toF8E4M3FNSaturating? x.toF32 rounding

abbrev toF8E4M3FN? {format : F4Format} := @toF8E4M3FNSaturating? format

def toF8E4M3FNUZSaturating? {format : F4Format} (x : F4 format) (rounding : DowncastRounding := .rtne) : Option F8E4M3FNUZ :=
  CastFromF32.toF8E4M3FNUZSaturating? x.toF32 rounding

abbrev toF8E4M3FNUZ? {format : F4Format} := @toF8E4M3FNUZSaturating? format

def toF8E5M2FNUZSaturating? {format : F4Format} (x : F4 format) (rounding : DowncastRounding := .rtne) : Option F8E5M2FNUZ :=
  CastFromF32.toF8E5M2FNUZSaturating? x.toF32 rounding

abbrev toF8E5M2FNUZ? {format : F4Format} := @toF8E5M2FNUZSaturating? format

def toF4E2M1Saturating? {format : F4Format} (x : F4 format) (rounding : DowncastRounding := .rtne) : Option F4E2M1 :=
  CastFromF32.toF4E2M1Saturating? x.toF32 rounding

abbrev toF4E2M1? {format : F4Format} := @toF4E2M1Saturating? format

end F4

end Silmaril.Numeric.LowPrecision
