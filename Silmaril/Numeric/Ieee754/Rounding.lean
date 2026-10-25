module

public import Silmaril.Numeric.Ieee754

/-!
# Directed binary floating-point rounding

Executable rounding and arithmetic for IEEE binary formats. The five rounding
directions follow IEEE 754-2019 §4.3; overflow selects infinity or the largest
finite magnitude according to §7.4. Subnormals are gradual, with no implicit
flush-to-zero. Exact cancellation uses the sign prescribed by §6.3.

Fused multiply-add follows §5.4.1: its product and sum are computed with
unbounded integer significands, and only the final result is rounded. This
remains true when the intermediate product would overflow or underflow the
destination format. Division and square root reuse Lean's integer quotient and
integer square-root residuals before applying the selected rounding direction.

These definitions model result values. They do not model IEEE exception flags,
traps, or implementation-specific NaN payload propagation. NaN results use the
positive canonical quiet encoding.

References: <https://standards.ieee.org/ieee/754/6210/>;
<https://docs.nvidia.com/cuda/parallel-thread-execution/#floating-point-instructions-fma>.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754

open Float.Model Float.Model.UnpackedFloat

namespace Rounding

/-- Round the truncated nonnegative magnitude using its exact residual class.
The sign determines the direction for `towardPositive` and `towardNegative`. -/
def roundMantissa (mode : RoundingMode) (sign : Sign) (mantissa : Nat)
    (accuracy : Accuracy) : Nat :=
  match accuracy with
  | .exact => mantissa
  | .inexact order =>
    match mode with
    | .nearestTiesToEven => accuracy.roundToNearestEven mantissa
    | .nearestTiesToAway => if order == .lt then mantissa else mantissa + 1
    | .towardZero => mantissa
    | .towardPositive => if sign == .positive then mantissa + 1 else mantissa
    | .towardNegative => if sign == .negative then mantissa + 1 else mantissa

@[simp] theorem roundMantissa_exact (mode : RoundingMode) (sign : Sign) (mantissa : Nat) :
    roundMantissa mode sign mantissa .exact = mantissa := rfl

/-- Round a significand whose exponent is already low enough for the target.
The second shift handles a carry from rounding; it discards no nonzero bits. -/
def roundWithAccuracy (format : Format) (mode : RoundingMode)
    (sign : Sign) (mantissa : Nat) (exponent : Int) (accuracy : Accuracy) : UnpackedFloat :=
  let (extended, exponent) := shiftToTargetExponent format mantissa exponent accuracy
  let rounded := roundMantissa mode sign extended.mantissa extended.accuracy
  let (finalExtended, finalExponent) := shiftToTargetExponent format rounded exponent .exact
  if h : finalExtended.mantissa = 0 then .zero sign
  else .finite sign finalExtended.mantissa finalExponent (Nat.pos_of_ne_zero h)

/-- Round an exact dyadic value into a target precision. Its exponent remains
unbounded here; `packRounded` applies the destination's overflow policy. -/
def roundUnpacked (format : Format) (mode : RoundingMode) : UnpackedFloat → UnpackedFloat
  | .notANumber => .notANumber
  | .infinity sign => .infinity sign
  | .zero sign => .zero sign
  | .finite sign mantissa exponent _ =>
    let target := format.targetExponent (totalExponent mantissa exponent)
    let (mantissa, exponent) := decreaseExponent mantissa exponent target
    roundWithAccuracy format mode sign mantissa exponent .exact

/-- Whether overflow in the given direction produces infinity. -/
def overflowToInfinity (mode : RoundingMode) (sign : Sign) : Bool :=
  match mode with
  | .nearestTiesToEven | .nearestTiesToAway => true
  | .towardZero => false
  | .towardPositive => sign == .positive
  | .towardNegative => sign == .negative

/-- Largest finite magnitude, with the requested sign. -/
def packedMaxFinite (format : Format) (sign : Sign) : BitVec format.numBits :=
  packComponents format sign (BitVec.ofNat _ (2 ^ format.exponentBits - 2)) (-1#_)

/-- Pack an already rounded significand, respecting directed overflow.
Infinities in the input remain infinities; saturation only applies to a finite
arithmetic result whose exponent exceeds the destination range. -/
def packNormalized (format : Format) (mode : RoundingMode) (value : UnpackedFloat) :
    BitVec format.numBits :=
  match value with
  | .finite sign _ exponent _ =>
    let biased := (exponent + format.exponentBias + format.mantissaBitsWithoutImplicit).toNat
    if 2 ^ format.exponentBits ≤ biased + 1 && !overflowToInfinity mode sign then
      packedMaxFinite format sign
    else value.pack format
  | _ => value.pack format

/-- Convert an exact unpacked value directly to a destination format, with
one rounding step. No intermediate binary32 conversion is introduced. -/
def packRounded (format : Format) (mode : RoundingMode) (value : UnpackedFloat) :
    BitVec format.numBits :=
  packNormalized format mode (roundUnpacked format mode value)

@[simp] theorem packRounded_zero (format : Format) (mode : RoundingMode) (sign : Sign) :
    packRounded format mode (.zero sign) = packedZero format sign := rfl

@[simp] theorem packRounded_infinity (format : Format) (mode : RoundingMode) (sign : Sign) :
    packRounded format mode (.infinity sign) = packedInfinity format sign := rfl

@[simp] theorem packRounded_notANumber (format : Format) (mode : RoundingMode) :
    packRounded format mode .notANumber = packedNaN format := rfl

/-- Exact signed dyadic construction, including an explicit sign for zero. -/
def ofDyadic (mantissa : Int) (exponent : Int) (zeroSign : Sign := .positive) : UnpackedFloat :=
  if h : mantissa.natAbs = 0 then .zero zeroSign
  else .finite (if mantissa < 0 then .negative else .positive)
    mantissa.natAbs exponent (Nat.pos_of_ne_zero h)

/-- Exact integer embedding; any destination rounding is performed separately. -/
def ofInt (value : Int) : UnpackedFloat := ofDyadic value 0

/-- Round to an unbounded integer. NaNs and infinities have no integer value.
Range checking for machine integer destinations must be applied afterwards. -/
def toInt? (mode : RoundingMode) : UnpackedFloat → Option Int
  | .notANumber | .infinity _ => none
  | .zero _ => some 0
  | .finite sign mantissa exponent _ =>
    if exponent ≥ 0 then some (sign.apply (mantissa <<< exponent.toNat))
    else
      let (extended, _) := shiftToExponent mantissa exponent .exact 0
      some (sign.apply (roundMantissa mode sign extended.mantissa extended.accuracy))

/-- Integer embedding is exact in every rounding direction before a bounded
destination format is selected. -/
@[simp] theorem toInt?_ofInt (mode : RoundingMode) (value : Int) :
    toInt? mode (ofInt value) = some value := by
  unfold ofInt ofDyadic
  split
  next h =>
    have : value = 0 := by omega
    subst value
    rfl
  next _ =>
    split
    next _ =>
      simp [toInt?, Sign.apply]
      omega
    next _ =>
      simp [toInt?, Sign.apply]
      omega

/-- IEEE's sign of an exact zero obtained by cancellation. -/
def cancellationSign (mode : RoundingMode) : Sign :=
  if mode == .towardNegative then .negative else .positive

/-- Exact addition with unbounded integer significands. No rounding or
destination overflow occurs here. -/
def addExact (mode : RoundingMode) : UnpackedFloat → UnpackedFloat → UnpackedFloat
  | .notANumber, _ | _, .notANumber => .notANumber
  | .infinity left, .infinity right =>
    if left == right then .infinity left else .notANumber
  | .infinity sign, _ | _, .infinity sign => .infinity sign
  | .zero left, .zero right =>
    .zero (if left == right then left else cancellationSign mode)
  | .zero _, value | value, .zero _ => value
  | .finite left lm le _, .finite right rm re _ =>
    let exponent := min le re
    let (lm, _) := decreaseExponent lm le exponent
    let (rm, _) := decreaseExponent rm re exponent
    ofDyadic (left.apply lm + right.apply rm) exponent (cancellationSign mode)

/-- Exact multiplication, including IEEE's invalid zero-times-infinity case. -/
def mulExact : UnpackedFloat → UnpackedFloat → UnpackedFloat
  | .notANumber, _ | _, .notANumber => .notANumber
  | .infinity _, .zero _ | .zero _, .infinity _ => .notANumber
  | .infinity left, .infinity right
  | .infinity left, .finite right ..
  | .finite left .., .infinity right => .infinity (left * right)
  | .zero left, .zero right
  | .zero left, .finite right ..
  | .finite left .., .zero right => .zero (left * right)
  | .finite left lm le lh, .finite right rm re rh =>
    .finite (left * right) (lm * rm) (le + re) (Nat.mul_pos lh rh)

/-- Addition with an explicit rounding direction. -/
def addRounded (format : Format) (mode : RoundingMode) (x y : UnpackedFloat) :
    BitVec format.numBits := packRounded format mode (addExact mode x y)

/-- Subtraction with an explicit rounding direction. -/
def subRounded (format : Format) (mode : RoundingMode) (x y : UnpackedFloat) :
    BitVec format.numBits := addRounded format mode x y.neg

/-- Multiplication with an explicit rounding direction. -/
def mulRounded (format : Format) (mode : RoundingMode) (x y : UnpackedFloat) :
    BitVec format.numBits := packRounded format mode (mulExact x y)

/-- Fused multiply-add: the exact product and exact sum are rounded only once,
even if the product lies outside the destination's finite or subnormal range. -/
def fmaRounded (format : Format) (mode : RoundingMode) (x y z : UnpackedFloat) :
    BitVec format.numBits := packRounded format mode (addExact mode (mulExact x y) z)

/-- Division with exact quotient residuals and one final rounding. -/
def divRounded (format : Format) (mode : RoundingMode) (x y : UnpackedFloat) :
    BitVec format.numBits :=
  let result := match x, y with
    | .finite left lm le _, .finite right rm re _ =>
      let (mantissa, exponent, accuracy) := divCore format lm le rm re
      roundWithAccuracy format mode (left / right) mantissa exponent accuracy
    | _, _ => UnpackedFloat.div format x y
  packNormalized format mode result

/-- Square root with exact integer-square-root residuals and one final rounding. -/
def sqrtRounded (format : Format) (mode : RoundingMode) (x : UnpackedFloat) :
    BitVec format.numBits :=
  let result := match x with
    | .finite .positive mantissa exponent _ =>
      let (mantissa, exponent, accuracy) := sqrtCore format mantissa exponent
      roundWithAccuracy format mode .positive mantissa exponent accuracy
    | _ => UnpackedFloat.sqrt format x
  packNormalized format mode result

/-- Round a finite value to an integral floating-point value, retaining the
source sign when the result is zero. Non-finite values are unchanged. -/
def integralRounded (format : Format) (mode : RoundingMode) (x : UnpackedFloat) :
    BitVec format.numBits :=
  match x with
  | .finite sign .. =>
    match toInt? mode x with
    | some value => packRounded format mode (ofDyadic value 0 sign)
    | none => packedNaN format
  | _ => packRounded format mode x

end Rounding

namespace F32

/-- Convert an arbitrary integer directly to binary32. -/
def ofInt (value : Int) (mode : RoundingMode := .nearestTiesToEven) : F32 :=
  ⟨UInt32.ofBitVec (Rounding.packRounded Format.binary32 mode (Rounding.ofInt value))⟩

/-- Convert to an unbounded integer, returning `none` on NaN or infinity. -/
def toInt? (x : F32) (mode : RoundingMode := .towardZero) : Option Int :=
  Rounding.toInt? mode x.model.unpack

def addWith (mode : RoundingMode) (x y : F32) : F32 :=
  ⟨UInt32.ofBitVec (Rounding.addRounded Format.binary32 mode x.model.unpack y.model.unpack)⟩
def subWith (mode : RoundingMode) (x y : F32) : F32 :=
  ⟨UInt32.ofBitVec (Rounding.subRounded Format.binary32 mode x.model.unpack y.model.unpack)⟩
def mulWith (mode : RoundingMode) (x y : F32) : F32 :=
  ⟨UInt32.ofBitVec (Rounding.mulRounded Format.binary32 mode x.model.unpack y.model.unpack)⟩
def divWith (mode : RoundingMode) (x y : F32) : F32 :=
  ⟨UInt32.ofBitVec (Rounding.divRounded Format.binary32 mode x.model.unpack y.model.unpack)⟩
def fmaWith (mode : RoundingMode) (x y z : F32) : F32 :=
  ⟨UInt32.ofBitVec (Rounding.fmaRounded Format.binary32 mode x.model.unpack y.model.unpack z.model.unpack)⟩
def sqrtWith (mode : RoundingMode) (x : F32) : F32 :=
  ⟨UInt32.ofBitVec (Rounding.sqrtRounded Format.binary32 mode x.model.unpack)⟩
def roundIntegral (mode : RoundingMode) (x : F32) : F32 :=
  ⟨UInt32.ofBitVec (Rounding.integralRounded Format.binary32 mode x.model.unpack)⟩

/-- Exact widening to binary64, canonicalizing NaN payloads. -/
def toF64 (x : F32) : F64 :=
  ⟨UInt64.ofBitVec (Rounding.packRounded Format.binary64 .nearestTiesToEven x.model.unpack)⟩

end F32

namespace F64

/-- Convert an arbitrary integer directly to binary64. -/
def ofInt (value : Int) (mode : RoundingMode := .nearestTiesToEven) : F64 :=
  ⟨UInt64.ofBitVec (Rounding.packRounded Format.binary64 mode (Rounding.ofInt value))⟩

/-- Convert to an unbounded integer, returning `none` on NaN or infinity. -/
def toInt? (x : F64) (mode : RoundingMode := .towardZero) : Option Int :=
  Rounding.toInt? mode x.model.unpack

def addWith (mode : RoundingMode) (x y : F64) : F64 :=
  ⟨UInt64.ofBitVec (Rounding.addRounded Format.binary64 mode x.model.unpack y.model.unpack)⟩
def subWith (mode : RoundingMode) (x y : F64) : F64 :=
  ⟨UInt64.ofBitVec (Rounding.subRounded Format.binary64 mode x.model.unpack y.model.unpack)⟩
def mulWith (mode : RoundingMode) (x y : F64) : F64 :=
  ⟨UInt64.ofBitVec (Rounding.mulRounded Format.binary64 mode x.model.unpack y.model.unpack)⟩
def divWith (mode : RoundingMode) (x y : F64) : F64 :=
  ⟨UInt64.ofBitVec (Rounding.divRounded Format.binary64 mode x.model.unpack y.model.unpack)⟩
def fmaWith (mode : RoundingMode) (x y z : F64) : F64 :=
  ⟨UInt64.ofBitVec (Rounding.fmaRounded Format.binary64 mode x.model.unpack y.model.unpack z.model.unpack)⟩
def sqrtWith (mode : RoundingMode) (x : F64) : F64 :=
  ⟨UInt64.ofBitVec (Rounding.sqrtRounded Format.binary64 mode x.model.unpack)⟩
def roundIntegral (mode : RoundingMode) (x : F64) : F64 :=
  ⟨UInt64.ofBitVec (Rounding.integralRounded Format.binary64 mode x.model.unpack)⟩

/-- Direct binary64-to-binary32 conversion with one rounding step. -/
def toF32 (x : F64) (mode : RoundingMode := .nearestTiesToEven) : F32 :=
  ⟨UInt32.ofBitVec (Rounding.packRounded Format.binary32 mode x.model.unpack)⟩

end F64

end Silmaril.Numeric.Ieee754
