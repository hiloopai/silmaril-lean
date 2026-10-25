module

public import Silmaril.Numeric.Ieee754.Rounding

/-!
# Scalar binary32 and binary64 operations

These operations supplement Lean's RNE arithmetic model with IEEE 754-2019
§5.3.1 remainder, integral rounding and adjacent values, §5.3.3 scaling, §5.5.1 sign operations, §5.11 comparisons, and §9.6 minimum/maximum.
`fmod` follows C/CUDA truncating-quotient semantics, whereas `remainder` uses
the IEEE nearest-even integer quotient. All results preserve gradual underflow.

`minimum`/`maximum` propagate NaNs; `minimumNumber`/`maximumNumber` prefer a
number over a NaN. Both order negative zero below positive zero. These separate
policies support Triton's `propagate_nan` option:
<https://triton-lang.org/main/python-api/generated/triton.language.minimum.html>.
Only result values are modeled; signaling exceptions are not tracked.

The refinement API offers total canonicalization and checked construction of
non-NaN and finite values. Arithmetic on non-NaNs can produce NaN (`0 / 0`),
and arithmetic on finite values can overflow, so those operations are checked.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754

open Float.Model (Format UnpackedFloat)
open Float.Model.UnpackedFloat (Sign)

/-- Round a nonnegative quotient to an integer using the requested direction
and the sign of the original value. `denominator` is positive at all call sites. -/
def roundQuotient (mode : RoundingMode) (sign : Sign)
    (numerator denominator : Nat) : Nat :=
  let q := numerator / denominator
  let r := numerator % denominator
  let increment : Bool := match mode with
    | .towardZero => false
    | .towardPositive => sign == .positive && r != 0
    | .towardNegative => sign == .negative && r != 0
    | .nearestTiesToEven => decide (2 * r > denominator) || (2 * r == denominator && q % 2 == 1)
    | .nearestTiesToAway => decide (2 * r ≥ denominator)
  if increment then q + 1 else q

/-- Compute a remainder with an exact integer quotient, avoiding rounded
floating division. `nearest = true` selects IEEE remainder; `false` selects fmod. -/
def remainderCore (spec : Format) (nearest : Bool) :
    UnpackedFloat → UnpackedFloat → UnpackedFloat
  | .notANumber, _ | _, .notANumber => .notANumber
  | .infinity _, _ | _, .zero _ => .notANumber
  | x, .infinity _ => x
  | .zero s, _ => .zero s
  | .finite sx mx ex _, .finite _ my ey _ =>
    let e := min ex ey
    let nx := mx * 2 ^ (ex - e).toNat
    let ny := my * 2 ^ (ey - e).toNat
    let q := roundQuotient (if nearest then .nearestTiesToEven else .towardZero)
      .positive nx ny
    let r : Int := (nx : Int) - (q : Int) * (ny : Int)
    UnpackedFloat.normalize spec (if sx == .negative then -r else r) e sx

/-- Exact multiplication by an integral power of two, followed by one RNE rounding. -/
def scaleBCore (spec : Format) (exponent : Int) : UnpackedFloat → UnpackedFloat
  | .finite s m e _ => UnpackedFloat.round spec s m (e + exponent)
  | x => x

namespace F32

/-- Positive zero. -/
def zero : F32 := ofBits 0
/-- Negative zero. -/
def negativeZero : F32 := ofBits 0x80000000
/-- The exactly represented number one. -/
def one : F32 := ofBits 0x3f800000
/-- Positive infinity. -/
def infinity : F32 := ofBits 0x7f800000
/-- Largest positive finite value. -/
def maxFinite : F32 := ofBits 0x7f7fffff
/-- Smallest positive normal value. -/
def minNormal : F32 := ofBits 0x00800000
/-- Smallest positive subnormal value. -/
def minSubnormal : F32 := ofBits 1

instance : Zero F32 := ⟨zero⟩
instance : One F32 := ⟨one⟩
instance : Inhabited F32 := ⟨zero⟩

/-- Raw interchange sign, including NaNs and signed zeros. -/
def signBit (x : F32) : Bool := (x.bits &&& 0x80000000) != 0
/-- The IEEE encoding class. -/
def classification (x : F32) : Class := classify32 x.bits.toNat
/-- Test for a NaN without changing its payload. -/
def isNaN (x : F32) : Bool := decide x.IsNaN
/-- A signaling NaN has a nonzero payload and a clear quiet bit (IEEE §6.2.1). -/
def isSignalingNaN (x : F32) : Bool := x.isNaN && (x.bits &&& 0x00400000) == 0
/-- A quiet NaN has its most significant trailing-significand bit set. -/
def isQuietNaN (x : F32) : Bool := x.isNaN && (x.bits &&& 0x00400000) != 0
/-- Test for finiteness using the exponent field. -/
def isFinite (x : F32) : Bool := decide x.IsFinite
/-- Test for either infinity. -/
def isInfinite (x : F32) : Bool := x.classification == .infinity
/-- Test for either zero. -/
def isZero (x : F32) : Bool := x.classification == .zero
/-- Test for a subnormal. -/
def isSubnormal (x : F32) : Bool := x.classification == .subnormal
/-- Test for a normal finite value. -/
def isNormal (x : F32) : Bool := x.classification == .normal

/-- IEEE comparison: NaN is unordered and the two zeros compare equal. -/
def compare (x y : F32) : Option Ordering := Float32.Model.compare x.model y.model
/-- IEEE ordered less-than-or-equal. -/
def lessEqual (x y : F32) : Bool := Float32.Model.le x.model y.model
/-- IEEE ordered greater-than. -/
def greaterThan (x y : F32) : Bool := lessThan y x
/-- IEEE ordered greater-than-or-equal. -/
def greaterEqual (x y : F32) : Bool := lessEqual y x
/-- Unordered comparison: true exactly when either operand is NaN. -/
def unordered (x y : F32) : Bool := x.isNaN || y.isNaN
/-- C/Triton inequality: true for an unordered comparison. -/
def notEqual (x y : F32) : Bool := !equal x y

/-- IEEE 754 §5.10 total ordering of interchange encodings. It distinguishes
zero signs and orders NaNs by sign, quiet/signaling status, and payload. -/
def totalOrder (x y : F32) : Bool :=
  let kx := if x.signBit then ~~~x.bits else x.bits ^^^ 0x80000000
  let ky := if y.signBit then ~~~y.bits else y.bits ^^^ 0x80000000
  decide (kx ≤ ky)

/-- NaN-propagating minimum with `minimum (-0) (+0) = -0`. -/
def minimum (x y : F32) : F32 :=
  if x.isNaN || y.isNaN then canonicalNaN
  else if equal x y then if x.signBit then x else y
  else if lessThan x y then x else y

/-- NaN-propagating maximum with `maximum (-0) (+0) = +0`. -/
def maximum (x y : F32) : F32 :=
  if x.isNaN || y.isNaN then canonicalNaN
  else if equal x y then if x.signBit then y else x
  else if lessThan x y then y else x

/-- Minimum preferring a numeric operand to a NaN, including a signaling NaN.
Exception flags are outside this value-only model. -/
def minimumNumber (x y : F32) : F32 :=
  if x.isNaN then if y.isNaN then canonicalNaN else y
  else if y.isNaN then x else minimum x y

/-- Maximum preferring a numeric operand to a NaN. -/
def maximumNumber (x y : F32) : F32 :=
  if x.isNaN then if y.isNaN then canonicalNaN else y
  else if y.isNaN then x else maximum x y

/-- Round to an integral value toward positive infinity. -/
def ceil := roundIntegral .towardPositive
/-- Round to an integral value toward negative infinity. -/
def floor := roundIntegral .towardNegative
/-- Round to an integral value toward zero. -/
def trunc := roundIntegral .towardZero
/-- Round to the nearest integral value, ties to even (WebAssembly `nearest`). -/
def nearest := roundIntegral .nearestTiesToEven

/-- C/CUDA fmod: exact `x - trunc(x/y) * y`, with zero carrying the sign of `x`. -/
def fmod (x y : F32) : F32 :=
  ofModel (Float32.Model.pack (remainderCore Format.binary32 false x.model.unpack y.model.unpack))

/-- IEEE 754 remainder: the integer quotient is rounded to nearest, ties to even. -/
def remainder (x y : F32) : F32 :=
  ofModel (Float32.Model.pack (remainderCore Format.binary32 true x.model.unpack y.model.unpack))

/-- Multiply by `2 ^ exponent`, using one final RNE rounding. -/
def scaleB (x : F32) (exponent : Int) : F32 :=
  ofModel (Float32.Model.pack (scaleBCore Format.binary32 exponent x.model.unpack))

/-- Rounded reciprocal. This is exact division followed by RNE, not an approximate GPU intrinsic. -/
def reciprocal (x : F32) : F32 := div one x

/-- Compose RNE square root and reciprocal. This has two rounding steps;
it does not model a hardware approximate reciprocal-square-root instruction. -/
def reciprocalSqrt (x : F32) : F32 := reciprocal (sqrt x)

/-- Adjacent representable value toward positive infinity. -/
def nextUp (x : F32) : F32 :=
  if x.isNaN then canonicalNaN
  else if x = infinity then x
  else if x.isZero then minSubnormal
  else if x.signBit then ofBits (x.bits - 1) else ofBits (x.bits + 1)

/-- Adjacent representable value toward negative infinity. -/
def nextDown (x : F32) : F32 :=
  if x.isNaN then canonicalNaN else neg (nextUp (neg x))

/-- NaN classes permitted by WebAssembly's minimum. -/
abbrev minimumRel := binaryResult minimum
/-- NaN classes permitted by WebAssembly's maximum. -/
abbrev maximumRel := binaryResult maximum
/-- Permitted NaN results of integral rounding. -/
abbrev roundIntegralRel (mode : RoundingMode) := unaryResult (roundIntegral mode)

/-- The chosen deterministic NaN has a canonical payload. -/
@[simp] theorem canonicalNaN_isCanonical : canonicalNaN.IsCanonicalNaN := by decide

/-- Replace noncanonical NaN payloads while preserving canonical NaN signs
and every non-NaN encoding, including zero signs. -/
def canonicalize (x : F32) : Canonicalized :=
  if h : x.IsNonNaNOrCanonicalNaN then ⟨x, h⟩
  else ⟨canonicalNaN, Or.inr canonicalNaN_isCanonical⟩

@[simp] theorem canonicalize_of_canonical (x : F32) (h : x.IsNonNaNOrCanonicalNaN) :
    (canonicalize x).val = x := by simp [canonicalize, h]

@[simp] theorem canonicalize_of_not_nan (x : F32) (h : ¬x.IsNaN) :
    (canonicalize x).val = x := canonicalize_of_canonical x (Or.inl h)

namespace Canonicalized

/-- Checked constructor preserving a canonical NaN's existing sign. -/
def ofRaw? (x : F32) : Option Canonicalized :=
  if h : x.IsNonNaNOrCanonicalNaN then some ⟨x, h⟩ else none

/-- Apply a raw unary operator and canonicalize its result. -/
def map (op : F32 → F32) (x : Canonicalized) : Canonicalized := canonicalize (op x.val)
/-- Apply a raw binary operator and canonicalize its result. -/
def map₂ (op : F32 → F32 → F32) (x y : Canonicalized) : Canonicalized :=
  canonicalize (op x.val y.val)

instance : Add Canonicalized := ⟨map₂ F32.add⟩
instance : Sub Canonicalized := ⟨map₂ F32.sub⟩
instance : Mul Canonicalized := ⟨map₂ F32.mul⟩
instance : Div Canonicalized := ⟨map₂ F32.div⟩
instance : Neg Canonicalized := ⟨map F32.neg⟩

/-- Canonicalized square root. -/
def sqrt := map F32.sqrt
/-- Canonicalized single-rounding fused multiply-add. -/
def fma (x y z : Canonicalized) : Canonicalized := canonicalize (F32.fma x.val y.val z.val)

end Canonicalized

namespace NonNaN

/-- Check the refinement without changing any bits. -/
def ofRaw? (x : F32) : Option NonNaN :=
  if h : ¬x.IsNaN then some ⟨x, h⟩ else none

/-- Apply a unary operation, returning `none` when the refinement fails. -/
def map? (op : F32 → F32) (x : NonNaN) : Option NonNaN := ofRaw? (op x.val)
/-- Apply a binary operation, returning `none` when the refinement fails. -/
def map₂? (op : F32 → F32 → F32) (x y : NonNaN) : Option NonNaN :=
  ofRaw? (op x.val y.val)

/-- Checked add. -/
def add? := map₂? F32.add

/-- Checked sub. -/
def sub? := map₂? F32.sub

/-- Checked mul. -/
def mul? := map₂? F32.mul

/-- Checked div. -/
def div? := map₂? F32.div

/-- Checked minimum. -/
def minimum? := map₂? F32.minimum

/-- Checked maximum. -/
def maximum? := map₂? F32.maximum

/-- Checked neg. -/
def neg? := map? F32.neg

/-- Checked abs. -/
def abs? := map? F32.abs

/-- Checked sqrt. -/
def sqrt? := map? F32.sqrt

/-- Checked single-rounding FMA. -/
def fma? (x y z : NonNaN) : Option NonNaN := ofRaw? (F32.fma x.val y.val z.val)

@[simp] theorem ofRaw?_val (x : NonNaN) : ofRaw? x.val = some x := by
  simp [ofRaw?, x.property]

end NonNaN

namespace Finite

/-- Check the refinement without changing any bits. -/
def ofRaw? (x : F32) : Option Finite :=
  if h : x.IsFinite then some ⟨x, h⟩ else none

/-- Apply a unary operation, returning `none` when the refinement fails. -/
def map? (op : F32 → F32) (x : Finite) : Option Finite := ofRaw? (op x.val)
/-- Apply a binary operation, returning `none` when the refinement fails. -/
def map₂? (op : F32 → F32 → F32) (x y : Finite) : Option Finite :=
  ofRaw? (op x.val y.val)

/-- Checked add. -/
def add? := map₂? F32.add

/-- Checked sub. -/
def sub? := map₂? F32.sub

/-- Checked mul. -/
def mul? := map₂? F32.mul

/-- Checked div. -/
def div? := map₂? F32.div

/-- Checked minimum. -/
def minimum? := map₂? F32.minimum

/-- Checked maximum. -/
def maximum? := map₂? F32.maximum

/-- Checked neg. -/
def neg? := map? F32.neg

/-- Checked abs. -/
def abs? := map? F32.abs

/-- Checked sqrt. -/
def sqrt? := map? F32.sqrt

/-- Checked single-rounding FMA. -/
def fma? (x y z : Finite) : Option Finite := ofRaw? (F32.fma x.val y.val z.val)

@[simp] theorem ofRaw?_val (x : Finite) : ofRaw? x.val = some x := by
  simp [ofRaw?, x.property]

end Finite

end F32

namespace F64

/-- Positive zero. -/
def zero : F64 := ofBits 0
/-- Negative zero. -/
def negativeZero : F64 := ofBits 0x8000000000000000
/-- The exactly represented number one. -/
def one : F64 := ofBits 0x3ff0000000000000
/-- Positive infinity. -/
def infinity : F64 := ofBits 0x7ff0000000000000
/-- Largest positive finite value. -/
def maxFinite : F64 := ofBits 0x7fefffffffffffff
/-- Smallest positive normal value. -/
def minNormal : F64 := ofBits 0x0010000000000000
/-- Smallest positive subnormal value. -/
def minSubnormal : F64 := ofBits 1

instance : Zero F64 := ⟨zero⟩
instance : One F64 := ⟨one⟩
instance : Inhabited F64 := ⟨zero⟩

/-- Raw interchange sign, including NaNs and signed zeros. -/
def signBit (x : F64) : Bool := (x.bits &&& 0x8000000000000000) != 0
/-- The IEEE encoding class. -/
def classification (x : F64) : Class := classify64 x.bits.toNat
/-- Test for a NaN without changing its payload. -/
def isNaN (x : F64) : Bool := decide x.IsNaN
/-- A signaling NaN has a nonzero payload and a clear quiet bit (IEEE §6.2.1). -/
def isSignalingNaN (x : F64) : Bool := x.isNaN && (x.bits &&& 0x0008000000000000) == 0
/-- A quiet NaN has its most significant trailing-significand bit set. -/
def isQuietNaN (x : F64) : Bool := x.isNaN && (x.bits &&& 0x0008000000000000) != 0
/-- Test for finiteness using the exponent field. -/
def isFinite (x : F64) : Bool := decide x.IsFinite
/-- Test for either infinity. -/
def isInfinite (x : F64) : Bool := x.classification == .infinity
/-- Test for either zero. -/
def isZero (x : F64) : Bool := x.classification == .zero
/-- Test for a subnormal. -/
def isSubnormal (x : F64) : Bool := x.classification == .subnormal
/-- Test for a normal finite value. -/
def isNormal (x : F64) : Bool := x.classification == .normal

/-- IEEE comparison: NaN is unordered and the two zeros compare equal. -/
def compare (x y : F64) : Option Ordering := Float.Model.compare x.model y.model
/-- IEEE ordered less-than-or-equal. -/
def lessEqual (x y : F64) : Bool := Float.Model.le x.model y.model
/-- IEEE ordered greater-than. -/
def greaterThan (x y : F64) : Bool := lessThan y x
/-- IEEE ordered greater-than-or-equal. -/
def greaterEqual (x y : F64) : Bool := lessEqual y x
/-- Unordered comparison: true exactly when either operand is NaN. -/
def unordered (x y : F64) : Bool := x.isNaN || y.isNaN
/-- C/Triton inequality: true for an unordered comparison. -/
def notEqual (x y : F64) : Bool := !equal x y

/-- IEEE 754 §5.10 total ordering of interchange encodings. It distinguishes
zero signs and orders NaNs by sign, quiet/signaling status, and payload. -/
def totalOrder (x y : F64) : Bool :=
  let kx := if x.signBit then ~~~x.bits else x.bits ^^^ 0x8000000000000000
  let ky := if y.signBit then ~~~y.bits else y.bits ^^^ 0x8000000000000000
  decide (kx ≤ ky)

/-- NaN-propagating minimum with `minimum (-0) (+0) = -0`. -/
def minimum (x y : F64) : F64 :=
  if x.isNaN || y.isNaN then canonicalNaN
  else if equal x y then if x.signBit then x else y
  else if lessThan x y then x else y

/-- NaN-propagating maximum with `maximum (-0) (+0) = +0`. -/
def maximum (x y : F64) : F64 :=
  if x.isNaN || y.isNaN then canonicalNaN
  else if equal x y then if x.signBit then y else x
  else if lessThan x y then y else x

/-- Minimum preferring a numeric operand to a NaN, including a signaling NaN.
Exception flags are outside this value-only model. -/
def minimumNumber (x y : F64) : F64 :=
  if x.isNaN then if y.isNaN then canonicalNaN else y
  else if y.isNaN then x else minimum x y

/-- Maximum preferring a numeric operand to a NaN. -/
def maximumNumber (x y : F64) : F64 :=
  if x.isNaN then if y.isNaN then canonicalNaN else y
  else if y.isNaN then x else maximum x y

/-- Round to an integral value toward positive infinity. -/
def ceil := roundIntegral .towardPositive
/-- Round to an integral value toward negative infinity. -/
def floor := roundIntegral .towardNegative
/-- Round to an integral value toward zero. -/
def trunc := roundIntegral .towardZero
/-- Round to the nearest integral value, ties to even (WebAssembly `nearest`). -/
def nearest := roundIntegral .nearestTiesToEven

/-- C/CUDA fmod: exact `x - trunc(x/y) * y`, with zero carrying the sign of `x`. -/
def fmod (x y : F64) : F64 :=
  ofModel (Float.Model.pack (remainderCore Format.binary64 false x.model.unpack y.model.unpack))

/-- IEEE 754 remainder: the integer quotient is rounded to nearest, ties to even. -/
def remainder (x y : F64) : F64 :=
  ofModel (Float.Model.pack (remainderCore Format.binary64 true x.model.unpack y.model.unpack))

/-- Multiply by `2 ^ exponent`, using one final RNE rounding. -/
def scaleB (x : F64) (exponent : Int) : F64 :=
  ofModel (Float.Model.pack (scaleBCore Format.binary64 exponent x.model.unpack))

/-- Rounded reciprocal. This is exact division followed by RNE, not an approximate GPU intrinsic. -/
def reciprocal (x : F64) : F64 := div one x

/-- Compose RNE square root and reciprocal. This has two rounding steps;
it does not model a hardware approximate reciprocal-square-root instruction. -/
def reciprocalSqrt (x : F64) : F64 := reciprocal (sqrt x)

/-- Adjacent representable value toward positive infinity. -/
def nextUp (x : F64) : F64 :=
  if x.isNaN then canonicalNaN
  else if x = infinity then x
  else if x.isZero then minSubnormal
  else if x.signBit then ofBits (x.bits - 1) else ofBits (x.bits + 1)

/-- Adjacent representable value toward negative infinity. -/
def nextDown (x : F64) : F64 :=
  if x.isNaN then canonicalNaN else neg (nextUp (neg x))

/-- NaN classes permitted by WebAssembly's minimum. -/
abbrev minimumRel := binaryResult minimum
/-- NaN classes permitted by WebAssembly's maximum. -/
abbrev maximumRel := binaryResult maximum
/-- Permitted NaN results of integral rounding. -/
abbrev roundIntegralRel (mode : RoundingMode) := unaryResult (roundIntegral mode)

/-- The chosen deterministic NaN has a canonical payload. -/
@[simp] theorem canonicalNaN_isCanonical : canonicalNaN.IsCanonicalNaN := by decide

/-- Replace noncanonical NaN payloads while preserving canonical NaN signs
and every non-NaN encoding, including zero signs. -/
def canonicalize (x : F64) : Canonicalized :=
  if h : x.IsNonNaNOrCanonicalNaN then ⟨x, h⟩
  else ⟨canonicalNaN, Or.inr canonicalNaN_isCanonical⟩

@[simp] theorem canonicalize_of_canonical (x : F64) (h : x.IsNonNaNOrCanonicalNaN) :
    (canonicalize x).val = x := by simp [canonicalize, h]

@[simp] theorem canonicalize_of_not_nan (x : F64) (h : ¬x.IsNaN) :
    (canonicalize x).val = x := canonicalize_of_canonical x (Or.inl h)

namespace Canonicalized

/-- Checked constructor preserving a canonical NaN's existing sign. -/
def ofRaw? (x : F64) : Option Canonicalized :=
  if h : x.IsNonNaNOrCanonicalNaN then some ⟨x, h⟩ else none

/-- Apply a raw unary operator and canonicalize its result. -/
def map (op : F64 → F64) (x : Canonicalized) : Canonicalized := canonicalize (op x.val)
/-- Apply a raw binary operator and canonicalize its result. -/
def map₂ (op : F64 → F64 → F64) (x y : Canonicalized) : Canonicalized :=
  canonicalize (op x.val y.val)

instance : Add Canonicalized := ⟨map₂ F64.add⟩
instance : Sub Canonicalized := ⟨map₂ F64.sub⟩
instance : Mul Canonicalized := ⟨map₂ F64.mul⟩
instance : Div Canonicalized := ⟨map₂ F64.div⟩
instance : Neg Canonicalized := ⟨map F64.neg⟩

/-- Canonicalized square root. -/
def sqrt := map F64.sqrt
/-- Canonicalized single-rounding fused multiply-add. -/
def fma (x y z : Canonicalized) : Canonicalized := canonicalize (F64.fma x.val y.val z.val)

end Canonicalized

namespace NonNaN

/-- Check the refinement without changing any bits. -/
def ofRaw? (x : F64) : Option NonNaN :=
  if h : ¬x.IsNaN then some ⟨x, h⟩ else none

/-- Apply a unary operation, returning `none` when the refinement fails. -/
def map? (op : F64 → F64) (x : NonNaN) : Option NonNaN := ofRaw? (op x.val)
/-- Apply a binary operation, returning `none` when the refinement fails. -/
def map₂? (op : F64 → F64 → F64) (x y : NonNaN) : Option NonNaN :=
  ofRaw? (op x.val y.val)

/-- Checked add. -/
def add? := map₂? F64.add

/-- Checked sub. -/
def sub? := map₂? F64.sub

/-- Checked mul. -/
def mul? := map₂? F64.mul

/-- Checked div. -/
def div? := map₂? F64.div

/-- Checked minimum. -/
def minimum? := map₂? F64.minimum

/-- Checked maximum. -/
def maximum? := map₂? F64.maximum

/-- Checked neg. -/
def neg? := map? F64.neg

/-- Checked abs. -/
def abs? := map? F64.abs

/-- Checked sqrt. -/
def sqrt? := map? F64.sqrt

/-- Checked single-rounding FMA. -/
def fma? (x y z : NonNaN) : Option NonNaN := ofRaw? (F64.fma x.val y.val z.val)

@[simp] theorem ofRaw?_val (x : NonNaN) : ofRaw? x.val = some x := by
  simp [ofRaw?, x.property]

end NonNaN

namespace Finite

/-- Check the refinement without changing any bits. -/
def ofRaw? (x : F64) : Option Finite :=
  if h : x.IsFinite then some ⟨x, h⟩ else none

/-- Apply a unary operation, returning `none` when the refinement fails. -/
def map? (op : F64 → F64) (x : Finite) : Option Finite := ofRaw? (op x.val)
/-- Apply a binary operation, returning `none` when the refinement fails. -/
def map₂? (op : F64 → F64 → F64) (x y : Finite) : Option Finite :=
  ofRaw? (op x.val y.val)

/-- Checked add. -/
def add? := map₂? F64.add

/-- Checked sub. -/
def sub? := map₂? F64.sub

/-- Checked mul. -/
def mul? := map₂? F64.mul

/-- Checked div. -/
def div? := map₂? F64.div

/-- Checked minimum. -/
def minimum? := map₂? F64.minimum

/-- Checked maximum. -/
def maximum? := map₂? F64.maximum

/-- Checked neg. -/
def neg? := map? F64.neg

/-- Checked abs. -/
def abs? := map? F64.abs

/-- Checked sqrt. -/
def sqrt? := map? F64.sqrt

/-- Checked single-rounding FMA. -/
def fma? (x y z : Finite) : Option Finite := ofRaw? (F64.fma x.val y.val z.val)

@[simp] theorem ofRaw?_val (x : Finite) : ofRaw? x.val = some x := by
  simp [ofRaw?, x.property]

end Finite

end F64

end Silmaril.Numeric.Ieee754
