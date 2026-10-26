module

public import Silmaril.Numeric.Integer
public import Silmaril.Numeric.Ieee754.Operations
public import Silmaril.Numeric.LowPrecision.Casts

/-!
# Floating-point scalars for typed kernel models

`Scalar format` provides a uniform, lossless storage type for tile elements.
`cast?` performs a single numeric conversion; `bitcast` preserves the bits.
`convert?` preserves identical formats and otherwise performs a numeric cast.
NaNs canonicalize under numeric conversion. By default IEEE destinations retain
IEEE overflow; E4M3FN, FNUZ, and E2M1 use finite saturation. The explicit
`saturateFinite` policy also clamps overflow for IEEE destinations. FP4 cannot represent a
NaN, so conversions and arithmetic that produce one return `none`.

`ArithmeticFormat` selects an IEEE-style computation precision independently
of storage. For example, FP8 tile elements can be widened to FP32 and accumulated
with `Arithmetic.fma`. Promotion, accumulation order, contraction, and block
scales belong to the kernel model and are explicit at its call sites.

Input and output flushing are separate switches because GPU instructions have
instruction-specific subnormal behavior. These operations implement ideal
rounded scalar results. Fast transcendental and tensor-core approximations
require their own backend contracts; see `Numeric.Approximation`.

Triton distinguishes precise `div_rn`/`sqrt_rn`, fast operations, and storage
casts: <https://triton-lang.org/main/python-api/triton.language.html>.
-/

@[expose] public section

namespace Silmaril.Numeric

open Ieee754 LowPrecision Float.Model

inductive FloatFormat where
  | f16 | bf16 | f32 | f64
  | f8 (format : F8Format)
  | f4 (format : F4Format)
  deriving DecidableEq, Repr

def FloatFormat.width : FloatFormat → Nat
  | .f16 | .bf16 => 16
  | .f32 => 32
  | .f64 => 64
  | .f8 _ => 8
  | .f4 _ => 4

def FloatFormat.spec : FloatFormat → FormatSpec
  | .f16 => binary16Spec
  | .bf16 => bfloat16Spec
  | .f32 => ⟨32, 8, 23, 127, .ieee⟩
  | .f64 => ⟨64, 11, 52, 1023, .ieee⟩
  | .f8 f => f.spec
  | .f4 f => f.spec

/-- The format index distinguishes equally-sized formats such as FP16/BF16. -/
structure Scalar (format : FloatFormat) where
  bits : BitVec format.width
  deriving DecidableEq, Repr

namespace Scalar

variable {format : FloatFormat}

@[ext] theorem ext {x y : Scalar format} (h : x.bits = y.bits) : x = y := by
  cases x; cases y; cases h; rfl

def ofBits (bits : BitVec format.width) : Scalar format := ⟨bits⟩
def toBits (x : Scalar format) : BitVec format.width := x.bits

@[simp] theorem ofBits_toBits (x : Scalar format) : ofBits x.toBits = x := rfl
@[simp] theorem toBits_ofBits (bits : BitVec format.width) : (ofBits bits).toBits = bits := rfl

/-- Reinterpret an equally wide format without changing any bits. -/
def bitcast (target : FloatFormat) (x : Scalar format)
    (h : format.width = target.width) : Scalar target := ⟨x.bits.cast h⟩

@[simp] theorem bitcast_roundtrip {target : FloatFormat}
    (h : format.width = target.width) (x : Scalar format) :
    (x.bitcast target h).bitcast format h.symm = x := by
  apply ext
  simp [bitcast]

/-- Reinterpret the raw bits as an equally wide integer, including NaN payloads. -/
def bitcastToInteger (target : IntFormat) (x : Scalar format)
    (h : format.width = target.width) : Integer target := ⟨x.bits.cast h⟩

/-- Reinterpret an equally wide integer as floating-point storage. -/
def bitcastFromInteger (target : FloatFormat) {source : IntFormat}
    (x : Integer source) (h : source.width = target.width) : Scalar target :=
  ⟨x.bits.cast h⟩

@[simp] theorem bitcastFromInteger_bitcastToInteger {target : IntFormat}
    (x : Scalar format) (h : format.width = target.width) :
    bitcastFromInteger format (x.bitcastToInteger target h) h.symm = x := by
  apply ext
  simp [bitcastFromInteger, bitcastToInteger]

@[simp] theorem bitcastToInteger_bitcastFromInteger {source : IntFormat}
    (x : Integer source) (h : source.width = format.width) :
    (bitcastFromInteger format x h).bitcastToInteger source h.symm = x := by
  cases x
  simp [bitcastFromInteger, bitcastToInteger]

def ofF32 (x : F32) : Scalar .f32 := ⟨x.bits.toBitVec⟩
def ofF64 (x : F64) : Scalar .f64 := ⟨x.bits.toBitVec⟩
def ofF16 (x : F16) : Scalar .f16 := ⟨x.bits.toBitVec⟩
def ofBF16 (x : BF16) : Scalar .bf16 := ⟨x.bits.toBitVec⟩
def ofF8 {f : F8Format} (x : F8 f) : Scalar (.f8 f) := ⟨x.bits.toBitVec⟩
def ofF4 {f : F4Format} (x : F4 f) : Scalar (.f4 f) := ⟨x.bits⟩

def asF32 (x : Scalar .f32) : F32 := ⟨UInt32.ofBitVec x.bits⟩
def asF64 (x : Scalar .f64) : F64 := ⟨UInt64.ofBitVec x.bits⟩
def asF16 (x : Scalar .f16) : F16 := ⟨UInt16.ofBitVec x.bits⟩
def asBF16 (x : Scalar .bf16) : BF16 := ⟨UInt16.ofBitVec x.bits⟩
def asF8 {f : F8Format} (x : Scalar (.f8 f)) : F8 f := ⟨UInt8.ofBitVec x.bits⟩
def asF4 {f : F4Format} (x : Scalar (.f4 f)) : F4 f := ⟨x.bits⟩

@[simp] theorem asF32_ofF32 (x : F32) : (ofF32 x).asF32 = x := rfl
@[simp] theorem asF64_ofF64 (x : F64) : (ofF64 x).asF64 = x := rfl
@[simp] theorem asF16_ofF16 (x : F16) : (ofF16 x).asF16 = x := rfl
@[simp] theorem asBF16_ofBF16 (x : BF16) : (ofBF16 x).asBF16 = x := rfl
@[simp] theorem asF8_ofF8 {f : F8Format} (x : F8 f) : (ofF8 x).asF8 = x := rfl
@[simp] theorem asF4_ofF4 {f : F4Format} (x : F4 f) : (ofF4 x).asF4 = x := rfl

def unpack (x : Scalar format) : UnpackedFloat := unpackBits format.spec x.bits.toNat
def toRat? (x : Scalar format) : Option ℚ := exactValue? format.spec x.bits.toNat

def classify (x : Scalar format) : LowPrecision.Class := classifyBits format.spec x.bits.toNat
def signBit (x : Scalar format) : Bool := LowPrecision.signBit format.spec x.bits.toNat
def isNaN (x : Scalar format) : Bool := x.classify == .nan
def isFinite (x : Scalar format) : Bool := x.classify != .nan && x.classify != .infinity

/-- Predicate conversion used by Triton `int1` casts: both zeros are false;
nonzero values, infinities, and NaNs are true. This differs from rounding to
the unsigned one-bit integer range. Triton lowers the conversion to unordered
inequality with zero:
<https://github.com/triton-lang/triton/blob/main/python/triton/language/semantic.py>. -/
def toBool (x : Scalar format) : Bool := x.classify != .zero

/-- Construct exactly positive zero or one in any supported storage format. -/
def ofBool (format : FloatFormat) (value : Bool) : Scalar format :=
  ⟨BitVec.ofNat _ (if value then format.spec.bias.toNat * 2 ^ format.spec.fractionBits else 0)⟩

@[simp] theorem toBool_ofBool (format : FloatFormat) (value : Bool) :
    (ofBool format value).toBool = value := by
  cases format <;> cases value <;> (try rename_i f; cases f) <;> decide +kernel

@[simp] theorem toRat?_ofBool (format : FloatFormat) (value : Bool) :
    (ofBool format value).toRat? = some (if value then 1 else 0) := by
  cases format <;> cases value <;> (try rename_i f; cases f) <;> decide +kernel

/-- Encode predicate conversion as the unsigned one-bit storage of a tile mask. -/
def toPredicate (x : Scalar format) : Integer .u1 := ⟨BitVec.ofBool x.toBool⟩

/-- Interpret a one-bit mask as exactly positive zero or one. -/
def ofPredicate (format : FloatFormat) (x : Integer .u1) : Scalar format :=
  ofBool format (x.bits.getLsbD 0)

@[simp] theorem toPredicate_ofPredicate (format : FloatFormat) (x : Integer .u1) :
    (ofPredicate format x).toPredicate = x := by
  cases x with
  | mk bits =>
    simp only [ofPredicate, toPredicate, toBool_ofBool]
    congr 1
    simpa using (BitVec.setWidth_one (x := bits)).symm

@[simp] theorem ofPredicate_toPredicate (x : Scalar format) :
    ofPredicate format x.toPredicate = ofBool format x.toBool := by
  simp [ofPredicate, toPredicate]

def ofUnpacked? (format : FloatFormat) (value : UnpackedFloat)
    (rounding : RoundingMode := .nearestTiesToEven)
    (overflow : OverflowPolicy := .formatDefault) : Option (Scalar format) :=
  (quantizeBitsWith? format.spec rounding overflow value).map (fun bits => ⟨BitVec.ofNat _ bits⟩)

/-- Direct numeric conversion between every supported pair of storage formats.
The overflow policy is independent of the destination encoding; numeric casts
canonicalize NaNs even when source and target formats coincide. -/
def cast? (target : FloatFormat) (x : Scalar format)
    (rounding : RoundingMode := .nearestTiesToEven)
    (overflow : OverflowPolicy := .formatDefault) : Option (Scalar target) :=
  ofUnpacked? target x.unpack rounding overflow

/-- A frontend conversion preserves all bits when its formats coincide;
otherwise it performs `cast?` with the selected rounding and overflow policy.
The identity case also preserves infinities under a saturation policy, since
no conversion instruction is applied. Triton uses this no-op rule:
<https://github.com/triton-lang/triton/blob/main/python/triton/language/semantic.py>. -/
def convert? (target : FloatFormat) (x : Scalar format)
    (rounding : RoundingMode := .nearestTiesToEven)
    (overflow : OverflowPolicy := .formatDefault) : Option (Scalar target) :=
  if h : format = target then some (h ▸ x) else x.cast? target rounding overflow

@[simp] theorem convert?_self (x : Scalar format) (rounding : RoundingMode)
    (overflow : OverflowPolicy) : convert? format x rounding overflow = some x := by
  simp [convert?]

theorem convert?_of_ne {target : FloatFormat} (h : format ≠ target)
    (x : Scalar format) (rounding : RoundingMode) (overflow : OverflowPolicy) :
    convert? target x rounding overflow = x.cast? target rounding overflow := by
  simp [convert?, h]

/-- Direct integer conversion, including signed/unsigned 4-, 8-, 16-, 32-, and 64-bit inputs. -/
def ofInteger? {source : IntFormat} (format : FloatFormat) (x : Integer source)
    (rounding : RoundingMode := .nearestTiesToEven)
    (overflow : OverflowPolicy := .formatDefault) : Option (Scalar format) :=
  ofUnpacked? format x.unpack rounding overflow

def ofInt? (format : FloatFormat) (x : Int)
    (rounding : RoundingMode := .nearestTiesToEven)
    (overflow : OverflowPolicy := .formatDefault) : Option (Scalar format) :=
  ofUnpacked? format (Rounding.ofInt x) rounding overflow

def toInteger? (target : IntFormat) (x : Scalar format)
    (rounding : RoundingMode := .towardZero) : Option (Integer target) :=
  Integer.fromFloat? target x.unpack rounding

def toIntegerSaturating (target : IntFormat) (x : Scalar format)
    (rounding : RoundingMode := .towardZero) : Integer target :=
  Integer.fromFloatSaturating target x.unpack rounding

/-- Exact numeric widening of every supported storage format to binary64. -/
def toF64 (x : Scalar format) : F64 :=
  ⟨UInt64.ofBitVec (Rounding.packRounded .binary64 .nearestTiesToEven x.unpack)⟩

/-- Ordered comparison: `none` means at least one operand is NaN. -/
def compare (x y : Scalar format) : Option Ordering := x.toF64.compare y.toF64

def equal (x y : Scalar format) : Bool := x.toF64.equal y.toF64

def lessThan (x y : Scalar format) : Bool := x.toF64.lessThan y.toF64

def lessEqual (x y : Scalar format) : Bool := x.toF64.lessEqual y.toF64

/-- Unordered inequality: a NaN operand makes the result true. -/
def notEqual (x y : Scalar format) : Bool := !x.equal y

def greaterThan (x y : Scalar format) : Bool := y.lessThan x

def greaterEqual (x y : Scalar format) : Bool := y.lessEqual x

/-- True exactly when a comparison has at least one NaN operand. -/
def unordered (x y : Scalar format) : Bool := x.isNaN || y.isNaN

def neg (x : Scalar format) : Scalar format :=
  ⟨BitVec.ofNat _ (negateBits format.spec x.bits.toNat)⟩

def abs (x : Scalar format) : Scalar format :=
  ⟨BitVec.ofNat _ (absBits format.spec x.bits.toNat)⟩

def copySign (x y : Scalar format) : Scalar format :=
  ⟨BitVec.ofNat _ (copySignBits format.spec x.bits.toNat y.bits.toNat)⟩

/-- Flush a subnormal to zero with its sign, respecting unsigned-zero formats. -/
def flushSubnormal (x : Scalar format) : Scalar format :=
  if x.classify == .subnormal then
    ⟨BitVec.ofNat _ (if x.signBit && format.spec.special != .fnuz then format.spec.signMask else 0)⟩
  else x

/-- Exact multiply/add before rounding to the storage format. Unsupported FP4
NaN results are explicit; finite-only formats use finite saturation. -/
def fma? (x y z : Scalar format) (mode : RoundingMode := .nearestTiesToEven) :
    Option (Scalar format) :=
  ofUnpacked? format (Rounding.addExact mode (Rounding.mulExact x.unpack y.unpack) z.unpack) mode

def add? (x y : Scalar format) (mode : RoundingMode := .nearestTiesToEven) :
    Option (Scalar format) := ofUnpacked? format (Rounding.addExact mode x.unpack y.unpack) mode

def sub? (x y : Scalar format) (mode : RoundingMode := .nearestTiesToEven) :
    Option (Scalar format) := add? x y.neg mode

def mul? (x y : Scalar format) (mode : RoundingMode := .nearestTiesToEven) :
    Option (Scalar format) := ofUnpacked? format (Rounding.mulExact x.unpack y.unpack) mode

end Scalar

/-- Computation precisions with IEEE encodings, independent of storage precision. -/
inductive ArithmeticFormat where
  | f16 | bf16 | f32 | f64
  deriving DecidableEq, Repr

def ArithmeticFormat.storage : ArithmeticFormat → FloatFormat
  | .f16 => .f16 | .bf16 => .bf16 | .f32 => .f32 | .f64 => .f64

def ArithmeticFormat.core : ArithmeticFormat → Float.Model.Format
  | .f16 => binary16CoreFormat
  | .bf16 => bfloat16CoreFormat
  | .f32 => .binary32
  | .f64 => .binary64

/-- Independent input/output subnormal handling for a selected instruction. -/
structure ArithmeticPolicy where
  rounding : RoundingMode := .nearestTiesToEven
  flushInputs : Bool := false
  flushOutput : Bool := false
  deriving DecidableEq, Repr

namespace Arithmetic

abbrev Value (format : ArithmeticFormat) := Scalar format.storage

def input {format : ArithmeticFormat} (policy : ArithmeticPolicy) (x : Value format) :
    UnpackedFloat := (if policy.flushInputs then x.flushSubnormal else x).unpack

def output (format : ArithmeticFormat) (policy : ArithmeticPolicy)
    (bits : BitVec format.core.numBits) : Value format :=
  let value : Value format := ⟨BitVec.ofNat _ bits.toNat⟩
  if policy.flushOutput then value.flushSubnormal else value

/-- Promote storage data directly to the chosen computation precision. -/
def convert (target : ArithmeticFormat) {source : FloatFormat} (x : Scalar source)
    (policy : ArithmeticPolicy := {}) : Value target :=
  output target policy (Rounding.packRounded target.core policy.rounding
    (if policy.flushInputs then x.flushSubnormal.unpack else x.unpack))

def add (format : ArithmeticFormat) (x y : Value format) (policy : ArithmeticPolicy := {}) : Value format :=
  output format policy (Rounding.addRounded format.core policy.rounding (input policy x) (input policy y))
def sub (format : ArithmeticFormat) (x y : Value format) (policy : ArithmeticPolicy := {}) : Value format :=
  output format policy (Rounding.subRounded format.core policy.rounding (input policy x) (input policy y))
def mul (format : ArithmeticFormat) (x y : Value format) (policy : ArithmeticPolicy := {}) : Value format :=
  output format policy (Rounding.mulRounded format.core policy.rounding (input policy x) (input policy y))
def div (format : ArithmeticFormat) (x y : Value format) (policy : ArithmeticPolicy := {}) : Value format :=
  output format policy (Rounding.divRounded format.core policy.rounding (input policy x) (input policy y))
def sqrt (format : ArithmeticFormat) (x : Value format) (policy : ArithmeticPolicy := {}) : Value format :=
  output format policy (Rounding.sqrtRounded format.core policy.rounding (input policy x))

/-- One final rounding in the accumulation precision; multiplication is exact. -/
def fma (format : ArithmeticFormat) (x y z : Value format) (policy : ArithmeticPolicy := {}) : Value format :=
  output format policy (Rounding.fmaRounded format.core policy.rounding
    (input policy x) (input policy y) (input policy z))

/-- Rounding to an integral floating-point value retains signed zero. -/
def roundIntegral (format : ArithmeticFormat) (mode : RoundingMode)
    (x : Value format) (policy : ArithmeticPolicy := {}) : Value format :=
  output format policy (Rounding.integralRounded format.core mode (input policy x))

/-- The canonical number-ignoring versus NaN-propagating choice is explicit. -/
inductive NaNPolicy where
  | propagate | ignoreSingle
  deriving DecidableEq, Repr

/-- Shared selection implementation; both inputs widen exactly to binary64. -/
def extremum (format : ArithmeticFormat) (minimum : Bool) (nan : NaNPolicy)
    (x y : Value format) (policy : ArithmeticPolicy) : Value format :=
  let left : F64 := ⟨UInt64.ofBitVec (Rounding.packRounded .binary64 .nearestTiesToEven (input policy x))⟩
  let right : F64 := ⟨UInt64.ofBitVec (Rounding.packRounded .binary64 .nearestTiesToEven (input policy y))⟩
  let selected := match minimum, nan with
    | true, .propagate => left.minimum right
    | false, .propagate => left.maximum right
    | true, .ignoreSingle => left.minimumNumber right
    | false, .ignoreSingle => left.maximumNumber right
  output format policy (Rounding.packRounded format.core policy.rounding selected.model.unpack)

/-- IEEE minimum with signed-zero ordering and a selected NaN policy. -/
def minimum (format : ArithmeticFormat) (x y : Value format)
    (nan : NaNPolicy := .propagate) (policy : ArithmeticPolicy := {}) : Value format :=
  extremum format true nan x y policy

/-- IEEE maximum with signed-zero ordering and a selected NaN policy. -/
def maximum (format : ArithmeticFormat) (x y : Value format)
    (nan : NaNPolicy := .propagate) (policy : ArithmeticPolicy := {}) : Value format :=
  extremum format false nan x y policy

/-- Clamp in the written order: minimum(maximum(x, lo), hi). -/
def clamp (format : ArithmeticFormat) (x lo hi : Value format)
    (nan : NaNPolicy := .propagate) (policy : ArithmeticPolicy := {}) : Value format :=
  minimum format (maximum format x lo nan policy) hi nan policy

/-- Reciprocal is a correctly rounded division of one by the operand. -/
def reciprocal (format : ArithmeticFormat) (x : Value format)
    (policy : ArithmeticPolicy := {}) : Value format :=
  let one := output format {} (Rounding.packRounded format.core .nearestTiesToEven (Rounding.ofInt 1))
  div format one x policy

/-- Scaling by a power of two is exact until the final destination rounding. -/
def scaleB (format : ArithmeticFormat) (x : Value format) (exponent : Int)
    (policy : ArithmeticPolicy := {}) : Value format :=
  let value := match input policy x with
    | .finite sign m e h => UnpackedFloat.finite sign m (e + exponent) h
    | other => other
  output format policy (Rounding.packRounded format.core policy.rounding value)

end Arithmetic
end Silmaril.Numeric
