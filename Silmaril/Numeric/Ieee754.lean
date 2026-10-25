module

public import Mathlib.Data.Rat.Defs
public import Init.Data.Float.Model.Float32

/-!
# IEEE 754 binary32 and binary64 arithmetic

This module defines lossless wrappers for IEEE 754 binary32 and binary64
encodings, together with their exact finite rational interpretation and
rounded arithmetic. These definitions model results under round-to-nearest,
ties-to-even with gradual underflow. They do not model exception flags, traps,
or a mutable rounding environment. The other `RoundingMode` constructors
are descriptors for APIs that explicitly accept them, not implicit modes
for `add`, `mul`, or `fma`. Lean's built-in `Float32.Model` and `Float.Model` provide
core encoding and round-to-nearest-even arithmetic definitions. They
canonicalize NaN payloads and expose no directed rounding modes, so this module
keeps lossless raw wrappers and formalizes WebAssembly's allowed NaN results
separately.

The field layouts, exponent biases, and interpretation rules below follow
IEEE Std 754-2019 §3.3 (formats), §3.4 (binary interchange encodings), and
§6.2 (NaNs). The parameter values for binary32 and binary64 are given in
§3.3, Table 3.2 and §3.6, Table 3.5. The standard is available from
<https://standards.ieee.org/ieee/754/6210/> (access may require a subscription).

WebAssembly Core 3.0 §4.3.3 requires round-to-nearest, ties-to-even for
arithmetic instructions. It specifies add, subtract, multiply, divide,
square root, min, max, copysign, and the integer rounding operations ceil,
floor, trunc, and nearest. See
<https://www.w3.org/TR/wasm-core/#floating-point-operations>.

For an exponent field `E` strictly between zero and all ones, the value is
`(-1)^S * (1 + T / 2^t) * 2^(E - bias)`. For `E = 0` and nonzero `T`, it is
`(-1)^S * (T / 2^t) * 2^(1 - bias)`. An all-ones exponent with zero trailing
significand denotes infinity; a zero exponent and zero trailing significand
denote signed zero. An all-ones exponent
with nonzero trailing significand denotes a NaN. Signed zeros and NaN payload
bits are preserved by representing the interchange datum as its raw bits.

`=` and `==` compare encodings (including zero signs and NaN payloads);
`F32.equal` and `F64.equal` implement IEEE numeric equality.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754

/-- IEEE 754 rounding directions. WebAssembly arithmetic uses
`nearestTiesToEven` (Core 3.0 §4.3.3.1). -/
inductive RoundingMode where
  | nearestTiesToEven
  | towardZero
  | towardPositive
  | towardNegative
  | nearestTiesToAway
  deriving DecidableEq, Repr

/-- A binary32 value, represented by its exact 32 interchange bits. -/
structure F32 where
  bits : UInt32
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

/-- A binary64 value, represented by its exact 64 interchange bits. -/
structure F64 where
  bits : UInt64
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

namespace F32

/-- Construct from an IEEE binary32 interchange bit pattern. -/
def ofBits (bits : UInt32) : F32 := ⟨bits⟩

/-- Return the unchanged interchange bit pattern. -/
def toBits (x : F32) : UInt32 := x.bits

/-- Lean's proof-oriented binary32 model. The model canonicalizes
NaN payloads, so this view is intended for arithmetic, while `bits` remains
the lossless interchange representation. -/
def model (x : F32) : Float32.Model := Float32.Model.ofBits x.bits

/-- Pack a modeled result back into the wrapper. Arithmetic results use the
model's canonical NaN encoding, as permitted by WebAssembly. -/
def ofModel (x : Float32.Model) : F32 := ⟨x.toBits⟩

/-- IEEE round-to-nearest, ties-to-even addition. -/
def add (x y : F32) : F32 := ofModel (x.model + y.model)

/-- IEEE round-to-nearest, ties-to-even subtraction. -/
def sub (x y : F32) : F32 := ofModel (x.model - y.model)

/-- IEEE round-to-nearest, ties-to-even multiplication. -/
def mul (x y : F32) : F32 := ofModel (x.model * y.model)

/-- IEEE round-to-nearest, ties-to-even division. -/
def div (x y : F32) : F32 := ofModel (x.model / y.model)

/-- IEEE round-to-nearest, ties-to-even square root. -/
def sqrt (x : F32) : F32 := ofModel (Float32.Model.sqrt x.model)

/-- Fused multiply-add with a single final rounding, as required by
IEEE 754-2019 §5.4.1: the exact product and sum are rounded once to the
destination format. Lean's model keeps the significand arithmetic exact until
its final normalization. -/
def fma (x y z : F32) : F32 := ofModel (Float32.Model.fma x.model y.model z.model)

/-- Change sign without changing the magnitude bits. -/
def neg (x : F32) : F32 := ⟨x.bits ^^^ 0x80000000⟩

/-- Clear the sign bit without changing the remaining bits. -/
def abs (x : F32) : F32 := ⟨x.bits &&& 0x7fffffff⟩

/-- Copy the sign bit of `y` onto the magnitude of `x`. -/
def copySign (x y : F32) : F32 :=
  ⟨(x.bits &&& 0x7fffffff) ||| (y.bits &&& 0x80000000)⟩

/-- IEEE numeric equality: NaNs are unequal and the two zeros compare equal. -/
def equal (x y : F32) : Bool := x.model == y.model

/-- IEEE unordered-aware less-than. -/
def lessThan (x y : F32) : Bool := decide (x.model < y.model)

instance : Add F32 := ⟨add⟩
instance : Sub F32 := ⟨sub⟩
instance : Mul F32 := ⟨mul⟩
instance : Div F32 := ⟨div⟩
instance : Neg F32 := ⟨neg⟩

end F32

namespace F64

/-- Construct from an IEEE binary64 interchange bit pattern. -/
def ofBits (bits : UInt64) : F64 := ⟨bits⟩

/-- Return the unchanged interchange bit pattern. -/
def toBits (x : F64) : UInt64 := x.bits

/-- Lean's proof-oriented binary64 model. The model canonicalizes
NaN payloads; `bits` itself remains lossless. -/
def model (x : F64) : Float.Model := Float.Model.ofBits x.bits

/-- Pack a modeled result back into the wrapper. -/
def ofModel (x : Float.Model) : F64 := ⟨x.toBits⟩

/-- IEEE round-to-nearest, ties-to-even addition. -/
def add (x y : F64) : F64 := ofModel (x.model + y.model)

/-- IEEE round-to-nearest, ties-to-even subtraction. -/
def sub (x y : F64) : F64 := ofModel (x.model - y.model)

/-- IEEE round-to-nearest, ties-to-even multiplication. -/
def mul (x y : F64) : F64 := ofModel (x.model * y.model)

/-- IEEE round-to-nearest, ties-to-even division. -/
def div (x y : F64) : F64 := ofModel (x.model / y.model)

/-- IEEE round-to-nearest, ties-to-even square root. -/
def sqrt (x : F64) : F64 := ofModel (Float.Model.sqrt x.model)

/-- Fused multiply-add with a single final rounding, as required by
IEEE 754-2019 §5.4.1: the exact product and sum are rounded once to the
destination format. Lean's model keeps the significand arithmetic exact until
its final normalization. -/
def fma (x y z : F64) : F64 := ofModel (Float.Model.fma x.model y.model z.model)

/-- Change sign without changing the magnitude bits. -/
def neg (x : F64) : F64 := ⟨x.bits ^^^ 0x8000000000000000⟩

/-- Clear the sign bit without changing the remaining bits. -/
def abs (x : F64) : F64 := ⟨x.bits &&& 0x7fffffffffffffff⟩

/-- Copy the sign bit of `y` onto the magnitude of `x`. -/
def copySign (x y : F64) : F64 :=
  ⟨(x.bits &&& 0x7fffffffffffffff) ||| (y.bits &&& 0x8000000000000000)⟩

/-- IEEE numeric equality. -/
def equal (x y : F64) : Bool := x.model == y.model

/-- IEEE unordered-aware less-than. -/
def lessThan (x y : F64) : Bool := decide (x.model < y.model)

instance : Add F64 := ⟨add⟩
instance : Sub F64 := ⟨sub⟩
instance : Mul F64 := ⟨mul⟩
instance : Div F64 := ⟨div⟩
instance : Neg F64 := ⟨neg⟩

end F64

/-- Classification of an IEEE 754 interchange datum. NaN payloads, signaling
status, and signs remain available in the raw encoding. -/
inductive Class where
  | zero
  | subnormal
  | normal
  | infinity
  | nan
  deriving DecidableEq, Repr

/-- IEEE 754 binary32 parameters (§3.3, Table 3.2 and §3.6, Table 3.5). -/
def binary32ExponentBits : Nat := 8
def binary32SignificandBits : Nat := 23
def binary32Bias : Int := 127
def binary32Width : Nat := 32

/-- IEEE 754 binary64 parameters (§3.3, Table 3.2 and §3.6, Table 3.5). -/
def binary64ExponentBits : Nat := 11
def binary64SignificandBits : Nat := 52
def binary64Bias : Int := 1023
def binary64Width : Nat := 64

/-- The maximum exponent-field value, reserved for infinities and NaNs. -/
def maxExponentField (exponentBits : Nat) : Nat := 2 ^ exponentBits - 1

/-- A decoded finite or non-finite datum, retaining all three fields. -/
structure Decoded where
  sign : Bool
  exponent : Nat
  trailingSignificand : Nat
  deriving DecidableEq, Repr

/-- Extract a `width`-bit field beginning at bit `offset` from an unsigned
integer bit pattern. Callers provide a raw bit pattern of the relevant width. -/
def field (bits : Nat) (offset width : Nat) : Nat :=
  bits / 2 ^ offset % 2 ^ width

/-- Decode a binary interchange bit pattern with `w` exponent bits and `t`
trailing-significand bits. The sign is the most significant bit. -/
def decode (w t : Nat) (bits : Nat) : Decoded :=
  { sign := field bits (w + t) 1 == 1
    exponent := field bits t w
    trailingSignificand := field bits 0 t }

/-- Classify fields according to IEEE 754-2019 §3.3. -/
def classify (w _t : Nat) (d : Decoded) : Class :=
  if d.exponent == 0 then
    if d.trailingSignificand == 0 then .zero else .subnormal
  else if d.exponent == maxExponentField w then
    if d.trailingSignificand == 0 then .infinity else .nan
  else .normal

/-- A signed integer as a rational. -/
def signed (negative : Bool) (n : ℚ) : ℚ :=
  if negative then -n else n

/-- Exact rational value of a finite encoding, computed from the encoding
fields. This is only defined for zero, subnormal, and normal values; signed
zero has rational value zero, while its sign remains in `Decoded.sign`. -/
def finiteValue (w t : Nat) (bias : Int) (d : Decoded) : Option ℚ :=
  let expAllOnes := maxExponentField w
  if d.exponent == expAllOnes then none
  else if d.exponent == 0 then
    let significand : ℚ := d.trailingSignificand / (2 ^ t : Nat)
    some (signed d.sign (significand * (2 : ℚ) ^ (1 - bias)))
  else
    let significand : ℚ := 1 + d.trailingSignificand / (2 ^ t : Nat)
    some (signed d.sign (significand * (2 : ℚ) ^ ((d.exponent : Int) - bias)))

/-- Decode a raw 32-bit pattern, represented as a natural below `2^32`. -/
def decode32 (bits : Nat) : Decoded := decode binary32ExponentBits binary32SignificandBits bits

/-- Decode a raw 64-bit pattern, represented as a natural below `2^64`. -/
def decode64 (bits : Nat) : Decoded := decode binary64ExponentBits binary64SignificandBits bits

/-- Classification of a binary32 bit pattern. -/
def classify32 (bits : Nat) : Class :=
  classify binary32ExponentBits binary32SignificandBits (decode32 bits)

/-- Classification of a binary64 bit pattern. -/
def classify64 (bits : Nat) : Class :=
  classify binary64ExponentBits binary64SignificandBits (decode64 bits)

/-- Exact finite binary32 value of a raw bit pattern. -/
def value32? (bits : Nat) : Option ℚ :=
  finiteValue binary32ExponentBits binary32SignificandBits binary32Bias (decode32 bits)

/-- Exact finite binary64 value of a raw bit pattern. -/
def value64? (bits : Nat) : Option ℚ :=
  finiteValue binary64ExponentBits binary64SignificandBits binary64Bias (decode64 bits)

/-- Exact rational interpretation when the encoding is finite. -/
def F32.toRat? (x : F32) : Option ℚ := value32? x.bits.toNat

/-- Exact rational interpretation when the encoding is finite. -/
def F64.toRat? (x : F64) : Option ℚ := value64? x.bits.toNat

/-! ## Refinement types

Raw values retain every interchange encoding. The subtypes below let APIs state
stronger input and output guarantees without losing that unrestricted type. -/

namespace F32

/-- Whether a binary32 encoding is a NaN. -/
def IsNaN (x : F32) : Prop := classify32 x.bits.toNat = .nan

instance (x : F32) : Decidable x.IsNaN := by
  unfold IsNaN
  infer_instance

/-- Whether a binary32 encoding is finite (including signed zero and subnormals). -/
def IsFinite (x : F32) : Prop :=
  (decode32 x.bits.toNat).exponent ≠ maxExponentField binary32ExponentBits

instance (x : F32) : Decidable x.IsFinite := by
  unfold IsFinite
  infer_instance

/-- Binary32 encodings with no NaN values. -/
abbrev NonNaN := {x : F32 // ¬ x.IsNaN}

/-- Finite binary32 encodings. -/
abbrev Finite := {x : F32 // x.IsFinite}

/-- The one canonical quiet NaN encoding used by Lean's arithmetic model. -/
def canonicalNaN : F32 := ⟨Float32.Model.nan.toBits⟩

/-- Whether `x` has the canonical quiet NaN payload, with either sign.
This is WebAssembly's canonical-NaN class; `canonicalNaN` selects positive sign. -/
def IsCanonicalNaN (x : F32) : Prop :=
  x.IsNaN ∧ (x.bits &&& 0x7fffffff) = (canonicalNaN.bits &&& 0x7fffffff)

/-- `x` is non-NaN or uses the canonical NaN payload. -/
def IsNonNaNOrCanonicalNaN (x : F32) : Prop := ¬ x.IsNaN ∨ x.IsCanonicalNaN

instance (x : F32) : Decidable x.IsCanonicalNaN := by
  unfold IsCanonicalNaN IsNaN
  infer_instance

instance (x : F32) : Decidable x.IsNonNaNOrCanonicalNaN := by
  unfold IsNonNaNOrCanonicalNaN
  infer_instance

/-- NaN bits admitted by WebAssembly's arithmetic-NaN class. -/
def IsArithmeticNaN (x : F32) : Prop :=
  x.IsNaN ∧ x.bits.toNat % 2 ^ binary32SignificandBits ≥ 2 ^ (binary32SignificandBits - 1)

instance (x : F32) : Decidable x.IsArithmeticNaN := by
  unfold IsArithmeticNaN IsNaN
  infer_instance

/-- Finite, infinite, and canonical-NaN binary32 values. This is the invariant
preserved by the deterministic arithmetic API. -/
abbrev Canonicalized := {x : F32 // x.IsNonNaNOrCanonicalNaN}

/-- Compatibility name emphasizing the NaN guarantee of `Canonicalized`. -/
abbrev CanonicalNaN := Canonicalized

/-- Short name for values with no non-canonical NaN payload. -/
abbrev Canonical := Canonicalized

end F32

namespace F64

/-- Whether a binary64 encoding is a NaN. -/
def IsNaN (x : F64) : Prop := classify64 x.bits.toNat = .nan

instance (x : F64) : Decidable x.IsNaN := by
  unfold IsNaN
  infer_instance

/-- Whether a binary64 encoding is finite. -/
def IsFinite (x : F64) : Prop :=
  (decode64 x.bits.toNat).exponent ≠ maxExponentField binary64ExponentBits

instance (x : F64) : Decidable x.IsFinite := by
  unfold IsFinite
  infer_instance

/-- Binary64 encodings with no NaN values. -/
abbrev NonNaN := {x : F64 // ¬ x.IsNaN}

/-- Finite binary64 encodings. -/
abbrev Finite := {x : F64 // x.IsFinite}

/-- The one canonical quiet NaN encoding used by Lean's arithmetic model. -/
def canonicalNaN : F64 := ⟨Float.Model.nan.toBits⟩

/-- Whether `x` has the canonical quiet NaN payload, with either sign.
This is WebAssembly's canonical-NaN class; `canonicalNaN` selects positive sign. -/
def IsCanonicalNaN (x : F64) : Prop :=
  x.IsNaN ∧ (x.bits &&& 0x7fffffffffffffff) = (canonicalNaN.bits &&& 0x7fffffffffffffff)

/-- `x` is non-NaN or uses the canonical NaN payload. -/
def IsNonNaNOrCanonicalNaN (x : F64) : Prop := ¬ x.IsNaN ∨ x.IsCanonicalNaN

instance (x : F64) : Decidable x.IsCanonicalNaN := by
  unfold IsCanonicalNaN IsNaN
  infer_instance

instance (x : F64) : Decidable x.IsNonNaNOrCanonicalNaN := by
  unfold IsNonNaNOrCanonicalNaN
  infer_instance

/-- NaN bits admitted by WebAssembly's arithmetic-NaN class. -/
def IsArithmeticNaN (x : F64) : Prop :=
  x.IsNaN ∧ x.bits.toNat % 2 ^ binary64SignificandBits ≥ 2 ^ (binary64SignificandBits - 1)

instance (x : F64) : Decidable x.IsArithmeticNaN := by
  unfold IsArithmeticNaN IsNaN
  infer_instance

/-- Finite, infinite, and canonical-NaN binary64 values. -/
abbrev Canonicalized := {x : F64 // x.IsNonNaNOrCanonicalNaN}

/-- Compatibility name emphasizing the NaN guarantee of `Canonicalized`. -/
abbrev CanonicalNaN := Canonicalized

/-- Short name for values with no non-canonical NaN payload. -/
abbrev Canonical := Canonicalized

end F64

/-! ## Relational WebAssembly results

WebAssembly Core 3.0 §4.3 models floating-point operators as relations when
the result is a NaN. With canonical NaN inputs (or no NaN inputs), either sign
of the canonical NaN is permitted. With a non-canonical NaN input, an
arithmetic NaN is permitted. The deterministic profile used here chooses
the positive canonical NaN in these cases. The functions above implement
that permitted deterministic choice; the relations below describe the broader Core
result set.
-/

namespace F32

/-- Whether every NaN among the operands is canonical. -/
def canonicalNaNInputs (x y : F32) : Prop :=
  x.IsNonNaNOrCanonicalNaN ∧ y.IsNonNaNOrCanonicalNaN

instance (x y : F32) : Decidable (canonicalNaNInputs x y) := by
  unfold canonicalNaNInputs
  infer_instance

/-- WebAssembly's allowed binary results for a deterministic evaluator. -/
def binaryResult (eval : F32 → F32 → F32) (x y z : F32) : Prop :=
  if (eval x y).IsNaN then
    if canonicalNaNInputs x y then z.IsCanonicalNaN
    else z.IsArithmeticNaN
  else z = eval x y

instance (eval : F32 → F32 → F32) (x y z : F32) : Decidable (binaryResult eval x y z) := by
  unfold binaryResult
  infer_instance

abbrev addRel := binaryResult add
abbrev subRel := binaryResult sub
abbrev mulRel := binaryResult mul
abbrev divRel := binaryResult div

/-- WebAssembly-permitted unary results, used here for square root. -/
def unaryResult (eval : F32 → F32) (x z : F32) : Prop :=
  if (eval x).IsNaN then
    if x.IsNonNaNOrCanonicalNaN then z.IsCanonicalNaN
    else z.IsArithmeticNaN
  else z = eval x

instance (eval : F32 → F32) (x z : F32) : Decidable (unaryResult eval x z) := by
  unfold unaryResult
  infer_instance

abbrev sqrtRel := unaryResult sqrt

/-- Whether every NaN among three operands is canonical. -/
def canonicalNaNInputs3 (x y z : F32) : Prop :=
  x.IsNonNaNOrCanonicalNaN ∧ y.IsNonNaNOrCanonicalNaN ∧ z.IsNonNaNOrCanonicalNaN

instance (x y z : F32) : Decidable (canonicalNaNInputs3 x y z) := by
  unfold canonicalNaNInputs3
  infer_instance

/-- NaN-result relation using the same canonical/arithmetic NaN policy as the
WebAssembly relation definitions. This operation is IEEE-style FMA; scalar FMA
is not a WebAssembly Core 3.0 instruction. -/
def fmaNaNResult (eval : F32 → F32 → F32 → F32) (x y w r : F32) : Prop :=
  if (eval x y w).IsNaN then
    if canonicalNaNInputs3 x y w then r.IsCanonicalNaN
    else r.IsArithmeticNaN
  else r = eval x y w

instance (eval : F32 → F32 → F32 → F32) (x y w r : F32) : Decidable (fmaNaNResult eval x y w r) := by
  unfold fmaNaNResult
  infer_instance

abbrev fmaNaNRel := fmaNaNResult fma

end F32

namespace F64

/-- Whether every NaN among the operands is canonical. -/
def canonicalNaNInputs (x y : F64) : Prop :=
  x.IsNonNaNOrCanonicalNaN ∧ y.IsNonNaNOrCanonicalNaN

instance (x y : F64) : Decidable (canonicalNaNInputs x y) := by
  unfold canonicalNaNInputs
  infer_instance

/-- WebAssembly's allowed binary results for a deterministic evaluator. -/
def binaryResult (eval : F64 → F64 → F64) (x y z : F64) : Prop :=
  if (eval x y).IsNaN then
    if canonicalNaNInputs x y then z.IsCanonicalNaN
    else z.IsArithmeticNaN
  else z = eval x y

instance (eval : F64 → F64 → F64) (x y z : F64) : Decidable (binaryResult eval x y z) := by
  unfold binaryResult
  infer_instance

abbrev addRel := binaryResult add
abbrev subRel := binaryResult sub
abbrev mulRel := binaryResult mul
abbrev divRel := binaryResult div

/-- WebAssembly-permitted unary results, used here for square root. -/
def unaryResult (eval : F64 → F64) (x z : F64) : Prop :=
  if (eval x).IsNaN then
    if x.IsNonNaNOrCanonicalNaN then z.IsCanonicalNaN
    else z.IsArithmeticNaN
  else z = eval x

instance (eval : F64 → F64) (x z : F64) : Decidable (unaryResult eval x z) := by
  unfold unaryResult
  infer_instance

abbrev sqrtRel := unaryResult sqrt

/-- Whether every NaN among three operands is canonical. -/
def canonicalNaNInputs3 (x y z : F64) : Prop :=
  x.IsNonNaNOrCanonicalNaN ∧ y.IsNonNaNOrCanonicalNaN ∧ z.IsNonNaNOrCanonicalNaN

instance (x y z : F64) : Decidable (canonicalNaNInputs3 x y z) := by
  unfold canonicalNaNInputs3
  infer_instance

/-- IEEE-style FMA NaN-result relation; scalar FMA is not in Wasm Core 3.0. -/
def fmaNaNResult (eval : F64 → F64 → F64 → F64) (x y w r : F64) : Prop :=
  if (eval x y w).IsNaN then
    if canonicalNaNInputs3 x y w then r.IsCanonicalNaN
    else r.IsArithmeticNaN
  else r = eval x y w

instance (eval : F64 → F64 → F64 → F64) (x y w r : F64) : Decidable (fmaNaNResult eval x y w r) := by
  unfold fmaNaNResult
  infer_instance

abbrev fmaNaNRel := fmaNaNResult fma

end F64

/-! ## Format facts -/

theorem binary32_width : binary32ExponentBits + binary32SignificandBits + 1 = binary32Width := by
  rfl

theorem binary64_width : binary64ExponentBits + binary64SignificandBits + 1 = binary64Width := by
  rfl

theorem binary32_max_finite_exponent :
    (maxExponentField binary32ExponentBits - 1 : Nat) = 254 := by
  rfl

theorem binary64_max_finite_exponent :
    (maxExponentField binary64ExponentBits - 1 : Nat) = 2046 := by
  rfl

@[simp] theorem classify32_positive_zero : classify32 0 = .zero := by
  rfl

@[simp] theorem classify64_positive_zero : classify64 0 = .zero := by
  rfl

@[simp] theorem value32_positive_zero : value32? 0 = some 0 := by
  simp [value32?, finiteValue, decode32, decode, field, binary32ExponentBits,
    binary32SignificandBits, binary32Bias, signed, maxExponentField,
    Rat.div_def, Rat.mul_def]

set_option exponentiation.threshold 2048 in
@[simp] theorem value64_positive_zero : value64? 0 = some 0 := by
  simp [value64?, finiteValue, decode64, decode, field, binary64ExponentBits,
    binary64SignificandBits, binary64Bias, signed, maxExponentField,
    Rat.div_def, Rat.mul_def]

end Silmaril.Numeric.Ieee754
