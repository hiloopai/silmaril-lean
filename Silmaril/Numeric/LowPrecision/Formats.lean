module

public import Mathlib.Data.Rat.Defs
public import Silmaril.Numeric.Ieee754

/-!
# Low-precision floating-point encodings

Lossless encodings and exact finite rational interpretations for IEEE
binary16, bfloat16, common FP8 formats, and E2M1 FP4. FP8/FP4 names describe
element formats only; block scales and packing layouts are modeled separately.

References: IEEE Std 754-2019 §§3.3–3.4 for binary16; Google,
"BFLOAT16: The secret to high performance on Cloud TPUs"
(<https://cloud.google.com/blog/products/ai-machine-learning/bfloat16-the-secret-to-high-performance>);
OCP Microscaling Formats (MX) v1.0 §§5.2–5.3 for E5M2, E4M3, and E2M1
(<https://www.opencompute.org/documents/ocp-microscaling-formats-mx-v1-0-spec-final-pdf>);
ONNX float8 technical specification for FNUZ encodings and biases
(<https://onnx.ai/onnx/technical/float8.html>);
NVIDIA Transformer Engine NVFP4 documentation for E2M1 element values
(<https://docs.nvidia.com/deeplearning/transformer-engine/features/low_precision_training/nvfp4/nvfp4.html>).
-/

@[expose] public section

namespace Silmaril.Numeric.LowPrecision

open Silmaril.Numeric.Ieee754

inductive SpecialEncoding where
  | ieee
  | e4m3fn
  | fnuz
  | finiteOnly
  deriving DecidableEq, Repr, Inhabited

/-- Parameters needed to decode a sign/exponent/fraction binary format. -/
structure FormatSpec where
  width : Nat
  exponentBits : Nat
  fractionBits : Nat
  bias : Int
  special : SpecialEncoding
  deriving DecidableEq, Repr, Inhabited

def binary16Spec : FormatSpec := ⟨16, 5, 10, 15, .ieee⟩
def bfloat16Spec : FormatSpec := ⟨16, 8, 7, 127, .ieee⟩
def e4m3fnSpec : FormatSpec := ⟨8, 4, 3, 7, .e4m3fn⟩
def e5m2Spec : FormatSpec := ⟨8, 5, 2, 15, .ieee⟩
def e4m3fnuzSpec : FormatSpec := ⟨8, 4, 3, 8, .fnuz⟩
def e5m2fnuzSpec : FormatSpec := ⟨8, 5, 2, 16, .fnuz⟩
def e2m1Spec : FormatSpec := ⟨4, 2, 1, 1, .finiteOnly⟩

inductive F8Format where
  | e4m3fn
  | e5m2
  | e4m3fnuz
  | e5m2fnuz
  deriving DecidableEq, Repr, Inhabited

def F8Format.spec : F8Format → FormatSpec
  | .e4m3fn => e4m3fnSpec
  | .e5m2 => e5m2Spec
  | .e4m3fnuz => e4m3fnuzSpec
  | .e5m2fnuz => e5m2fnuzSpec

inductive F4Format where
  | e2m1
  deriving DecidableEq, Repr, Inhabited

def F4Format.spec : F4Format → FormatSpec
  | .e2m1 => e2m1Spec

structure F16 where
  bits : UInt16
  deriving DecidableEq, Repr, Inhabited

structure BF16 where
  bits : UInt16
  deriving DecidableEq, Repr, Inhabited

/-- FP8 wrapper. The format index prevents mixing E4M3 and E5M2 encodings. -/
structure F8 (format : F8Format) where
  bits : UInt8
  deriving DecidableEq, Repr, Inhabited

/-- One unpacked FP4 element. Packed pairs are represented by two such values. -/
structure F4 (format : F4Format) where
  bits : BitVec 4
  deriving DecidableEq, Repr, Inhabited

abbrev F8E4M3FN := F8 .e4m3fn
abbrev F8E5M2 := F8 .e5m2
abbrev F8E4M3FNUZ := F8 .e4m3fnuz
abbrev F8E5M2FNUZ := F8 .e5m2fnuz
abbrev F4E2M1 := F4 .e2m1

/-- MXFP4 and NVFP4 use E2M1 element encodings. Their shared scale metadata
and block sizes belong to tensor formats, not this scalar alias. -/
abbrev MXFP4Element := F4E2M1
abbrev NVFP4Element := F4E2M1

inductive Class where
  | zero | subnormal | normal | infinity | nan
  deriving DecidableEq, Repr, Inhabited

def FormatSpec.maxExponent (spec : FormatSpec) : Nat := 2 ^ spec.exponentBits - 1
def FormatSpec.maxFraction (spec : FormatSpec) : Nat := 2 ^ spec.fractionBits - 1
def FormatSpec.signMask (spec : FormatSpec) : Nat := 2 ^ (spec.width - 1)

def exponentField (spec : FormatSpec) (bits : Nat) : Nat :=
  bits / 2 ^ spec.fractionBits % 2 ^ spec.exponentBits

def fractionField (spec : FormatSpec) (bits : Nat) : Nat :=
  bits % 2 ^ spec.fractionBits

def isNaNBits (spec : FormatSpec) (bits : Nat) : Bool :=
  let e := exponentField spec bits
  let m := fractionField spec bits
  match spec.special with
  | .ieee => e == spec.maxExponent && m != 0
  | .e4m3fn => e == spec.maxExponent && m == spec.maxFraction
  | .fnuz => bits == spec.signMask
  | .finiteOnly => false

def isInfinityBits (spec : FormatSpec) (bits : Nat) : Bool :=
  match spec.special with
  | .ieee => exponentField spec bits == spec.maxExponent && fractionField spec bits == 0
  | _ => false

/-- Read the encoding's sign bit, including the sign bit of NaNs. -/
def signBit (spec : FormatSpec) (bits : Nat) : Bool :=
  bits / spec.signMask % 2 == 1

/-- Negation preserves the unique zero and unique NaN of FNUZ formats.
For formats with signed zero, this is an exact sign-bit toggle. -/
def negateBits (spec : FormatSpec) (bits : Nat) : Nat :=
  if spec.special == .fnuz && (bits == 0 || isNaNBits spec bits) then bits
  else bits ^^^ spec.signMask

/-- Absolute value preserves FNUZ's unique NaN encoding. -/
def absBits (spec : FormatSpec) (bits : Nat) : Nat :=
  if spec.special == .fnuz && isNaNBits spec bits then bits
  else bits % spec.signMask

/-- Copy a sign while preserving FNUZ's unique zero and NaN. -/
def copySignBits (spec : FormatSpec) (magnitude sign : Nat) : Nat :=
  if spec.special == .fnuz && (magnitude == 0 || isNaNBits spec magnitude) then magnitude
  else absBits spec magnitude + if signBit spec sign then spec.signMask else 0

def classifyBits (spec : FormatSpec) (bits : Nat) : Class :=
  if isNaNBits spec bits then .nan
  else if isInfinityBits spec bits then .infinity
  else if exponentField spec bits == 0 then
    if fractionField spec bits == 0 then .zero else .subnormal
  else .normal

def signedRat (negative : Bool) (q : ℚ) : ℚ := if negative then -q else q

/-- Exact finite value of a format encoding. NaNs and infinities have no
rational denotation. Signed zeros both denote rational zero. -/
def exactValue? (spec : FormatSpec) (bits : Nat) : Option ℚ := do
  if isNaNBits spec bits || isInfinityBits spec bits then none else
  let e := exponentField spec bits
  let m := fractionField spec bits
  let negative := bits / spec.signMask % 2 == 1
  if e == 0 then
    some (signedRat negative ((m : ℚ) * (2 : ℚ) ^ (1 - spec.bias - spec.fractionBits)))
  else
    some (signedRat negative (((2 ^ spec.fractionBits + m : Nat) : ℚ) *
      (2 : ℚ) ^ ((e : Int) - spec.bias - spec.fractionBits)))

def F16.toRat? (x : F16) : Option ℚ := exactValue? binary16Spec x.bits.toNat
def BF16.toRat? (x : BF16) : Option ℚ := exactValue? bfloat16Spec x.bits.toNat
def F8.toRat? {format : F8Format} (x : F8 format) : Option ℚ := exactValue? format.spec x.bits.toNat
def F4.toRat? {format : F4Format} (x : F4 format) : Option ℚ := exactValue? format.spec x.bits.toNat

def F16.classify (x : F16) : Class := classifyBits binary16Spec x.bits.toNat
def BF16.classify (x : BF16) : Class := classifyBits bfloat16Spec x.bits.toNat
def F8.classify {format : F8Format} (x : F8 format) : Class := classifyBits format.spec x.bits.toNat
def F4.classify {format : F4Format} (x : F4 format) : Class := classifyBits format.spec x.bits.toNat

namespace F16

@[ext] theorem ext {x y : F16} (h : x.bits = y.bits) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- Construct from the lossless interchange bits. -/
def ofBits (bits : UInt16) : F16 := ⟨bits⟩

/-- Return the unchanged interchange bits. -/
def toBits (x : F16) : UInt16 := x.bits

def signBit (x : F16) : Bool := LowPrecision.signBit binary16Spec x.bits.toNat

def isNaN (x : F16) : Bool := isNaNBits binary16Spec x.bits.toNat

def isInfinite (x : F16) : Bool := isInfinityBits binary16Spec x.bits.toNat

def isFinite (x : F16) : Bool := !(x.isNaN || x.isInfinite)

def neg (x : F16) : F16 := ⟨UInt16.ofNat (negateBits binary16Spec x.bits.toNat)⟩

def abs (x : F16) : F16 := ⟨UInt16.ofNat (absBits binary16Spec x.bits.toNat)⟩

def copySign (x y : F16) : F16 :=
  ⟨UInt16.ofNat (copySignBits binary16Spec x.bits.toNat y.bits.toNat)⟩

instance : Neg (F16) := ⟨neg⟩

@[simp] theorem toBits_ofBits (bits : UInt16) :
    (ofBits bits : F16).toBits = bits := rfl

@[simp] theorem ofBits_toBits (x : F16) : ofBits x.toBits = x := rfl

end F16

namespace BF16

@[ext] theorem ext {x y : BF16} (h : x.bits = y.bits) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- Construct from the lossless interchange bits. -/
def ofBits (bits : UInt16) : BF16 := ⟨bits⟩

/-- Return the unchanged interchange bits. -/
def toBits (x : BF16) : UInt16 := x.bits

def signBit (x : BF16) : Bool := LowPrecision.signBit bfloat16Spec x.bits.toNat

def isNaN (x : BF16) : Bool := isNaNBits bfloat16Spec x.bits.toNat

def isInfinite (x : BF16) : Bool := isInfinityBits bfloat16Spec x.bits.toNat

def isFinite (x : BF16) : Bool := !(x.isNaN || x.isInfinite)

def neg (x : BF16) : BF16 := ⟨UInt16.ofNat (negateBits bfloat16Spec x.bits.toNat)⟩

def abs (x : BF16) : BF16 := ⟨UInt16.ofNat (absBits bfloat16Spec x.bits.toNat)⟩

def copySign (x y : BF16) : BF16 :=
  ⟨UInt16.ofNat (copySignBits bfloat16Spec x.bits.toNat y.bits.toNat)⟩

instance : Neg (BF16) := ⟨neg⟩

@[simp] theorem toBits_ofBits (bits : UInt16) :
    (ofBits bits : BF16).toBits = bits := rfl

@[simp] theorem ofBits_toBits (x : BF16) : ofBits x.toBits = x := rfl

end BF16

namespace F8

@[ext] theorem ext {format : F8Format} {x y : F8 format} (h : x.bits = y.bits) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- Construct from the lossless interchange bits. -/
def ofBits {format : F8Format} (bits : UInt8) : F8 format := ⟨bits⟩

/-- Return the unchanged interchange bits. -/
def toBits {format : F8Format} (x : F8 format) : UInt8 := x.bits

def signBit {format : F8Format} (x : F8 format) : Bool := LowPrecision.signBit format.spec x.bits.toNat

def isNaN {format : F8Format} (x : F8 format) : Bool := isNaNBits format.spec x.bits.toNat

def isInfinite {format : F8Format} (x : F8 format) : Bool := isInfinityBits format.spec x.bits.toNat

def isFinite {format : F8Format} (x : F8 format) : Bool := !(x.isNaN || x.isInfinite)

def neg {format : F8Format} (x : F8 format) : F8 format := ⟨UInt8.ofNat (negateBits format.spec x.bits.toNat)⟩

def abs {format : F8Format} (x : F8 format) : F8 format := ⟨UInt8.ofNat (absBits format.spec x.bits.toNat)⟩

def copySign {format : F8Format} (x y : F8 format) : F8 format :=
  ⟨UInt8.ofNat (copySignBits format.spec x.bits.toNat y.bits.toNat)⟩

instance {format : F8Format} : Neg (F8 format) := ⟨neg⟩

@[simp] theorem toBits_ofBits {format : F8Format} (bits : UInt8) :
    (ofBits bits : F8 format).toBits = bits := rfl

@[simp] theorem ofBits_toBits {format : F8Format} (x : F8 format) : ofBits x.toBits = x := rfl

end F8

namespace F4

@[ext] theorem ext {format : F4Format} {x y : F4 format} (h : x.bits = y.bits) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- Construct from the lossless interchange bits. -/
def ofBits {format : F4Format} (bits : BitVec 4) : F4 format := ⟨bits⟩

/-- Return the unchanged interchange bits. -/
def toBits {format : F4Format} (x : F4 format) : BitVec 4 := x.bits

def signBit {format : F4Format} (x : F4 format) : Bool := LowPrecision.signBit format.spec x.bits.toNat

def isNaN {format : F4Format} (x : F4 format) : Bool := isNaNBits format.spec x.bits.toNat

def isInfinite {format : F4Format} (x : F4 format) : Bool := isInfinityBits format.spec x.bits.toNat

def isFinite {format : F4Format} (x : F4 format) : Bool := !(x.isNaN || x.isInfinite)

def neg {format : F4Format} (x : F4 format) : F4 format := ⟨BitVec.ofNat 4 (negateBits format.spec x.bits.toNat)⟩

def abs {format : F4Format} (x : F4 format) : F4 format := ⟨BitVec.ofNat 4 (absBits format.spec x.bits.toNat)⟩

def copySign {format : F4Format} (x y : F4 format) : F4 format :=
  ⟨BitVec.ofNat 4 (copySignBits format.spec x.bits.toNat y.bits.toNat)⟩

instance {format : F4Format} : Neg (F4 format) := ⟨neg⟩

@[simp] theorem toBits_ofBits {format : F4Format} (bits : BitVec 4) :
    (ofBits bits : F4 format).toBits = bits := rfl

@[simp] theorem ofBits_toBits {format : F4Format} (x : F4 format) : ofBits x.toBits = x := rfl

end F4

end Silmaril.Numeric.LowPrecision
