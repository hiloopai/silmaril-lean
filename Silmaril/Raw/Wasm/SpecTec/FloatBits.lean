module

public import Silmaril.Raw.Wasm.SpecTec.Basic
public import Silmaril.Wasm.Types
public import Mathlib.Data.BitVec

@[expose] public section

/-! # IEEE bit patterns as SpecTec float literals

The elaborated `fN`/`fNmag` constructors preserve the sign of zero and every NaN
payload bit. Normal literals carry the fraction field and an unbiased signed
exponent. This encodes literals only; no host floating-point arithmetic is used.
See the [pinned value grammar](https://github.com/WebAssembly/spec/blob/608711107b7f1edb13efd57b7d79b49477462d36/specification/wasm-3.0/1.1-syntax.values.spectec).
-/

namespace Silmaril.Wasm.SpecTecEnc

def floatFractionWidth : FloatType → Nat
  | .f32 => 23 | .f64 => 52

def floatExponentWidth : FloatType → Nat
  | .f32 => 8 | .f64 => 11

def floatFraction (t : FloatType) (bits : BitVec t.width) : Nat :=
  bits.toNat % 2 ^ floatFractionWidth t

def floatExponent (t : FloatType) (bits : BitVec t.width) : Nat :=
  bits.toNat / 2 ^ floatFractionWidth t % 2 ^ floatExponentWidth t

def floatSign (t : FloatType) (bits : BitVec t.width) : Nat :=
  bits.toNat / 2 ^ (floatFractionWidth t + floatExponentWidth t)

/-- The three extracted fields reconstruct the original unsigned bit pattern. -/
theorem floatFields_reconstruct (t : FloatType) (bits : BitVec t.width) :
    bits.toNat = floatFraction t bits + 2 ^ floatFractionWidth t * floatExponent t bits +
      2 ^ (floatFractionWidth t + floatExponentWidth t) * floatSign t bits := by
  cases t <;>
    simp only [floatFraction, floatExponent, floatSign, floatFractionWidth, floatExponentWidth] <;>
    omega

theorem floatSign_le_one (t : FloatType) (bits : BitVec t.width) : floatSign t bits ≤ 1 := by
  have h := bits.isLt
  cases t <;> simp only [floatSign, floatFractionWidth, floatExponentWidth, FloatType.width] at * <;>
    omega

def floatBits (t : FloatType) (bits : BitVec t.width) : Value :=
  let mantissa := floatFraction t bits
  let exponent := floatExponent t bits
  let magnitude :=
    if exponent = 0 then node "SUBNORM" [nat mantissa]
    else if exponent = 2 ^ floatExponentWidth t - 1 then
      if mantissa = 0 then node "INF" [] else node "NAN" [nat mantissa]
    else node "NORM" [nat mantissa,
      .atom ((exponent : Int) - ((2 ^ (floatExponentWidth t - 1) - 1 : Nat) : Int))]
  node (if floatSign t bits = 0 then "POS" else "NEG") [magnitude]

example : floatBits .f32 (0#32) = node "POS" [node "SUBNORM" [nat 0]] := rfl
example : floatBits .f32 (0x80000000#32) = node "NEG" [node "SUBNORM" [nat 0]] := rfl
example : floatBits .f32 (0x3f000000#32) = node "POS" [node "NORM" [nat 0, .atom (-1)]] := rfl
example : floatBits .f32 (0x00800000#32) = node "POS" [node "NORM" [nat 0, .atom (-126)]] := rfl
example : floatBits .f32 (1#32) = node "POS" [node "SUBNORM" [nat 1]] := rfl
example : floatBits .f32 (0x7f7fffff#32) =
    node "POS" [node "NORM" [nat 8388607, .atom 127]] := rfl
example : floatBits .f32 (0xff800000#32) = node "NEG" [node "INF" []] := rfl
example : floatBits .f32 (0x7f800001#32) = node "POS" [node "NAN" [nat 1]] := rfl
example : floatBits .f32 (0xffc00000#32) = node "NEG" [node "NAN" [nat 4194304]] := rfl
example : floatBits .f64 (0x0010000000000000#64) =
    node "POS" [node "NORM" [nat 0, .atom (-1022)]] := rfl
example : floatBits .f64 (0x7fefffffffffffff#64) =
    node "POS" [node "NORM" [nat 4503599627370495, .atom 1023]] := rfl
example : floatBits .f64 (0x7ff0000000000001#64) = node "POS" [node "NAN" [nat 1]] := rfl

end Silmaril.Wasm.SpecTecEnc
