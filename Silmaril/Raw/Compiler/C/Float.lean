module

public import Silmaril.Numeric.Ieee754.Rounding
public import Silmaril.Cerberus.Mem.Defs
/-! # Floating constants for code generation

The C compiler keeps a floating value in a 64-bit register as its IEEE 754
interchange bits: binary32 (`float`) zero-extended from 32 bits, binary64
(`double`). Operations on them are calls of the soft-float routines of the runtime
library (`tools/ccomp/runtime/libc.c`); this module computes the same operations at
compile time, for floating constants and constant initializers, with the correctly
rounded (round to nearest, ties to even) model of `Silmaril.Numeric.Ieee754`.

A floating format is named by its width in bytes: `4` (binary32) or `8` (binary64).

## Intended theorem

`parse w text` is the encoding of the real number denoted by the C floating constant
`text` (STD §6.4.4.2, decimal or hexadecimal) rounded to nearest-even in format `w`;
`ofInt`, `convert`, `toInt?` and `binary` are the IEEE 754 operations of
`Silmaril.Numeric.Ieee754` on encodings (`F32`, `F64`), so that a constant folded
here equals the value the soft-float routines compute at run time.
-/

@[expose] public section

namespace Silmaril.Compile.C.FloatConst

open Silmaril.Numeric.Ieee754

/-- The IEEE format of a floating width (4: binary32, otherwise binary64). -/
def format (w : Nat) : Float.Model.Format := if w == 4 then .binary32 else .binary64

/-- The sign bit of format `w`. -/
def signBit (w : Nat) : Nat := if w == 4 then 2 ^ 31 else 2 ^ 63

/-- The encoding of `m · 2 ^ e` rounded to nearest-even in format `w`. -/
def ofDyadic (w : Nat) (m e : Int) : Nat :=
  (Rounding.packRounded (format w) .nearestTiesToEven (Rounding.ofDyadic m e)).toNat

/-- The encoding of the integer `n`. -/
def ofInt (w : Nat) (n : Int) : Nat := ofDyadic w n 0

/-- The encoding of `m · 10 ^ e`, rounded once: for `e < 0`, `⌊m 2^k / 10^-e⌋` with a
sticky bit, at `k = 1100` bits below the binary point, rounds like the exact value
(every rounding boundary of both formats is a multiple of `2 ^ -1075`). -/
def ofDecimal (w : Nat) (m : Nat) (e : Int) : Nat :=
  if e ≥ 0 then ofDyadic w (m * 10 ^ e.toNat) 0
  else
    let k : Nat := 1100
    let den : Nat := 10 ^ e.natAbs
    let q := m * 2 ^ k / den
    let sticky := if q * den == m * 2 ^ k then 0 else 1
    ofDyadic w (2 * q + sticky) (-(k + 1 : Int))

/-- The value of a hexadecimal digit. -/
def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87

/-- Digits in `base`, an optional fraction, and the number of fraction digits. -/
def mantissa (base : Nat) (isDigit : Char → Bool) (s : List Char) : Nat × Nat × List Char :=
  let int := s.takeWhile isDigit
  let rest := s.drop int.length
  let (frac, rest) := match rest with
    | '.' :: r => let f := r.takeWhile isDigit; (f, r.drop f.length)
    | r => ([], r)
  let digit (c : Char) := if base == 16 then hexDigit c else c.toNat - 48
  ((int ++ frac).foldl (fun a c => a * base + digit c) 0, frac.length, rest)

/-- A signed decimal exponent. -/
def exponent (s : List Char) : Option Int :=
  let (neg, ds) := match s with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  if ds.isEmpty || !ds.all Char.isDigit then none
  else
    let v : Int := ds.foldl (fun a c => a * 10 + (c.toNat - 48)) 0
    some (if neg then -v else v)

/-- The encoding of a C floating constant (its text, without suffix) in format `w`. -/
def parse (w : Nat) (text : String) : Option Nat :=
  match text.toList with
  | '0' :: x :: rest =>
    if x == 'x' || x == 'X' then
      let (m, nf, rest) := mantissa 16 Char.isHexDigit rest
      match rest with
      | p :: er => if p == 'p' || p == 'P' then
          (exponent er).map fun e => ofDyadic w m (e - 4 * nf)
        else none
      | [] => none
    else decimal ('0' :: x :: rest)
  | s => decimal s
where
  decimal (s : List Char) : Option Nat :=
    let (m, nf, rest) := mantissa 10 Char.isDigit s
    match rest with
    | [] => some (ofDecimal w m (-(nf : Int)))
    | c :: er => if c == 'e' || c == 'E' then
        (exponent er).map fun e => ofDecimal w m (e - nf)
      else none

/-- Convert an encoding from format `src` to format `dst`. -/
def convert (src dst : Nat) (x : Nat) : Nat :=
  if (src == 4) == (dst == 4) then x
  else if src == 4 then (F32.toF64 ⟨x.toUInt32⟩).bits.toNat
  else (F64.toF32 ⟨x.toUInt64⟩).bits.toNat

/-- Truncation toward zero; `none` for NaN and infinities. -/
def toInt? (w : Nat) (x : Nat) : Option Int :=
  if w == 4 then F32.toInt? ⟨x.toUInt32⟩ else F64.toInt? ⟨x.toUInt64⟩

/-- An arithmetic operation of C on two encodings of format `w`. -/
def binary (w : Nat) (op : Cerberus.ArithmeticOperator) (x y : Nat) : Option Nat :=
  if w == 4 then
    let (a, b) : F32 × F32 := (⟨x.toUInt32⟩, ⟨y.toUInt32⟩)
    let r : Option F32 := match op with
      | .add => some (F32.addWith .nearestTiesToEven a b) | .sub => some (F32.subWith .nearestTiesToEven a b)
      | .mul => some (F32.mulWith .nearestTiesToEven a b) | .div => some (F32.divWith .nearestTiesToEven a b)
      | _ => none
    r.map (·.bits.toNat)
  else
    let (a, b) : F64 × F64 := (⟨x.toUInt64⟩, ⟨y.toUInt64⟩)
    let r : Option F64 := match op with
      | .add => some (F64.addWith .nearestTiesToEven a b) | .sub => some (F64.subWith .nearestTiesToEven a b)
      | .mul => some (F64.mulWith .nearestTiesToEven a b) | .div => some (F64.divWith .nearestTiesToEven a b)
      | _ => none
    r.map (·.bits.toNat)

end Silmaril.Compile.C.FloatConst
