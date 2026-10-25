module

public meta import Silmaril.Wasm.Wat.Lexer
public meta import Init.Data.Float.Model.Float32

/-! Exact WAT floating literals. Decimal and hexadecimal significands remain
integers until one rounding in Lean's logical IEEE model. No host floating
conversion is used. Explicit NaNs preserve their sign and payload. -/

public meta section

namespace Silmaril.Wasm.Wat

open Float.Model

/-- A signed decimal exponent, with WAT's underscore placement rules. -/
def floatExponent (text : String) : Except String Int := do
  let negative := text.startsWith "-"
  let signed := negative || text.startsWith "+"
  let n ← digits 10 (if signed then (text.drop 1).toString else text)
  return if negative then -(n : Int) else (n : Int)

/-- The exact significand and count of fractional digits, ignoring separators. -/
def floatMantissa (radix : Nat) (text : String) : Except String (Nat × Nat) := do
  match text.splitOn "." with
  | [whole] => return (← digits radix whole, 0)
  | [whole, fraction] =>
    let hi ← digits radix whole
    if fraction.isEmpty then return (hi, 0)
    let lo ← digits radix fraction
    let count := fraction.toList.countP (· != '_')
    return (hi * radix ^ count + lo, count)
  | _ => throw "floating literal has more than one radix point"

/-- Parse a magnitude into `mantissa * radix^exponent`. For hexadecimal input
the returned exponent is binary; for decimal input it is decimal. -/
def floatScientific (hexadecimal : Bool) (text : String) : Except String (Nat × Int) := do
  let text := if hexadecimal then (text.drop 2).toString else text
  let marker := if hexadecimal then "p" else "e"
  let parts := text.toLower.splitOn marker
  let (mantissa, exponent) ← match parts with
    | [mantissa] => pure (mantissa, 0)
    | [mantissa, exponent] => pure (mantissa, ← floatExponent exponent)
    | _ => throw "floating literal has more than one exponent"
  let (m, fractional) ← floatMantissa (if hexadecimal then 16 else 10) mantissa
  return (m, exponent - (fractional : Int) * (if hexadecimal then 4 else 1))

/-- Round an exact hexadecimal magnitude, avoiding enormous shifts for inputs
whose bit position already proves definite overflow or underflow. -/
def floatDyadic (format : Format) (mantissa : Nat) (exponent : Int) : Except String Nat := do
  if mantissa == 0 then return 0
  let leading := (mantissa.log2 : Int) + exponent
  if leading > (format.exponentBias : Int) then throw "floating literal overflows its format"
  if leading < format.minExponent - 1 then return 0
  return ((UnpackedFloat.round format .positive mantissa exponent).pack format).toNat

/-- Exact raw binary32/binary64 bits of a WAT literal. Numeric overflow is an
error; explicit infinity is valid. Underflow is rounded gradually, including
signed zero. NaN payloads must be nonzero and fit the trailing significand. -/
def floatBits (width : Nat) (text : String) : Except String Nat := do
  let format ← match width with
    | 32 => pure Format.binary32
    | 64 => pure Format.binary64
    | _ => throw "floating literal requires a 32-bit or 64-bit format"
  let negative := text.startsWith "-"
  let signed := negative || text.startsWith "+"
  let text := if signed then (text.drop 1).toString else text
  let trailing := format.mantissaBitsWithoutImplicit
  let infinity := (2 ^ format.exponentBits - 1) * 2 ^ trailing
  let sign := if negative then 2 ^ (width - 1) else 0
  if text == "inf" then return sign + infinity
  if text == "nan" then return sign + infinity + 2 ^ (trailing - 1)
  if text.startsWith "nan:0x" then
    let payload ← digits 16 (text.drop 6).toString
    unless 0 < payload && payload < 2 ^ trailing do
      throw "NaN payload must be nonzero and fit the significand"
    return sign + infinity + payload
  let hexadecimal := text.startsWith "0x"
  let (mantissa, exponent) ← floatScientific hexadecimal text
  let bits ← if hexadecimal then floatDyadic format mantissa exponent
    else pure ((UnpackedFloat.ofScientific format mantissa exponent).pack format).toNat
  if bits == infinity then throw "floating literal overflows its format"
  return sign + bits

end Silmaril.Wasm.Wat
