module

public import Mathlib.Data.Rat.Defs
public import Init.Data.Nat.ToString

/-! # Exact decimal text parsing

A small executable parser for signed decimal numerals and scientific notation.
It preserves the sign of zero separately from the rational value. This module
contains no binary floating-point or formatter dependencies.
-/

@[expose] public section

namespace Silmaril.Numeric.DecimalText

/-- Decimal sign and nonnegative magnitude, retaining negative zero. -/
structure Finite where
  negative : Bool
  magnitude : ℚ
  deriving DecidableEq, Repr

def Finite.value (value : Finite) : ℚ := if value.negative then -value.magnitude else value.magnitude

/-- Special spellings retain infinity sign; NaNs carry no payload in text. -/
inductive Value where
  | finite (value : Finite)
  | infinity (negative : Bool)
  | nan
  deriving DecidableEq, Repr

/-- Exact interpretation of an unsigned list of decimal digits. -/
def digitsValue (digits : List Char) : Nat := Nat.ofDigitChars 10 digits 0

/-- Parse a nonempty sequence of decimal digits. -/
def parseNat (digits : List Char) : Option Nat :=
  if digits.isEmpty || !(digits.all Char.isDigit) then none else some (digitsValue digits)

/-- Exponents accept a leading sign and require at least one decimal digit. -/
def parseExponent : List Char → Option Int
  | '+' :: digits => (parseNat digits).map Int.ofNat
  | '-' :: digits => (parseNat digits).map (fun n => -(n : Int))
  | digits => (parseNat digits).map Int.ofNat

/-- Finish a decimal coefficient using the count of fractional digits. -/
def finish (coefficient fractional : Nat) (exponent : Int) : ℚ :=
  (coefficient : ℚ) * (10 : ℚ) ^ (exponent - (fractional : Int))

/-- Consume the mantissa while accumulating its integer coefficient and the
number of digits after the decimal point. Reject extra punctuation and trailing
junk; scientific notation consumes the entire remaining exponent. -/
def scan : List Char → Nat → Nat → Bool → Bool → Option ℚ
  | [], coefficient, fractional, _, seen =>
    if seen then some (finish coefficient fractional 0) else none
  | c :: rest, coefficient, fractional, point, seen =>
    if c.isDigit then
      scan rest (10 * coefficient + (c.toNat - 48)) (fractional + if point then 1 else 0) point true
    else if c == '.' && !point then scan rest coefficient fractional true seen
    else if c == 'e' && seen then (parseExponent rest).map (finish coefficient fractional)
    else none

/-- Parse a signed finite decimal, preserving the sign of a zero mantissa. -/
def parseFinite (input : List Char) : Option Finite :=
  match input with
  | '-' :: rest => (scan rest 0 0 false false).map (Finite.mk true)
  | '+' :: rest => (scan rest 0 0 false false).map (Finite.mk false)
  | rest => (scan rest 0 0 false false).map (Finite.mk false)

def parse (input : String) : Option Value :=
  if input == "nan" then some .nan
  else if input == "inf" || input == "+inf" then some (.infinity false)
  else if input == "-inf" then some (.infinity true)
  else (parseFinite input.toList).map Value.finite

end Silmaril.Numeric.DecimalText
