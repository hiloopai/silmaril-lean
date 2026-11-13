module
public import Silmaril.Compiler.C.Float.Defs
public import Silmaril.Cerberus.Ail.Syntax.Defs
public import Silmaril.X86.Features.Ext.X87.Arith

/-! Extended real literals use the existing C mantissa/exponent reader and x87
64-bit significand rounding model. Decimal conversion retains a sticky bit below
all binary80 rounding boundaries; it does not first round to binary64. Numerical
adequacy of this compiler reader/model composition is a separate proof task. -/
@[expose] public section
namespace Silmaril.Compiler.Native.X87.Literals
open Silmaril.Compile.C
open Silmaril.X86.Features

/-- Round a nonnegative dyadic magnitude once to binary80, nearest ties to even. -/
def dyadic (mantissa : Nat) (exponent : Int) : Nat :=
  if mantissa == 0 then 0
  else (Fpu.roundExt 64 .nearest false mantissa exponent false {}).value.toNat

/-- Every binary80 rounding boundary is a multiple of `2^-16446`. The quotient
and sticky bit are taken below that grid, including the subnormal boundary. -/
def decimal (mantissa : Nat) (exponent : Int) : Nat :=
  if exponent ≥ 0 then dyadic (mantissa * 10 ^ exponent.toNat) 0
  else
    let bits : Nat := 16450
    let denominator := 10 ^ exponent.natAbs
    let numerator := mantissa * 2 ^ bits
    let quotient := numerator / denominator
    let sticky := if quotient * denominator == numerator then 0 else 1
    dyadic (2 * quotient + sticky) (-(bits + 1 : Int))

/-- A finite resource bound on source exponents; all ordinary binary80 literal
ranges lie inside it. Very large source exponents fail explicitly. -/
def bounded (exponent : Int) : Bool := exponent.natAbs ≤ 20000

def parse (text : String) : Option Nat :=
  match text.toList with
  | '0' :: x :: rest =>
      if x == 'x' || x == 'X' then
        let (mantissa, fraction, rest) := FloatConst.mantissa 16 Char.isHexDigit rest
        match rest with
        | p :: tail => do
            if p != 'p' && p != 'P' then none else do
              let exponent ← FloatConst.exponent tail
              let exponent := exponent - 4 * fraction
              if bounded exponent then some (dyadic mantissa exponent) else none
        | [] => none
      else decimalText ('0' :: x :: rest)
  | characters => decimalText characters
where
  decimalText (characters : List Char) : Option Nat := do
    let (mantissa, fraction, rest) := FloatConst.mantissa 10 Char.isDigit characters
    let exponent ← match rest with
      | [] => some (-(fraction : Int))
      | c :: tail =>
          if c == 'e' || c == 'E' then (FloatConst.exponent tail).map (· - fraction) else none
    if bounded exponent then some (decimal mantissa exponent) else none

/-- Preserve the source literal's own rounding before assignment conversion.
An unsuffixed literal is binary64 even when it initializes a long double. -/
def constant (literal : Silmaril.Cerberus.Ail.FloatingConstant) : Option Nat :=
  match literal.2 with
  | some .l => parse literal.1
  | some .f => (FloatConst.parse 4 literal.1).map fun bits => (Fpu.ofIeee 24 8 bits).toNat
  | none => (FloatConst.parse 8 literal.1).map fun bits => (Fpu.ofIeee 53 11 bits).toNat

def integer (value : Int) : Nat :=
  dyadic value.natAbs 0 ||| (if value < 0 then 2 ^ 79 else 0)

end Silmaril.Compiler.Native.X87.Literals
