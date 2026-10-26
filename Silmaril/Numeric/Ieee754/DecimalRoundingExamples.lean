module

public import Silmaril.Numeric.Ieee754.DecimalRounding
meta import Silmaril.Numeric.Ieee754
meta import Silmaril.Numeric.Ieee754.Rounding
meta import Silmaril.Numeric.Ieee754.Exact
meta import Silmaril.Numeric.Ieee754.Operations
meta import Silmaril.Numeric.Ieee754.Decimal
meta import Silmaril.Numeric.Ieee754.BinaryMagnitude
meta import Silmaril.Numeric.Ieee754.Bisection
meta import Silmaril.Numeric.Ieee754.AdjacentRounding
meta import Silmaril.Numeric.Ieee754.RationalRounding

/-! # Executable rational conversion and decimal round-trip boundaries

Exact rationals exercise both tie directions, subnormals, normal binade
boundaries, and the finite-to-infinity threshold. These checks execute the
bisection converter and the actual decimal formatter without host floats.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.RationalRounding.Examples

def hasBits (query : ℚ) (expected : UInt64) : Bool := roundPositive query == expected

def checks : List (String × Bool) := [
  ("zero", hasBits 0 0),
  ("one", hasBits 1 0x3ff0000000000000),
  ("one tenth", hasBits (1 / 10) 0x3fb999999999999a),
  ("normal tie selects lower even", hasBits (1 + 1 / 2 ^ 53) 0x3ff0000000000000),
  ("normal tie selects upper even", hasBits (1 + 3 / 2 ^ 53) 0x3ff0000000000002),
  ("zero tie selects zero", hasBits ((2 : ℚ) ^ (-1075 : Int)) 0),
  ("above zero tie selects minimum subnormal", hasBits
    ((2 : ℚ) ^ (-1075 : Int) + 2 ^ (-1200 : Int)) 1),
  ("subnormal tie selects upper even", hasBits (3 * (2 : ℚ) ^ (-1075 : Int)) 2),
  ("subnormal normal tie", hasBits
    ((2 : ℚ) ^ (-1022 : Int) - 2 ^ (-1075 : Int)) 0x0010000000000000),
  ("lower binade tie", hasBits (1 - 1 / 2 ^ 54) 0x3ff0000000000000),
  ("overflow tie selects infinity", hasBits overflowThreshold 0x7ff0000000000000),
  ("below overflow tie", hasBits (overflowThreshold - 2 ^ 969) 0x7fefffffffffffff),
  ("above overflow tie", hasBits (overflowThreshold + 2 ^ 969) 0x7ff0000000000000),
  ("large finite overflow", hasBits ((2 : ℚ) ^ (1024 : Nat)) 0x7ff0000000000000)]

def encodings : List UInt64 := [
  1, 2, 0x000fffffffffffff, 0x0010000000000000, 0x0010000000000001,
  0x3fb999999999999a, 0x3fefffffffffffff, 0x3ff0000000000000, 0x3ff0000000000001,
  0x3ff0000000000002, 0x4340000000000000, 0x7feffffffffffffe, 0x7fefffffffffffff]

def runChecks : IO Unit := do
  for (name, passed) in checks do
    if !passed then throw (IO.userError ("rational rounding check failed: " ++ name))
  for bits in encodings do
    if roundPositive (Decimal.rational bits) != bits then
      throw (IO.userError ("exact magnitude round-trip failed: " ++ toString bits))
    if roundPositive (Decimal.shortest bits).value != bits then
      throw (IO.userError ("decimal round-trip failed: " ++ toString bits))

#eval runChecks

end Silmaril.Numeric.Ieee754.RationalRounding.Examples
