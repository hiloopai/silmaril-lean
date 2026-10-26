module

public import Silmaril.Numeric.Ieee754.DecimalSelection
meta import Silmaril.Numeric.Ieee754
meta import Silmaril.Numeric.Ieee754.Rounding
meta import Silmaril.Numeric.Ieee754.Exact
meta import Silmaril.Numeric.Ieee754.Operations
meta import Silmaril.Numeric.Ieee754.Decimal
meta import Silmaril.Numeric.Ieee754.DecimalNormalization

/-! # Decimal shortestness and decade-boundary checks

These execute the actual coefficient search and layout normalization. The
universal minimality and normalization claims are proved in DecimalShortest.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Decimal.ShortestExamples

def matchesNumber (actual : Number) (coefficient : Nat) (exponent : Int) : Bool :=
  actual.coefficient == coefficient && actual.exponent == exponent

def checks : List (String × Bool) := [
  ("lower-decade competitor", candidate ⟨9, 12, true⟩ 11 1 == some ⟨1, 1⟩),
  ("next-decade raw coefficient", candidate ⟨995 / 10, 1005 / 10, true⟩ (999 / 10) 1 == some ⟨10, 1⟩),
  ("next-decade normalization", matchesNumber (Number.mk 10 1).normalize 1 2),
  ("strict endpoints reject precision one", candidate ⟨99, 100, false⟩ (995 / 10) 1 == none),
  ("strict endpoints reject precision two", candidate ⟨99, 100, false⟩ (995 / 10) 2 == none),
  ("strict endpoints accept precision three", candidate ⟨99, 100, false⟩ (995 / 10) 3 == some ⟨995, -1⟩),
  ("decimal tie selects lower even", candidate ⟨12, 13, true⟩ (25 / 2) 2 == some ⟨12, 0⟩),
  ("decimal tie selects upper even", candidate ⟨13, 14, true⟩ (27 / 2) 2 == some ⟨14, 0⟩),
  ("long trailing-zero normalization", matchesNumber (Number.mk 123000000 (-8)).normalize 123 (-2)),
  ("power-of-ten significant digit", (Number.mk (10 ^ 17) (-8)).significantDigits == 1),
  ("normalized significant digits", (Number.mk 123 (-2)).significantDigits == 3),
  ("minimum subnormal", matchesNumber (shortest 1).normalize 5 (-324)),
  ("second subnormal", matchesNumber (shortest 2).normalize 1 (-323)),
  ("maximum subnormal", matchesNumber (shortest 0x000fffffffffffff).normalize 2225073858507201 (-323)),
  ("minimum normal", matchesNumber (shortest 0x0010000000000000).normalize 22250738585072014 (-324)),
  ("next normal", matchesNumber (shortest 0x0010000000000001).normalize 2225073858507202 (-323)),
  ("one tenth", matchesNumber (shortest 0x3fb999999999999a).normalize 1 (-1)),
  ("one's predecessor", matchesNumber (shortest 0x3fefffffffffffff).normalize 9999999999999999 (-16)),
  ("one", matchesNumber (shortest 0x3ff0000000000000).normalize 1 0),
  ("one's successor", matchesNumber (shortest 0x3ff0000000000001).normalize 10000000000000002 (-16)),
  ("maximum finite", matchesNumber (shortest 0x7fefffffffffffff).normalize 17976931348623157 292)]

def runChecks : IO Unit := do
  for (name, passed) in checks do
    if !passed then throw (IO.userError ("decimal shortestness check failed: " ++ name))

#eval runChecks

end Silmaril.Numeric.Ieee754.Decimal.ShortestExamples
