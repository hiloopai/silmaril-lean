module

public import Silmaril.Numeric.Ieee754.DecimalRepr
public import Silmaril.Numeric.Ieee754.DecimalTie
meta import Silmaril.Numeric.Ieee754
meta import Silmaril.Numeric.Ieee754.Rounding
meta import Silmaril.Numeric.Ieee754.Exact
meta import Silmaril.Numeric.Ieee754.Operations
meta import Silmaril.Numeric.Ieee754.Decimal
meta import Silmaril.Numeric.Ieee754.BinaryMagnitude
meta import Silmaril.Numeric.Ieee754.Bisection
meta import Silmaril.Numeric.Ieee754.AdjacentRounding
meta import Silmaril.Numeric.Ieee754.RationalRounding
meta import Silmaril.Numeric.Ieee754.Binary64Signs
meta import Silmaril.Numeric.Ieee754.SignedRationalRounding
meta import Silmaril.Numeric.DecimalText

/-! # Executable full-string formatting and parsing checks

Exercise layout thresholds, exact exponent parsing, malformed input, zero signs,
nonfinite spellings and signed binary64 round-trips through actual text.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Decimal.ReprExamples

open RationalRounding

def checks : List (String × Bool) := [
  ("fixed lower threshold", layout ⟨1, -4⟩ == "0.0001"),
  ("scientific lower threshold", layout ⟨1, -5⟩ == "1e-05"),
  ("fixed upper threshold", layout ⟨1, 15⟩ == "1000000000000000.0"),
  ("scientific upper threshold", layout ⟨1, 16⟩ == "1e+16"),
  ("interior point", layout ⟨12345, -4⟩ == "1.2345"),
  ("trim before layout", layout ⟨1230000, -4⟩ == "123.0"),
  ("large zero exponent", parseBinary64 (layout ⟨0, 999⟩) == some 0),
  ("exact parsed rational", decide (DecimalText.parse "1.25e-3" == some (.finite ⟨false, 1 / 800⟩))),
  ("positive zero spelling", repr 0 == "0.0"),
  ("negative zero spelling", repr 0x8000000000000000 == "-0.0"),
  ("positive infinity spelling", repr 0x7ff0000000000000 == "inf"),
  ("negative infinity spelling", repr 0xfff0000000000000 == "-inf"),
  ("negative NaN spelling", repr 0xfff0000000000001 == "nan"),
  ("negative zero parsing", parseBinary64 "-0.0" == some 0x8000000000000000),
  ("negative one tenth parsing", parseBinary64 "-0.1" == some 0xbfb999999999999a),
  ("explicit positive sign", parseBinary64 "+1.0" == some 0x3ff0000000000000),
  ("negative rational rounding", roundRational (-1 / 10) == 0xbfb999999999999a),
  ("negative overflow tie", roundRational (-overflowThreshold) == 0xfff0000000000000)]

def malformed : List String := ["", "+", "-", "--1", "1.2.3", "1e", "1e+", "1e2x", "1x", "1e2e3"]

def magnitudes : List UInt64 := [0, 1, 2, 0x000fffffffffffff, 0x0010000000000000, 0x0010000000000001,
  0x3fb999999999999a, 0x3fefffffffffffff, 0x3ff0000000000000, 0x3ff0000000000001,
  0x4340000000000000, 0x7feffffffffffffe, 0x7fefffffffffffff, 0x7ff0000000000000]

def nanEncodings : List UInt64 := [0x7ff0000000000001, 0x7ff8000000000000,
  0x7fffffffffffffff, 0xfff0000000000001, 0xfff8000000000000, 0xffffffffffffffff]

def runChecks : IO Unit := do
  for (name, passed) in checks do
    if !passed then throw (IO.userError ("decimal rendering check failed: " ++ name))
  for text in malformed do
    if (parseBinary64 text).isSome then throw (IO.userError ("malformed decimal accepted: " ++ text))
  for magnitude in magnitudes do
    for negative in [false, true] do
      let bits := Binary64Signs.withSign negative magnitude
      if parseBinary64 (repr bits) != some bits then
        throw (IO.userError ("full string round-trip failed: " ++ toString bits))
  for bits in nanEncodings do
    if parseBinary64 (repr bits) != some 0x7ff8000000000000 then
      throw (IO.userError ("NaN canonicalization failed: " ++ toString bits))

#eval runChecks

end Silmaril.Numeric.Ieee754.Decimal.ReprExamples
