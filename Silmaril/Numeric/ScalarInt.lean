module

public import Silmaril.Numeric.Scalar

/-! # Integer conversion at the selected arithmetic precision

Conversion packs the exact integer directly in the destination format. In
particular, it does not first round through a wider floating-point format.
-/

@[expose] public section
namespace Silmaril.Numeric.Arithmetic

def ofInt (format : ArithmeticFormat) (n : Int) (policy : ArithmeticPolicy := {}) :
    Value format :=
  output format policy (Ieee754.Rounding.packRounded format.core policy.rounding
    (Ieee754.Rounding.ofInt n))

end Silmaril.Numeric.Arithmetic
