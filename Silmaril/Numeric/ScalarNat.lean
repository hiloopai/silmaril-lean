module

public import Silmaril.Numeric.ScalarInt

/-! # Dimension constants at scalar precision -/

@[expose] public section
namespace Silmaril.Numeric.Arithmetic

def nat32 (n : Nat) : Value .f32 :=
  ofInt .f32 n

end Silmaril.Numeric.Arithmetic
