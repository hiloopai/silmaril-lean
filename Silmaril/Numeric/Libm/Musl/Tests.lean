module

public import Silmaril.Numeric.Libm.Musl.Defs
public meta import Silmaril.Numeric.Libm.Musl.Defs

/-!
# musl `sin`/`cos`: sample evaluations

The transcription is compared with the host's `Float.sin`/`Float.cos` (the
platform libm, not musl): on these samples the two agree to within one step
of the encoding. Tiny arguments take musl's early exits exactly.
-/

namespace Silmaril.Numeric.Libm.Musl

open Silmaril.Numeric.Ieee754 Silmaril.Numeric.Libm.B64

/-- Encodings at most one step apart (same sign). -/
def adjacent (a b : F64) : Bool := a.bits == b.bits || a.bits + 1 == b.bits || b.bits + 1 == a.bits

def trigSamples : List Float :=
  [0.5, 1.0, -1.0, 2.0, 3.0, -3.0, 0.785398, 1.5707963267948966, 3.141592653589793,
    4.71238898038469, 6.283185307179586, 10.0, -100.0, 1e5, 123456.789, 7.0, 0.1,
    0.7853981633974483, 1647000.5, 1e6, -0.9]

#guard trigSamples.all fun x => match sin (d x) with
  | some y => adjacent y (d (Float.sin x))
  | none => false

#guard trigSamples.all fun x => match cos (d x) with
  | some y => adjacent y (d (Float.cos x))
  | none => false

#guard sin (d 1e-9) == some (d 1e-9)
#guard sin (d (-0.0)) == some (d (-0.0))
#guard cos (d 1e-9) == some (d 1.0)
#guard sin (d 1647099.0) == none
#guard sin (d 1e10) == none
#guard sin posInf == none

end Silmaril.Numeric.Libm.Musl
