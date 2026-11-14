module

public import Silmaril.Numeric.Libm.Exact.Defs
public meta import Silmaril.Numeric.Libm.Exact.Defs

/-!
# Batch 1: sample evaluations

Build-time checks of the batch-1 references: values on sample inputs (signed
zeros, halfway cases, subnormals, overflow), and every applicable special case
of each `Spec` on `B64.samples` and `B64.samplePairs`.
-/

namespace Silmaril.Numeric.Libm.Double

open Silmaril.Numeric.Ieee754 Silmaril.Numeric.Libm.B64

/-! ## Sample evaluations -/

#guard Ref.floor (d (-0.5)) == d (-1.0)
#guard Ref.floor (d 0.5) == d 0.0
#guard Ref.ceil (d (-0.5)) == d (-0.0)
#guard Ref.trunc (d (-1.75)) == d (-1.0)
#guard Ref.round (d 2.5) == d 3.0
#guard Ref.round (d (-2.5)) == d (-3.0)
#guard Ref.rint (d 2.5) == d 2.0
#guard Ref.rint (d 3.5) == d 4.0
#guard Ref.sqrt (d 2.0) == d (Float.sqrt 2.0)
#guard Ref.sqrt (d (-0.0)) == d (-0.0)
#guard (Ref.sqrt (d (-1.0))).isNaN
#guard Ref.fmod (d 5.5, d 2.0) == d 1.5
#guard Ref.fmod (d (-4.0), d 2.0) == d (-0.0)
#guard Ref.remainder (d 5.5, d 2.0) == d (-0.5)
#guard Ref.remainder (d 5.0, d 2.0) == d 1.0
#guard Ref.fmax (d 1.0, F64.canonicalNaN) == d 1.0
#guard Ref.fmin (F64.canonicalNaN, d (-3.0)) == d (-3.0)
#guard Ref.copysign (d 3.0, d (-0.0)) == d (-3.0)
#guard Ref.fabs (d (-0.0)) == d 0.0
#guard Ref.ldexp (d 0.75, 4) == d 12.0
#guard Ref.ldexp (d 1.0, 1024) == posInf
#guard Ref.ldexp (d 1.0, -1074) == F64.ofBits 1
#guard Ref.frexp (d 8.0) == (d 0.5, 4)
#guard Ref.frexp (d (-0.0)) == (d (-0.0), 0)
#guard Ref.frexp (F64.ofBits 1) == (d 0.5, -1073)
#guard Ref.modf (d (-3.25)) == (d (-0.25), d (-3.0))
#guard Ref.modf (d (-2.0)) == (d (-0.0), d (-2.0))
#guard Ref.modf negInf == (d (-0.0), negInf)

/-! ## The references meet their special cases on the samples -/

#guard checkCases (integralCases "floor" .towardNegative false) Ref.floor samples
#guard checkCases (integralCases "ceil" .towardPositive false) Ref.ceil samples
#guard checkCases (integralCases "trunc" .towardZero false) Ref.trunc samples
#guard checkCases (integralCases "round" .nearestTiesToAway false) Ref.round samples
#guard checkCases (integralCases "rint" .nearestTiesToEven true) Ref.rint samples
#guard checkCases fabsCases Ref.fabs samples
#guard checkCases sqrtCases Ref.sqrt samples
#guard checkCases copysignCases Ref.copysign samplePairs
#guard checkCases fmodCases Ref.fmod samplePairs
#guard checkCases remainderCases Ref.remainder samplePairs
#guard checkCases (minmaxCases "fmin" false) Ref.fmin samplePairs
#guard checkCases (minmaxCases "fmax" true) Ref.fmax samplePairs

end Silmaril.Numeric.Libm.Double
