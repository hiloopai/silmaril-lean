module

public import Silmaril.Numeric.Ieee754.Flags.Grid
public import Silmaril.Numeric.Ieee754.Flags.Rounding
public import Silmaril.Numeric.Ieee754.Flags.Sqrt
public import Silmaril.Numeric.Ieee754.Flags.Datum
public import Silmaril.Numeric.Ieee754.Flags.Operations
public import Silmaril.Numeric.Ieee754.Flags.Outcome
public import Silmaril.Numeric.Ieee754.Flags.Denormal
public import Silmaril.Numeric.Ieee754.Flags.Compare
public import Silmaril.Numeric.Ieee754.Flags.Binary
public import Silmaril.Numeric.Ieee754.Flags.Executable
public import Silmaril.Numeric.Ieee754.Flags.DivSqrt

/-!
# IEEE 754 arithmetic exception flags

This module specifies the five exception flags of IEEE 754-2019 §7 (invalid
operation, division by zero, overflow, underflow, inexact) for the arithmetic
and conversion operations, under default (non-trapping) exception handling.
The specification is architecture-independent and generic over the core
`Float.Model.Format`, so it applies to binary16, bfloat16, binary32 and binary64
alike. It is independent of the executable rounding in `Numeric.Ieee754.Rounding`.

* `Flags.Grid`: the five rounding directions as integer rounding in any ordered
  field with a floor function, and rounding to a binary grid.
* `Flags.Rounding`: overflow, tininess (both `Tininess` conventions), underflow and
  inexact for an exact result; `inexact_iff_not_representable` and the
  implications between the flags.
* `Flags.Sqrt`: a computable classification of irrational square roots, equal to
  the classification of `Real.sqrt`.
* `Flags.Datum`: operand classification from raw encodings, including signaling
  NaNs, and agreement with the `F32`/`F64` wrappers.
* `Flags.Operations`: flags of add, sub, mul, div, sqrt, fma, format conversion,
  integer conversions and integral rounding, with characterisations.
* `Flags.Outcome`: the operand-determined outcome of each operation, separated
  from the rounding stage.
* `Flags.Denormal`: denormals-are-zero and flush-to-zero hooks, and the effect of
  output flushing on an outcome's flags (`Outcome.flags_flushToZero`).
* `Flags.Compare`: flags of quiet and signaling comparisons and of the IEEE
  minimum/maximum operations.
* `Flags.Binary`: binary32/binary64 entry points and sticky accumulation in an
  `Environment`.
* `Flags.Executable`: the executable rounding (`Rounding.packRounded`) delivers
  exactly the specification's `deliver`, so for binary32/binary64 addition,
  subtraction, multiplication, fused multiply-add, integer-to-float conversion,
  binary64-to-binary32 narrowing and round-to-integral
  (`Rounding.integralRounded`), the inexact flag holds exactly when the returned
  value differs from the exact result.
* `Flags.DivSqrt`: the same for division and square root, which round through
  separate quotient and root cores (`Rounding.divRounded`,
  `Rounding.sqrtRounded`): the decoded quotient is `deliver` of the exact
  quotient, the decoded root read in `ℝ` is `deliver` of the real square root,
  and the binary32/binary64 inexact flags agree with the returned values.

NaN payloads and zero signs are not part of this specification.

Reference: <https://standards.ieee.org/ieee/754/6210/>.
-/
