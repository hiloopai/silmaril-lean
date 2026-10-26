module

public import Silmaril.Numeric.Float.Encoding
public import Silmaril.Numeric.Float.Classify
public import Silmaril.Numeric.Float.Profile
public import Silmaril.Numeric.Float.Ops
public import Silmaril.Numeric.Float.Instances
public import Silmaril.Numeric.Float.Flags
public import Silmaril.Numeric.Float.Delivered
public import Silmaril.Numeric.Float.Exceptions
public import Silmaril.Numeric.Float.Wasm
public import Silmaril.Numeric.Float.Lowering
public import Silmaril.Numeric.Float.Spec
public import Silmaril.Numeric.Float.Tests

/-!
# Architecture floating-point profiles

The shared layer between the IEEE 754 model (`Silmaril.Numeric.Ieee754`) and
instruction-set semantics for floating point:

* `Float.Encoding`: format-generic raw encodings (`Bits fmt`), NaN classes, quieting,
  default NaNs, NaN format conversion and subnormal flushing.
* `Float.Classify`: `Bits.datum`, a raw encoding as an operand of the IEEE
  exception specification (`Silmaril.Numeric.Ieee754.Flags`), with the bridges
  to the bit-level NaN, subnormal and flushing predicates and to the decoder's
  exact value.
* `Float.Profile`: `Profile`, the record of implementation choices (NaN propagation,
  default NaN sign, DAZ/FTZ, tininess, min/max rules, float-to-integer overflow
  results and inexact signaling), the rounding stage (`Profile.stage`) that
  classifies exact results, and `RoundingSelect` for an instruction's static or
  dynamic rounding direction (the direction itself is an argument of every
  operation, not a profile field).
* `Float.Ops`: profile-parametric add, sub, mul, div, sqrt, fma, min/max, compare,
  round-to-integral and conversions, returning result bits, IEEE exception flags
  and a subnormal-operand indication.
* `Float.Instances`: x86 SSE (MXCSR), RISC-V F/D and AArch64 (FPCR) profiles,
  each field cited to its manual, plus x86 `CMPSS` predicates and flag encodings.
* `Float.Flags`: each operation's flags against the IEEE flag functions: equal
  without flushing; with DAZ, the IEEE flags of the flushed operands; with FTZ
  (and DAZ clear), the exact difference for x86; x86 `COMIS`/`UCOMIS`, `MINSS`
  and integer-indefinite conversions.
* `Float.Delivered`: without flushing, the returned value of add, sub, mul, div,
  sqrt, fma and conversion on finite operands decodes to the IEEE delivered result
  of the exact value, so inexact is raised exactly when the value differs from it.
* `Float.Exceptions`: conditions outside IEEE default handling that several
  architectures share: underflow with the trap enabled (`Profile.tinyOutcome`,
  `Profile.underflowCondition`) and the x86 DE and AArch64 IDC subnormal-operand
  rules (`Outcome.denormalAfterPriority`, `Outcome.inputDenormalFlushed`).
* `Float.Wasm`: which profile results WebAssembly's nondeterministic float semantics
  admits, for every profile.
* `Float.Lowering`: architecture-independent lemmas for verifying instruction
  sequences that implement WebAssembly float operators (comparison facts, exact
  results, rounding of integer values, float-to-integer ranges).
* `Float.Spec`: `FloatImpl`, `ConvertImpl` and `SoftFloat` with their correctness
  statements, for software implementations.
* `Float.Tests`: kernel-checked vectors.
-/
