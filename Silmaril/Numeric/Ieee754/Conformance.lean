module

public import Silmaril.Numeric.Ieee754.ArithmeticCorrectness
public import Silmaril.Numeric.Ieee754.ConversionCorrectness
public import Silmaril.Numeric.Ieee754.Environment
public import Silmaril.Numeric.Ieee754.Inspection
public import Silmaril.Numeric.Ieee754.IntegerRounding

/-!
# IEEE 754 correctness development

Imports mathematical proofs of exact arithmetic, residual classification,
rounding decisions, normalization, encoding, and selected arithmetic and
conversion contracts. Exception-state and binary inspection laws are included.

This is not a theorem of complete IEEE 754 conformance. In particular, arithmetic
exception generation and required external character conversions are not yet
implemented. The precise proven contracts and remaining obligations are listed
in `docs/IEEEConformance.md`.

IEEE 754-2019: <https://standards.ieee.org/ieee/754/6210/>.
-/
