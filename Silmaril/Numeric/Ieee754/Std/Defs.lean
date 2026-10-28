module

public import Silmaril.Numeric.Ieee754.Exact
public import Silmaril.Numeric.Ieee754.Std.Isa
public import Silmaril.Numeric.Ieee754.Std.IntegerRound
public import Silmaril.Numeric.Ieee754.Std.TestFloat
public import Silmaril.Numeric.Ieee754.Std.Bridge

/-!
# IEEE 754-2019 `Std` core: definitions

Entry point for the definitions of the `Std` core: grids and rounding
(`Std.Round`), formats and delivery (`Std.Format`), exact outcomes of the
operations (`Std.Ops`, `Std.Sqrt`, `Std.IntegerRound`), encodings
(`Std.Encoding`), NaN policies (`Std.NaN`), ISA profiles (`Std.Isa`), the
TestFloat line checker (`Std.TestFloat`) and the executable bridges
(`Std.Bridge`). See `docs/Ieee754Std.md`.
-/
