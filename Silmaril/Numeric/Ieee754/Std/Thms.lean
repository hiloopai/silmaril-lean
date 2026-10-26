module

public import Silmaril.Numeric.Ieee754.Std.Defs
public import Silmaril.Numeric.Ieee754.Std.EncodingCorrect
public import Silmaril.Numeric.Ieee754.Std.Chaos
public import Silmaril.Numeric.Ieee754.Std.CoreBridge
public import Silmaril.Numeric.Ieee754.Std.WasmBridge
public import Silmaril.Numeric.Ieee754.Std.ProfileBridge

/-!
# IEEE 754-2019 `Std` core: theorems

Entry point for the theorems about the `Std` core: uniqueness of the rounding
specification and correctness of the executable rounder (`Std.Round`,
`Std.Format`), faithful encodings (`Std.EncodingCorrect`), the NaN-policy
lattice and ISA inclusions (`Std.NaN`, `Std.Isa`, `Std.WasmBridge`), chaotic
variants (`Std.Chaos`), and the bridges to `Float.Model`, `F32`/`F64` and the
`Numeric.Float` profiles (`Std.CoreBridge`, `Std.ProfileBridge`).
-/
