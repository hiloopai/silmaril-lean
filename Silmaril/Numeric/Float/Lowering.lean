module

public import Silmaril.Numeric.Float.Lowering.Compare
public import Silmaril.Numeric.Float.Lowering.Order
public import Silmaril.Numeric.Float.Lowering.Rounding
public import Silmaril.Numeric.Float.Lowering.Exact

/-!
# Architecture-independent lemmas for lowering WebAssembly floating point

Facts about the numeric layer that verified instruction sequences for
WebAssembly `f32`/`f64` operators need on any instruction set, collected in the
namespace `Silmaril.Numeric.Float.Lowering`:

* `Lowering.Compare`: `UnpackedFloat.compare` on decoded encodings (unordered
  exactly for NaN operands), `Admits` away from NaN, and the binary32/binary64
  zero encodings.
* `Lowering.Order`: the numerical order of decoded encodings as the order of an
  extended rational value (`ext`), the range in which truncation to an integer
  format succeeds (`fromFloat_isSome_iff`), the non-strict form of a range check
  at a power-of-two bound (`le_iff_pred_lt`), and saturation (`sat_high`, …).
* `Lowering.Rounding`: the executable rounding depends only on the value
  (`roundUnpacked_congr`) and, for integers, only on the high bits and a sticky
  bit (`roundUnpacked_ofInt_sticky`).
* `Lowering.Exact`: representable values are packed unchanged, and without
  flushing the profile's addition, subtraction and conversion are the core
  rounding of the exact result (`binary_value`, `convert_value`).

`Silmaril.X86.Float.Wasm` uses them for x86-64 SSE; nothing here depends on an
instruction set.
-/
