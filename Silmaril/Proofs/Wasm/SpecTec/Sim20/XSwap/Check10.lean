module

public import Silmaril.Wasm.SpecTec.Sim20.XSwap.Defs
public import Silmaril.Wasm.SpecTec.Sim10.Utf8Fix.Defs

/-!
# the 1.0 script passes the re-encoding check

Kernel computations (`decide +kernel`, no native evaluation) on the 1.0 script with both errata,
`Utf8Fix.fixedU10`, in two halves: every definition of `gd10` and every relation of `gr10` passes
`xDefOk`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll

set_option maxRecDepth 100000

theorem fixedU10_length : Silmaril.Wasm.SpecTec.Sim10.Utf8Fix.fixedU10.length ≤ 175 * 2 := by
  decide +kernel

/-- The first half of the check of the 1.0 script. -/
theorem xScript10_chunk00 :
    ((Silmaril.Wasm.SpecTec.Sim10.Utf8Fix.fixedU10.drop 0).take 175).all (xDefOk gr10 gd10) = true := by
  decide +kernel

/-- The second half of the check of the 1.0 script. -/
theorem xScript10_chunk01 :
    ((Silmaril.Wasm.SpecTec.Sim10.Utf8Fix.fixedU10.drop 175).take 175).all (xDefOk gr10 gd10) =
      true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll
