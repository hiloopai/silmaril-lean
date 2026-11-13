module

public import Silmaril.Wasm.SpecTec.Sim20.XSwap.Defs
public import Silmaril.Wasm.SpecTec.Sim20.StoreFix.Defs

/-!
# the 2.0 script passes the re-encoding check: chunks 5–9

Kernel computations (`decide +kernel`, no native evaluation) on the top-level definitions 125–249 of
the corrected 2.0 script `StoreFix.fixedT20`: every definition of `gd20` and every relation of
`gr20` passes `xDefOk`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll

set_option maxRecDepth 100000

/-- Chunk 5 of the check of the corrected 2.0 script. -/
theorem xScript20_chunk05 :
    ((Silmaril.Wasm.SpecTec.Sim20.StoreFix.fixedT20.drop 125).take 25).all (xDefOk gr20 gd20) = true := by
  decide +kernel

/-- Chunk 6 of the check of the corrected 2.0 script. -/
theorem xScript20_chunk06 :
    ((Silmaril.Wasm.SpecTec.Sim20.StoreFix.fixedT20.drop 150).take 25).all (xDefOk gr20 gd20) = true := by
  decide +kernel

/-- Chunk 7 of the check of the corrected 2.0 script. -/
theorem xScript20_chunk07 :
    ((Silmaril.Wasm.SpecTec.Sim20.StoreFix.fixedT20.drop 175).take 25).all (xDefOk gr20 gd20) = true := by
  decide +kernel

/-- Chunk 8 of the check of the corrected 2.0 script. -/
theorem xScript20_chunk08 :
    ((Silmaril.Wasm.SpecTec.Sim20.StoreFix.fixedT20.drop 200).take 25).all (xDefOk gr20 gd20) = true := by
  decide +kernel

/-- Chunk 9 of the check of the corrected 2.0 script. -/
theorem xScript20_chunk09 :
    ((Silmaril.Wasm.SpecTec.Sim20.StoreFix.fixedT20.drop 225).take 25).all (xDefOk gr20 gd20) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll
