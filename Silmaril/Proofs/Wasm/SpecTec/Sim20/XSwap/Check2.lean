module

public import Silmaril.Wasm.SpecTec.Sim20.XSwap.Defs
public import Silmaril.Wasm.SpecTec.Sim20.StoreFix.Defs

/-!
# the 2.0 script passes the re-encoding check: chunks 10–14

Kernel computations (`decide +kernel`, no native evaluation) on the top-level definitions 250–374 of
the corrected 2.0 script `StoreFix.fixedT20`: every definition of `gd20` and every relation of
`gr20` passes `xDefOk`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll

set_option maxRecDepth 100000

/-- Chunk 10 of the check of the corrected 2.0 script. -/
theorem xScript20_chunk10 :
    ((Silmaril.Wasm.SpecTec.Sim20.StoreFix.fixedT20.drop 250).take 25).all (xDefOk gr20 gd20) = true := by
  decide +kernel

/-- Chunk 11 of the check of the corrected 2.0 script. -/
theorem xScript20_chunk11 :
    ((Silmaril.Wasm.SpecTec.Sim20.StoreFix.fixedT20.drop 275).take 25).all (xDefOk gr20 gd20) = true := by
  decide +kernel

/-- Chunk 12 of the check of the corrected 2.0 script. -/
theorem xScript20_chunk12 :
    ((Silmaril.Wasm.SpecTec.Sim20.StoreFix.fixedT20.drop 300).take 25).all (xDefOk gr20 gd20) = true := by
  decide +kernel

/-- Chunk 13 of the check of the corrected 2.0 script. -/
theorem xScript20_chunk13 :
    ((Silmaril.Wasm.SpecTec.Sim20.StoreFix.fixedT20.drop 325).take 25).all (xDefOk gr20 gd20) = true := by
  decide +kernel

/-- Chunk 14 of the check of the corrected 2.0 script. -/
theorem xScript20_chunk14 :
    ((Silmaril.Wasm.SpecTec.Sim20.StoreFix.fixedT20.drop 350).take 25).all (xDefOk gr20 gd20) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll
