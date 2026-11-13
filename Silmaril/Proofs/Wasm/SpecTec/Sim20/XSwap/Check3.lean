module

public import Silmaril.Wasm.SpecTec.Sim20.XSwap.Defs
public import Silmaril.Wasm.SpecTec.Sim20.StoreFix.Defs

/-!
# the 2.0 script passes the re-encoding check: chunks 15–19

Kernel computations (`decide +kernel`, no native evaluation) on the top-level definitions 375–499 of
the corrected 2.0 script `StoreFix.fixedT20`: every definition of `gd20` and every relation of
`gr20` passes `xDefOk`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll

set_option maxRecDepth 100000

/-- Chunk 15 of the check of the corrected 2.0 script. -/
theorem xScript20_chunk15 :
    ((Silmaril.Wasm.SpecTec.Sim20.StoreFix.fixedT20.drop 375).take 25).all (xDefOk gr20 gd20) = true := by
  decide +kernel

/-- Chunk 16 of the check of the corrected 2.0 script. -/
theorem xScript20_chunk16 :
    ((Silmaril.Wasm.SpecTec.Sim20.StoreFix.fixedT20.drop 400).take 25).all (xDefOk gr20 gd20) = true := by
  decide +kernel

/-- Chunk 17 of the check of the corrected 2.0 script. -/
theorem xScript20_chunk17 :
    ((Silmaril.Wasm.SpecTec.Sim20.StoreFix.fixedT20.drop 425).take 25).all (xDefOk gr20 gd20) = true := by
  decide +kernel

/-- Chunk 18 of the check of the corrected 2.0 script. -/
theorem xScript20_chunk18 :
    ((Silmaril.Wasm.SpecTec.Sim20.StoreFix.fixedT20.drop 450).take 25).all (xDefOk gr20 gd20) = true := by
  decide +kernel

/-- Chunk 19 of the check of the corrected 2.0 script. -/
theorem xScript20_chunk19 :
    ((Silmaril.Wasm.SpecTec.Sim20.StoreFix.fixedT20.drop 475).take 25).all (xDefOk gr20 gd20) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll
