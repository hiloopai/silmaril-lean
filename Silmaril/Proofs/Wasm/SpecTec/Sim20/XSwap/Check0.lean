module

public import Silmaril.Wasm.SpecTec.Sim20.XSwap.Defs
public import Silmaril.Wasm.SpecTec.Sim20.StoreFix.Defs

/-!
# the 2.0 script passes the re-encoding check: chunks 0–4

Kernel computations (`decide +kernel`, no native evaluation) on the top-level definitions 0–124 of
the corrected 2.0 script `StoreFix.fixedT20`: every definition of `gd20` and every relation of
`gr20` passes `xDefOk`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll

set_option maxRecDepth 100000

/-- Chunk 0 of the check of the corrected 2.0 script. -/
theorem xScript20_chunk00 :
    ((Silmaril.Wasm.SpecTec.Sim20.StoreFix.fixedT20.drop 0).take 25).all (xDefOk gr20 gd20) = true := by
  decide +kernel

/-- Chunk 1 of the check of the corrected 2.0 script. -/
theorem xScript20_chunk01 :
    ((Silmaril.Wasm.SpecTec.Sim20.StoreFix.fixedT20.drop 25).take 25).all (xDefOk gr20 gd20) = true := by
  decide +kernel

/-- Chunk 2 of the check of the corrected 2.0 script. -/
theorem xScript20_chunk02 :
    ((Silmaril.Wasm.SpecTec.Sim20.StoreFix.fixedT20.drop 50).take 25).all (xDefOk gr20 gd20) = true := by
  decide +kernel

/-- Chunk 3 of the check of the corrected 2.0 script. -/
theorem xScript20_chunk03 :
    ((Silmaril.Wasm.SpecTec.Sim20.StoreFix.fixedT20.drop 75).take 25).all (xDefOk gr20 gd20) = true := by
  decide +kernel

/-- Chunk 4 of the check of the corrected 2.0 script. -/
theorem xScript20_chunk04 :
    ((Silmaril.Wasm.SpecTec.Sim20.StoreFix.fixedT20.drop 100).take 25).all (xDefOk gr20 gd20) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll
