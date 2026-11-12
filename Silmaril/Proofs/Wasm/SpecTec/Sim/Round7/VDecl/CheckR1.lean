module

public import Silmaril.Wasm.SpecTec.Sim.Round7.VDecl.Defs

/-!
# Round 7, memory SIMD: the rules `Step` reaches, by the kernel (chunk 1)

One kernel computation (`decide +kernel`, kernel reduction, no native code) over relations 40–49 of the fixed wasm-3.0 script:
every relation `Step` reaches has no parameters, and each of its rules has `RG` quantifier types
and `RG` conclusion alternatives (`Round7.VDecl.relFactsB`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VDecl

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000

/-- **The relations `Step` reaches have no parameters, `RG` quantifier types and `RG` conclusion
alternatives.** -/
theorem relFacts_chunk1 :
    relFactsB (((relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed).drop 40).take 10) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.VDecl
