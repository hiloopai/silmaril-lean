module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HAgree.Defs

/-!
# Round 7, `BD`: the rules `Step` reaches, by the kernel (chunk 2)

One kernel computation (`decide +kernel`, kernel reduction, no native code) over the relations from 80 on of the fixed wasm-3.0 script:
every relation `Step` reaches has no parameters, and each of its rules has `RG` quantifier types
and `RG` conclusion alternatives (`Round7.HAgree.relFactsB`, `$hostcall` excluded).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HAgree

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000

/-- **The relations `Step` reaches have no parameters, `RG` quantifier types and `RG` conclusion
alternatives.** -/
theorem relFacts_chunk2 :
    relFactsB ((relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed).drop 80) = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.HAgree
