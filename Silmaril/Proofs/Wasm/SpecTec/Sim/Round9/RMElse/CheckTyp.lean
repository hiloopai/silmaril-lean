module

public import Silmaril.Wasm.SpecTec.Sim.Round9.RMElse.Defs

/-!
# Round 9, rm: the kernel check on the `CODE`-free type names

`goodTypsC_fixed` (`decide +kernel`): every type of the fixed wasm-3.0 script named in `goodC`
has instance bodies without a `CODE` field whose types are named in `goodC`. `expandNC`: every
rule of `Expand` concludes a pair of quantifiers of such types.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMElse

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000 in
/-- **The `goodC` types of the fixed script are `CODE`-free.** -/
theorem goodTypsC_fixed : goodTypsC (typsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **`Expand` concludes `CODE`-free values.** -/
theorem expandNC : relNC (Silmaril.SpecTec.Sem.relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed)
    "Expand" = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round9.RMElse
