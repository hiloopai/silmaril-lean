module

public import Silmaril.Wasm.Component.Passes.Fusion.Defs
public import Silmaril.Wasm.Component.Passes.Flatten.Defs
public import Silmaril.Wasm.Component.Passes.DeadInstance.Defs
public import Silmaril.Wasm.Component.Passes.DeadExport.Defs

/-!
# The component optimiser (executable)

* `optimizeLinked`: adapter fusion, then dead instance elimination, on the flat
  IR;
* `optimizeComponent : Comp M → Comp M`: flatten the nested components, run
  `optimizeLinked`, and embed the flat result back into the nested IR;
* `optimizeProgram`: dead export elimination for the observed exports, then
  `optimizeComponent`.

These are plain computable functions, the entry points for a driver. Their
soundness is in `Silmaril.Wasm.Component.Pipeline.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

variable {M : Type} [CoreModule M]

/-- Optimise a flat component: adapter fusion, then dead instance elimination. -/
def optimizeLinked (l : Linked M) : Linked M := deadInstances (fuseLinked l)

/-- **The component optimiser**: flatten, optimise, embed back. -/
def optimizeComponent (c : Comp M) : Comp M := (optimizeLinked (flatten c)).toComponent

/-- Optimise a program: keep the observed exports, then optimise the component. -/
def optimizeProgram (p : Program M) : Program M :=
  let p' := deadExports p
  { p' with comp := optimizeComponent p'.comp }

end Silmaril.Wasm.Component
