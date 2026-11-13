module

public import Silmaril.Wasm.JcoTool.KDrop.Defs
public import Silmaril.Wasm.JcoTool.KCoreEmit.Defs

/-!
# The generator behind `wasm-jco kcore`

`wasm-jco kcore NAME KERNEL N` prints (or encodes) the core module of the drop-aware generator
`KDrop.genD` (`docs/projects/wasm-components.md`, *asyncmodel, an earlier step*). The generator ,
`KCore.gen`, is kept as a documented baseline behind `--baseline`: it is correct over the
`Async` model, and traps in chains under the Component Model's drop behaviour.

`toolGen base k N` is the program the tool emits; `KCoreEmit.watChecked`, `watOf` and `wasmOf`
turn it into text and bytes (theorems in `KDropEmit.Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KDropEmit

open Silmaril.Wasm.JcoTool.KCore (Prog)
open Silmaril.Wasm.Component.Streams.Kernel (KM)

/-- The program `wasm-jco kcore` emits: `KDrop.genD k N`, or with `--baseline` (`base = true`)
`KCore.gen k N`. -/
def toolGen (base : Bool) (k : KM) (N : Nat) : Prog :=
  if base then KCore.gen k N else KDrop.genD k N

end Silmaril.Wasm.JcoTool.KDropEmit
