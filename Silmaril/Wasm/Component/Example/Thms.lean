module

public import Silmaril.Wasm.Component.Example.Defs
public import Silmaril.Wasm.Component.Pipeline.Thms

/-!
# The example: soundness instances

For *every* core semantics `C` (for instance `toySem`):

* adapter fusion on the nested example preserves its strategy
  (unconditional);
* the full optimiser (flattening, fusion across the component boundary, dead
  instance elimination) preserves it (`parent_optimize'`; `parent_optimize`
  takes the pairing laws as an argument).
-/

public section

namespace Silmaril.Wasm.Component.Example

open Silmaril.Wasm.Component

theorem parent_fuse (C : CoreSem Toy) (ft : FuncTy) :
    (fuseComponent (parent ft)).denU C = (parent ft).denU C :=
  denU_fuseComponent C _

theorem parent_optimize (L : PairLaws) (C : CoreSem Toy) (ft : FuncTy) :
    (optimizeComponent (parent ft)).denU C = (parent ft).denU C :=
  (optimizeComponent_sound L C _).1

theorem parent_optimize' (C : CoreSem Toy) (ft : FuncTy) :
    (optimizeComponent (parent ft)).denU C = (parent ft).denU C :=
  (optimizeComponent_sound' C _).1

end Silmaril.Wasm.Component.Example
