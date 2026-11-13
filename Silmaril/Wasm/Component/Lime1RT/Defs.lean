module

public import Silmaril.Wasm.Component.Lime1G.Defs
public import Silmaril.Wasm.Models.Runtime.Defs

/-!
# Core 3.0 restricted to Lime1 at runtime: definitions

`Lime1G.core3LG P` restricts `core3P P` to the modules of `lime1` through `Valid` only (its
runtime invariant `Rt` is `True`). Neither the component machine nor `engineSem` consults
`Valid`, so that restriction does not constrain any run: every internal step of `core3P P` is
an internal step of `core3LG P`.

`lime1RT P` is the restriction that also constrains runs: an internal step must land in a
configuration whose code and store functions are of `lime1` (the runtime invariant
`Silmaril.Wasm.Models.Rt.InFeat lime1` of the thread's Core configuration). `core3LRG P` is the
resulting game engine. `Lime1RT.Thms` shows that the invariant is closed under the Core 3.0
internal step, that the restricted engine is sound for the reference component machine (through
the hereditary properties of `Silmaril.Wasm.Component.Hered`), and that its game semantics is that
of Core 3.0 on every instance whose store is of `lime1`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Lime1RT

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Numerics (Profile)

/-- The runtime invariant of `lime1` on a Core 3.0 engine configuration: the Core configuration
denoted by the thread has code and store functions of `lime1`. -/
def RtL {H : Type}
    (c : Silmaril.Wasm.Execution.Core.Store H × Silmaril.Wasm.SingleThreaded.Thread) : Prop :=
  Silmaril.Wasm.Models.Rt.InFeat Silmaril.Wasm.Models.lime1 (c.2.config c.1)

/-- **The restriction of Core 3.0 to `lime1` at runtime**: modules of `lime1`, and internal steps
landing in the runtime invariant of `lime1`. -/
noncomputable def lime1RT (P : Profile) : Restriction (core3P P) where
  Mod m := Silmaril.Wasm.Models.Module.InFeat Silmaril.Wasm.Models.lime1 m
  Rt c := RtL c

/-- **Core 3.0 restricted to `lime1` at runtime, as a game engine.** -/
noncomputable def core3LRG (P : Profile) : GameEngine where
  E := restrict (core3P P) (lime1RT P)
  lawful := restrict_lawful
  abi := @AbiLawful.ofLawful _ restrict_lawful
  M := NumModule
  core := inferInstance
  emb := NumModule.mod

end Silmaril.Wasm.Component.Lime1RT
