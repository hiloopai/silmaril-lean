module

public import Silmaril.Wasm.Jco.Fuse.Defs

/-!
# Glue modules as base modules

To check that the semantic fusion `fuseSem` is realised by a code
transformation, take glue modules themselves as the base modules: `Glue` is a
`CoreModule` and `glueSem : CoreSem Glue` interprets a glue module by its
handler. A fused module `JMod.fused g₁ g₂` is then compared with the inlined
module `JMod.glue (Glue.inline g₁ g₂)` (`Silmaril.Wasm.Jco.Fuse.Inline.Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Fuse

open Silmaril.Games
open Silmaril.Wasm.Component

instance : CoreModule Glue where
  imports := Glue.imports
  exports := Glue.exports

/-- Glue modules denote their handlers. -/
def glueSem : CoreSem Glue where
  sem g := Strategy.ofHandler g.handler

end Silmaril.Wasm.Jco.Fuse
