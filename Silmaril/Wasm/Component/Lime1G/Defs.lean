module

public import Silmaril.Wasm.Component.Param.Thms
public import Silmaril.Wasm.Component.Core3G.Defs
public import Silmaril.Wasm.Models.Syntax.Defs
public import Silmaril.Wasm.Component.Reference.Engine.Lime1.Properties.Defs

/-!
# Component instances for Lime1: the Lime1 engine and Core 3.0 restricted to `lime1`

Two game engines (`Silmaril.Wasm.Component.Param.GameEngine`) for Lime1 components:

* `lime1G`: **the Lime1 engine** `Silmaril.Wasm.Component.Engine.Lime1.lime1` (the copied
  `Engine/Lime1.lean`, which runs the Lime1 machine `Silmaril.Wasm.Lime1.Execution` through its
  callout view), with its laws `Engine.Lime1.lawful` (the copied `Engine/Lime1/Properties.lean`,
  `NumModule` (Core 3.0 syntax) through the canonical decoding `lime1Emb m`, which is
  `Lime1.Module.ofCore? m.mod` (the empty Lime1 module off its domain);
* `lime1R P`: the restriction of `core3P P` to the Core modules of `lime1`
  (`Module.InFeat lime1`), and `core3LG P`, **Core 3.0 restricted to `lime1`** as a game
  engine. Its laws pass from `core3P P` (`restrict_lawful`), and it inherits the soundness of
  the reference component machine from the I4/I5 restriction theorems
  (`Simple.sound_restrict_core3P` and `Linked2.sound_restrict_core3P`), see `Thms`.

New definitions over the copied engine.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Lime1G

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Numerics (Profile)

/-- The empty Lime1 module. -/
def emptyL : Silmaril.Wasm.Lime1.Module :=
  { types := [], imports := [], funcs := [], globals := [], tables := [], memories := [],
    elems := [], data := [], start := none, exports := [] }

/-- The Lime1 module of a numeric IR module: the canonical decoding of its Core syntax. -/
def lime1Emb (m : NumModule) : Silmaril.Wasm.Lime1.Module :=
  (Silmaril.Wasm.Lime1.Module.ofCore? m.mod).getD emptyL

/-- **The Lime1 game engine.** -/
def lime1G : GameEngine where
  E := Silmaril.Wasm.Component.Engine.Lime1.lime1
  lawful := Silmaril.Wasm.Component.Engine.Lime1.lawful
  abi := AbiLawful.ofLawful _
  M := NumModule
  core := inferInstance
  emb := lime1Emb

/-- The restriction of Core 3.0 to the modules of `lime1`. -/
noncomputable def lime1R (P : Profile) : Restriction (core3P P) where
  Mod m := Silmaril.Wasm.Models.Module.InFeat Silmaril.Wasm.Models.lime1 m
  Rt _ := True

/-- **Core 3.0 restricted to `lime1` as a game engine.** -/
noncomputable def core3LG (P : Profile) : GameEngine where
  E := restrict (core3P P) (lime1R P)
  lawful := restrict_lawful
  abi := @AbiLawful.ofLawful _ restrict_lawful
  M := NumModule
  core := inferInstance
  emb := NumModule.mod

end Silmaril.Wasm.Component.Lime1G
