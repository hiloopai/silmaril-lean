module

public import Silmaril.Wasm.Category.Institution.Defs
public import Silmaril.Wasm.Institution.Components.Thms
public import Silmaril.Wasm.Component.Reference.Core3Sem.Thms
public import Silmaril.Compile.Category.PassAPI

@[expose] public section

/-!
# Components as languages

Silmaril's component IR (`Silmaril.Wasm.Component`) is denoted parametrically in a core semantics
`C : CoreSem M`. Two languages of the category of Wasm programs, for every `C`:

* `compLang C`: components, observed by the plays of their strategy over `sigU`;
* `modCompLang C`: core modules seen as components, observed by the plays of `modU C m` (the
  module's strategy between the boundary masks of the component IR).

The category of Wasm programs instantiates `C` with the Core 3.0 core semantics
`Silmaril.Wasm.Component.Reference.core3Sem P` (owned by `Silmaril.Wasm.Component.Reference`, reused
here): numeric Core 3.0 instances, each denoting its Core 3.0 strategy
`ScalarInstance.strategy P` between the canonical-ABI boundary adapters.

What is not proved (here or in `Silmaril.Wasm.Component.Reference`): that the boundary adapters
are faithful, i.e. that the closed-world observations of `(core3Sem P).sem m`, at payloads
encoding typed values, are the Core 3.0 behaviours of the instance; so the component objects
are not connected by morphisms to the closed-world objects.
-/

namespace Silmaril.Wasm.Category

open CategoryTheory Silmaril.Compile.Category Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Component
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

/-- **Components observed by the plays of their strategy**, for a core semantics `C`. -/
abbrev compLang {M : Type} [CoreModule M] (C : CoreSem M) : Language.{0} where
  Iface := Unit
  Prog := Comp M
  iface _ := ()
  Obs := List (Move sigU sigU)
  beh c := {s | s ∈ c.denU C}

/-- **Core modules as components**: the plays of `modU C m` (the module's strategy between the
boundary masks of the component IR). -/
abbrev modCompLang {M : Type} [CoreModule M] (C : CoreSem M) : Language.{0} where
  Iface := Unit
  Prog := M
  iface _ := ()
  Obs := List (Move sigU sigU)
  beh m := {s | s ∈ Silmaril.Wasm.Institution.Components.modU C m}

end Silmaril.Wasm.Category
