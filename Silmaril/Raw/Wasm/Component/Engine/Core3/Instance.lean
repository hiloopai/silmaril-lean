module

public import Silmaril.Wasm.Component.Reference.Engine.Core3.Instance.Defs

public import Silmaril.Raw.Wasm.Component.Engine.Core3.Store
public import Silmaril.Raw.Wasm.Component.Engine.Core3.StepLaws
public import Silmaril.Raw.Wasm.Component.Engine.Core3.Typed

/-!
# The concrete Core 3.0 engine is a `Core3Engine`

* `core3_lawful o : (core3 o).Lawful`: the untyped laws of `CoreEngine.Lawful`
  (Engine/Laws.lean), assembled from the store laws (Engine/Core3/Store.lean), the step laws
  (Engine/Core3/StepLaws.lean) and import matching by `ExternSub {}`, which is reflexive and,
  with a middle type valid in the empty context, transitive (`ExternSub.refl`,
  `ExternSub.trans`).
* `core3Engine o : Core3Engine`: the concrete engine with the identity equivalences on modules,
  function types and extern types; flat types, validity and import matching are the Core 3.0
  ones by definition, import and export types are the validator's (`importTypesE_eq`,
  `exportTypesE_eq`), and the typed laws are `core3Typed o` (Engine/Core3/Typed.lean).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine

open Silmaril.Wasm.Execution.Core Core3

namespace Core3

end Core3

end Silmaril.Wasm.Component.Engine
