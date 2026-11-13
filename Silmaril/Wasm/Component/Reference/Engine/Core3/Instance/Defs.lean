module

public import Silmaril.Wasm.Component.Reference.Engine.Core3.Store.Defs
public import Silmaril.Wasm.Component.Reference.Engine.Core3.StepLaws.Defs
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Typed.Defs
import Silmaril.Wasm.Component.Reference.Engine.Core3.Grows.Defs

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

theorem core3_externSub_refl {o : SingleThreaded.GrowOracle} (τ : (core3 o).ExternType) :
    (core3 o).ExternSub τ τ :=
  Validation.ExternSub.refl {} τ.1

theorem core3_externSub_trans {o : SingleThreaded.GrowOracle} {τ₁ τ₂ τ₃ : (core3 o).ExternType}
    (h₁ : (core3 o).ExternSub τ₁ τ₂) (h₂ : (core3 o).ExternSub τ₂ τ₃) :
    (core3 o).ExternSub τ₁ τ₃ :=
  Validation.ExternSub.trans Validation.TypeCtx.ok_empty τ₂.2 h₁ h₂

end Core3

/-- The concrete Core 3.0 engine satisfies the untyped engine laws. -/
instance core3_lawful (o : SingleThreaded.GrowOracle) : (core3 o).Lawful where
  flatType?_ofFlatType := SingleThreaded.flatType?_ofFlatType
  returned_no_step := statusE_returned_no_step
  callout_no_step := statusE_callout_no_step
  stuck_no_step := statusE_stuck_no_step
  externSub_refl := core3_externSub_refl
  externSub_trans := core3_externSub_trans
  asFunc?_ofFunc _ := rfl
  internal_extends h := (internal_grows h).extends
  prepare_extends := prepareE?_extends
  allocHost_extends := allocHost_extends
  allocHost_fresh := allocHost_fresh
  allocHost_frame := allocHost_frame
  allocHost_funcType := allocHost_funcType
  allocHost_callout := statusE_allocHost_callout
  memWrite_extends := memWrite?_extends
  memWrite_memSize := memWrite?_memSize
  memWrite_memAddrType := memWrite?_memAddrType
  memWrite_read := memWrite?_read
  memWrite_read_other := memWrite?_read_other
  memRead_isSome_iff := memRead?_isSome_iff
  memRead_size := memRead?_size
  memWrite_isSome_iff := memWrite?_isSome_iff
  memAddrType_isSome_iff := memAddrType?_isSome_iff

/-- The concrete Core 3.0 engine over grow oracle `o`. -/
def core3Engine (o : SingleThreaded.GrowOracle) : Core3Engine where
  E := core3 o
  modules := Equiv.refl _
  funcTypes := Equiv.refl _
  externTypes := Equiv.refl _
  ofFlatType_eq _ := rfl
  flatType?_eq _ := rfl
  externSub_iff _ _ := Iff.rfl
  valid_iff _ := Iff.rfl
  importTypes_eq _ _ h := importTypesE_eq h
  exportTypes_eq _ _ h := exportTypesE_eq h
  lawful := core3_lawful o
  typed := core3Typed o

end Silmaril.Wasm.Component.Engine
