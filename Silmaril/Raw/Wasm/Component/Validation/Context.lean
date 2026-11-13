module

public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Defs

public import Silmaril.Raw.Wasm.Component.Features
public import Silmaril.Raw.Wasm.Component.Syntax.Basic
public import Silmaril.Raw.Wasm.Component.Types.Basic
public import Silmaril.Wasm.Validation.DefTypes
import all Init.Data.String.Defs
import all Init.Data.Repr

/-!
# Validation context (the wasmparser `ComponentState` analogue)

Component validation is incremental over the ordered definition list. The state it threads is
wasmparser's `ComponentState` (`wasmparser/src/validator/component.rs`, lines 41-176); this
file transcribes that state as the plain-data record `Ctx X`, a stack of enclosing scopes `Scopes X`
for outer aliases, and the error type `ValidationError`.

Design decisions:

* **Resource variables are `Nat`.** Every semantic type stored here is a `Types/Basic.lean` type
  over `R := Nat` (`Types.TypeDef Nat X`, `Types.FuncType Nat`, ...). Fresh variables come from the
  counter `nextVar`; relational judgements may instead pick any variable with an explicit freshness
  side condition.
* **Core extern type parameter `X`.** `Ctx X` is parametric in the core extern type
  (`Engine.CoreExternType` for the V1/Lime1 profiles, closed extern types `Core3Extern` for the
  Core 3.0 profile), like the types of `Types/Basic.lean`. The core function space is not `List
  V1.FuncType`: because `Ctx` is parametric in `X` and a Core 3.0 core function aliased out of a
  core instance has a Core 3.0 type, *every* core entity space (`coreFuncs`, `coreTables`,
  `coreMems`, `coreGlobals`, `coreTags`) stores `X`; the invariant that `coreFuncs` holds
  function-kind extern types is maintained by the judgements. Canonical definitions whose core type
  is a flat `V1.FuncType` push its image under the profile's `ofFlatType` (`CoreEngine.ofFlatType`),
  passed by the judgement.
* **Core types.** `coreTypes` stores `CoreTypeSlot X`: member `k` of a Core 3.0 `rec` type
  group (`Silmaril.Wasm.RecType`, as in the syntax; a group of `n` subtypes occupies `n`
  consecutive core type indices, `CoreTypeSlot.ofRec`, as in `Binary.md` and wasmparser) or a
  validated, index-free core module type (`Types.CoreModuleType X`). A group member also
  carries its **closed** defined type (`DefType`): the group rolled at its first index and
  closed against the defined types of the slots before it (`CoreTypeSlot.closeRec`, one step of
  the Core 3.0 `$alloctypes`, `Execution.Core.allocTypes`, and of `Type_ok`'s
  `Context.rollGroup`). Type indices inside the syntactic group are relative to the space it
  was defined in; the closed type is not, so it survives `alias outer` into another core type
  space (a module type's local space) unchanged, and two slots of different spaces can be
  compared by Core 3.0 subtyping. A core module type slot has no defined type
  (`CoreTypeSlot.defType` gives the never-valid placeholder `default`, so a group referring to
  it closes to a type that is not valid, as wasmparser rejects "type index ... is a module
  type, not a sub type").
* **Type identity for external visibility.** A component type index holds a `TypeSlot X`
  `{def_, token}`: `def_` is the semantic type, `token` its naming identity (wasmparser
  `created` vs `referenced`; `Explainer.md` §External Visibility of Types). `importedTokens` and
  `exportedTokens` are wasmparser's `imported_types`/`exported_types`.
  Since an imported or exported instance names all of its exported types, recursively,
  an instance index holds an `InstanceSlot X` `{ty, tokens}` recording one token per
  type-export path (`["t"]`, or `["j", "u"]` for type `u` of nested instance export `j`).
  Identity rules provided here:
  - `pushType`/`pushInstance` (and `pushEntity`) allocate fresh tokens: a new identity that
    nothing names (a type definition, `instantiate`, `with_unique`).
  - `pushImportEntity`/`pushExportEntity` allocate fresh tokens *and* register them in
    `importedTokens`/`exportedTokens` (import/export of a type or of an instance).
  - `aliasInstanceExport?` (`alias export i "n"`) and `pushTypeSlot`/`pushInstanceSlot`
    (outer aliases, inline-export instances) *keep* the stored tokens, so aliasing a type out
    of an exported instance yields a named type while aliasing out of an unexported or
    instantiated one does not (`test/validation/external-visibility.wast` lines 408-454).
* **Names are `String`.** Import/export maps are `List (String × Entity Nat X)`, keyed by the
  canonical name strings used by the `ComponentType`/`InstanceType` lists, rather than
  `Syntax.ExternName`; name parsing, annotation handling and strong uniqueness belong to
  Syntax/Names.lean and the judgements.
* **No derived instances on `TypeSlot`, `InstanceSlot`, `Ctx`.** The mutual types
  `TypeDef`/`InstanceType`/`ComponentType` derive no `Repr`/`DecidableEq`, so these cannot
  derive them either; tests compare projections.
* **Features are a parameter of every judgement**, not a field of `Ctx` (the `Features` import
  is kept so that downstream judgements importing this file get it): the feature set is
  fixed for a whole validation run, and keeping it out of `Ctx` keeps scope entry/exit and
  the push/lookup lemmas feature-independent. Judgements take `(feat : Features)` as their
  first explicit argument (`ValidDefValType feat Γ`, `ValidDef feat ...`).
* **Index spaces are lists** extended at the end; every push returns the new index
  (= the old length). Lookups return `Option`; the `...At?` variants return
  `Except ValidationError` with the wasmparser "unknown ... index out of bounds" message.
* **Scopes.** `Scopes X := List (Ctx X)` holds the *enclosing* contexts, innermost first.
  `Scopes.enter` pushes the current context and starts a fresh one of the given `Kind`
  (a nested component definition, or a component/instance type declarator);
  `Scopes.exit?` pops it, handing the child's `nextVar`/`nextToken` back so that variables and
  tokens stay globally fresh. `outer?` resolves the count `ct` of `alias outer ct i`
  (0 = the current context).

Also provided: fresh variable/token allocation, the resource-tracking maps
(`importedRes`, `definedRes`, `explicitRes`), the visibility sets, the top-level resource name
maps for `[method]`/`[constructor]` annotation typing, `contextType` fixing, value consumption
(🪙 linearity), and lemmas for every push: a lookup of the returned index yields the pushed
item, the returned index is the old length of the space (`..._index`), and earlier indices
are unchanged (`..._lt`).

Error messages are wasmparser's (from `component.rs`, by the substrings the upstream corpus
`test/validation/*.wast` expects, e.g. "type index out of bounds", "invalid outer alias
count"); only the substrings matched by the corpus are claimed ("index out of bounds",
"type index out of bounds", "invalid outer alias count", "instance 0 has no export named
`t`"). The `valueConsumed` and
`contextTypeMismatch` texts are descriptive, not verified against wasmparser. The private imports
`import all Init.Data.String.Defs` / `Init.Data.Repr` expose `Nat.repr` so that the message
tests reduce in the kernel.

NOT modelled here: any validation rule, subtyping, strong name uniqueness (Syntax/Names.lean), and
the core type/validation contexts of core modules. -/

@[expose] public section

namespace Silmaril.Wasm.Component.Validation

open Silmaril.Wasm.Component.Types

/-! ## Errors -/

namespace ValidationError

end ValidationError

/-! ## Context -/

namespace CoreTypeSlot

variable {X : Type}

open Silmaril.Wasm.Validation (DefType rolldt liftRec Ty)

-- FLAG(statement-change): `ofRec` takes the preceding slots `prev` (to close the group).
end CoreTypeSlot

namespace InstanceSlot

variable {X : Type}

end InstanceSlot

namespace Ctx

variable {X : Type}

theorem pushList_get_lt {α : Type} (l : List α) (a : α) {i : Nat} (h : i < l.length) :
    (pushList l a).2[i]? = l[i]? := by
  simp [pushList, List.getElem?_append_left h]

theorem pushList_length {α : Type} (l : List α) (a : α) :
    (pushList l a).2.length = l.length + 1 := by
  simp [pushList]

/-! ### Fresh variables and tokens -/

/-! ### Pushes (each returns the new index) -/

/-! ### Lookups -/

/-! ### Lookups with wasmparser errors -/

/-! ### Values (🪙 linearity) -/

/-! ### Imports, exports, resources, visibility -/

/-! ### Push/lookup lemmas -/

section Lemmas

variable (Γ : Ctx X)

theorem pushType_nextToken (t : TypeDef Nat X) :
    (Γ.pushType t).2.nextToken = Γ.nextToken + 1 := rfl

/-- `pushInstance` records the tokens `nextToken, nextToken + 1, ...` for the type-export
paths, in order. -/
theorem pushInstance_tokens (t : InstanceType Nat X) :
    ((Γ.pushInstance t).2.instanceSlot? (Γ.pushInstance t).1).map (·.tokens) =
      some ((exportsTypePaths t.exports).zip
        (List.range' Γ.nextToken (exportsTypePaths t.exports).length)) := by
  simp [pushInstance, freshTokens, instanceSlot?, pushInstanceSlot, pushList]

/-- The returned index of every push is the old length of the space. -/
theorem pushCoreType_index (t : CoreTypeSlot X) :
    (Γ.pushCoreType t).1 = Γ.coreTypes.length := rfl
theorem pushCoreFunc_index (t : X) : (Γ.pushCoreFunc t).1 = Γ.coreFuncs.length := rfl
theorem pushCoreTable_index (t : X) : (Γ.pushCoreTable t).1 = Γ.coreTables.length := rfl
theorem pushCoreMem_index (t : X) : (Γ.pushCoreMem t).1 = Γ.coreMems.length := rfl
theorem pushCoreGlobal_index (t : X) : (Γ.pushCoreGlobal t).1 = Γ.coreGlobals.length := rfl
theorem pushCoreTag_index (t : X) : (Γ.pushCoreTag t).1 = Γ.coreTags.length := rfl
theorem pushCoreModule_index (t : CoreModuleType X) :
    (Γ.pushCoreModule t).1 = Γ.coreModules.length := rfl
theorem pushCoreInstance_index (t : List (String × X)) :
    (Γ.pushCoreInstance t).1 = Γ.coreInstances.length := rfl
theorem pushTypeSlot_index (s : TypeSlot X) : (Γ.pushTypeSlot s).1 = Γ.types.length := rfl
theorem pushType_index (t : TypeDef Nat X) : (Γ.pushType t).1 = Γ.types.length := rfl
theorem pushFunc_index (t : Types.FuncType Nat) : (Γ.pushFunc t).1 = Γ.funcs.length := rfl
theorem pushValue_index (t : Types.ValType Nat) : (Γ.pushValue t).1 = Γ.values.length := rfl
theorem pushInstanceSlot_index (s : InstanceSlot X) :
    (Γ.pushInstanceSlot s).1 = Γ.instances.length := rfl
theorem pushInstance_index (t : InstanceType Nat X) :
    (Γ.pushInstance t).1 = Γ.instances.length := rfl
theorem pushComponent_index (t : ComponentType Nat X) :
    (Γ.pushComponent t).1 = Γ.components.length := rfl

/-- Pushes preserve earlier indices. -/
theorem pushCoreType_coreType?_lt (t : CoreTypeSlot X) {i : Nat}
    (h : i < Γ.coreTypes.length) : (Γ.pushCoreType t).2.coreType? i = Γ.coreType? i :=
  pushList_get_lt _ _ h
theorem pushCoreFunc_coreFunc?_lt (t : X) {i : Nat} (h : i < Γ.coreFuncs.length) :
    (Γ.pushCoreFunc t).2.coreFunc? i = Γ.coreFunc? i := pushList_get_lt _ _ h
theorem pushCoreTable_coreTable?_lt (t : X) {i : Nat} (h : i < Γ.coreTables.length) :
    (Γ.pushCoreTable t).2.coreTable? i = Γ.coreTable? i := pushList_get_lt _ _ h
theorem pushCoreMem_coreMem?_lt (t : X) {i : Nat} (h : i < Γ.coreMems.length) :
    (Γ.pushCoreMem t).2.coreMem? i = Γ.coreMem? i := pushList_get_lt _ _ h
theorem pushCoreGlobal_coreGlobal?_lt (t : X) {i : Nat} (h : i < Γ.coreGlobals.length) :
    (Γ.pushCoreGlobal t).2.coreGlobal? i = Γ.coreGlobal? i := pushList_get_lt _ _ h
theorem pushCoreTag_coreTag?_lt (t : X) {i : Nat} (h : i < Γ.coreTags.length) :
    (Γ.pushCoreTag t).2.coreTag? i = Γ.coreTag? i := pushList_get_lt _ _ h
theorem pushCoreModule_coreModule?_lt (t : CoreModuleType X) {i : Nat}
    (h : i < Γ.coreModules.length) :
    (Γ.pushCoreModule t).2.coreModule? i = Γ.coreModule? i := pushList_get_lt _ _ h
theorem pushCoreInstance_coreInstance?_lt (t : List (String × X)) {i : Nat}
    (h : i < Γ.coreInstances.length) :
    (Γ.pushCoreInstance t).2.coreInstance? i = Γ.coreInstance? i := pushList_get_lt _ _ h
theorem pushTypeSlot_typeSlot?_lt (s : TypeSlot X) {i : Nat} (h : i < Γ.types.length) :
    (Γ.pushTypeSlot s).2.typeSlot? i = Γ.typeSlot? i := pushList_get_lt _ _ h
theorem pushType_typeSlot?_lt (t : TypeDef Nat X) {i : Nat} (h : i < Γ.types.length) :
    (Γ.pushType t).2.typeSlot? i = Γ.typeSlot? i := pushList_get_lt _ _ h
theorem pushType_type?_lt (t : TypeDef Nat X) {i : Nat} (h : i < Γ.types.length) :
    (Γ.pushType t).2.type? i = Γ.type? i := by
  simp [pushType, freshToken, type?, pushTypeSlot, pushList, List.getElem?_append_left h]
theorem pushFunc_func?_lt (t : Types.FuncType Nat) {i : Nat} (h : i < Γ.funcs.length) :
    (Γ.pushFunc t).2.func? i = Γ.func? i := pushList_get_lt _ _ h
theorem pushValue_value?_lt (t : Types.ValType Nat) {i : Nat} (h : i < Γ.values.length) :
    (Γ.pushValue t).2.value? i = Γ.value? i := pushList_get_lt _ _ h
theorem pushInstanceSlot_instanceSlot?_lt (s : InstanceSlot X) {i : Nat}
    (h : i < Γ.instances.length) :
    (Γ.pushInstanceSlot s).2.instanceSlot? i = Γ.instanceSlot? i := pushList_get_lt _ _ h
theorem pushInstance_instanceSlot?_lt (t : InstanceType Nat X) {i : Nat}
    (h : i < Γ.instances.length) :
    (Γ.pushInstance t).2.instanceSlot? i = Γ.instanceSlot? i := pushList_get_lt _ _ h
theorem pushInstance_instance?_lt (t : InstanceType Nat X) {i : Nat}
    (h : i < Γ.instances.length) : (Γ.pushInstance t).2.instance? i = Γ.instance? i := by
  simp [pushInstance, freshTokens, instance?, pushInstanceSlot, pushList,
    List.getElem?_append_left h]
theorem pushComponent_component?_lt (t : ComponentType Nat X) {i : Nat}
    (h : i < Γ.components.length) : (Γ.pushComponent t).2.component? i = Γ.component? i :=
  pushList_get_lt _ _ h

/-- A push increases the count of its sort by one. -/
theorem pushEntity_count (e : Entity Nat X) :
    (Γ.pushEntity e).2.count (match e.sort with
      | .module => .core .module_ | .func => .func | .value => .value | .type => .type
      | .instance => .instance_ | .component => .component) =
    Γ.count (match e.sort with
      | .module => .core .module_ | .func => .func | .value => .value | .type => .type
      | .instance => .instance_ | .component => .component) + 1 := by
  cases e <;>
    simp [pushEntity, Entity.sort, count, pushCoreModule, pushFunc, pushValue, pushType,
      freshToken, pushTypeSlot, pushInstance, freshTokens, pushInstanceSlot, pushComponent,
      pushList]

theorem freshVar_fst : Γ.freshVar.1 = Γ.nextVar := rfl
theorem freshVar_lt : Γ.freshVar.1 < Γ.freshVar.2.nextVar := Nat.lt_succ_self _

theorem consumeValue?_ok {i : Nat} {t : Types.ValType Nat} (h : Γ.value? i = some (t, false)) :
    ∃ Γ', Γ.consumeValue? i = .ok (t, Γ') ∧ Γ'.value? i = some (t, true) := by
  simp only [value?] at h
  refine ⟨{ Γ with values := Γ.values.set i (t, true) }, ?_, ?_⟩
  · simp [consumeValue?, h]
  · have hi : i < Γ.values.length := by
      rcases List.getElem?_eq_some_iff.mp h with ⟨hi, _⟩; exact hi
    simp [value?, hi]

end Lemmas

end Ctx

/-! ## Scope stack (outer aliases) -/

namespace Scopes

variable {X : Type}

theorem exit?_enter (sc : Scopes X) (Γ Γ' : Ctx X) (k : Kind)
    (h : Γ'.nextVar = Γ.nextVar ∧ Γ'.nextToken = Γ.nextToken) :
    exit? (enter sc Γ k).1 Γ' = some (sc, Γ) := by
  obtain ⟨h1, h2⟩ := h
  simp [enter, exit?, h1, h2]

theorem outer?_enter_one (sc : Scopes X) (Γ Γ' : Ctx X) (k : Kind) :
    outer? (enter sc Γ k).1 Γ' 1 = .ok Γ := rfl

theorem outer?_zero (sc : Scopes X) (Γ : Ctx X) : outer? sc Γ 0 = .ok Γ := rfl

end Scopes

/-! ## Tests: push/lookup round trips -/

section Tests

namespace Tests

theorem test_pushFunc_roundtrip :
    ((ctxTest0.pushFunc funcTypeTest).2.func? 0) = some funcTypeTest := rfl

theorem test_pushType_two :
    (let (i, g) := ctxTest0.pushType (.resource 7)
     let (j, g) := g.pushType (.val u32Test)
     (i, j, g.type? i, g.type? j, (g.typeSlot? j).map (·.token))) =
      (0, 1, some (.resource 7), some (.val u32Test), some 1) := rfl

theorem test_pushValue_consume :
    (match ((ctxTest0.pushValue u32Test).2.consumeValue? 0) with
     | .ok (t, g) => some (t, g.value? 0, g.allValuesConsumed)
     | .error _ => none) = some (u32Test, some (u32Test, true), true) := rfl

theorem test_consume_twice :
    errOf? (((ctxTest0.pushValue u32Test).2.consumeValue? 0).bind
      fun (_, g) => g.consumeValue? 0) = some (ValidationError.valueConsumed 0) := rfl

theorem test_funcAt_oob :
    errOf? (ctxTest0.funcAt? 3) = some (ValidationError.outOfBounds "function" "function" 3) :=
  rfl

theorem test_outOfBounds_message :
    (ValidationError.outOfBounds "function" "function" 3).message =
      "unknown function 3: function index out of bounds" := by decide +kernel

theorem test_valueConsumed_message :
    (ValidationError.valueConsumed 0).message = "value 0 cannot be used more than once" := by
  decide +kernel

theorem test_coreInstance_roundtrip :
    (let (i, g) := ctxTest0.pushCoreInstance [("f", ())]
     g.coreInstance? i) = some [("f", ())] := rfl

theorem test_scopes_outer :
    (let (sc, g) := Scopes.enter [] (ctxTest0.pushFunc funcTypeTest).2 .componentType
     let (_, g) := g.freshVar
     ((Scopes.outer? sc g 1).toOption.bind (·.func? 0),
      (Scopes.outer? sc g 2).toOption.isNone,
      (Scopes.exit? sc g).map (·.2.nextVar))) = (some funcTypeTest, true, some 1) := rfl

/-! External visibility through instance slots (`external-visibility.wast` lines 408-454):
aliasing a type out of an exported instance yields a token in `exportedTokens`; aliasing out of
the unexported inline-export instance, or out of an instantiated instance, does not. -/

/-- `(type $Rec ...) (instance $bag (export "t" (type $Rec))) (export $bag' "i" (instance
$bag))`, then `alias export $bag' "t"` and `alias export $bag "t"`. -/
theorem test_alias_exported_instance :
    (let (r, g) := ctxTest0.pushType (.val u32Test)
     let tok := ((g.typeSlot? r).map (·.token)).getD 0
     let (bag, g) := g.pushInstanceSlot ⟨bagTy, [(["t"], tok)]⟩
     let (bag', g) := g.pushExportEntity (.instance bagTy)
     match g.aliasInstanceExport? bag' "t", g.aliasInstanceExport? bag "t" with
     | .ok (j, g1), .ok (k, g2) => some (typeVis g1 j, typeVis g2 k, g1.exportedTokens)
     | _, _ => none) =
      some (some (1, true), some (0, false), [1]) := rfl

/-- `(instance $c (instantiate $C))` then `alias export $c "t"`: fresh, unnamed identity. -/
theorem test_alias_instantiated_instance :
    (let (c, g) := ctxTest0.pushInstance bagTy
     match g.aliasInstanceExport? c "t" with
     | .ok (j, g) => typeVis g j
     | .error _ => none) = some (0, false) := rfl

/-- Nested instance exports: importing `(instance (export "j" (instance (export "t" (type
...)))))` names the nested type; aliasing `j` then `t` recovers that name. -/
theorem test_alias_nested_imported :
    (let outer : InstanceType Nat Unit := ⟨[], [("j", .instance bagTy)]⟩
     let (i, g) := ctxTest0.pushImportEntity (.instance outer)
     match g.aliasInstanceExport? i "j" with
     | .ok (j, g) =>
       match g.aliasInstanceExport? j "t" with
       | .ok (k, g) => some ((g.typeSlot? k).map (fun s => g.importVisible s.token),
           g.importedTokens)
       | .error _ => none
     | .error _ => none) = some (some true, [0]) := rfl

theorem test_alias_no_export :
    errOf? (ctxTest0.pushInstance bagTy |>.2.aliasInstanceExport? 0 "u") =
      some (ValidationError.noExportNamed 0 "u") := rfl

theorem test_noExportNamed_message :
    (ValidationError.noExportNamed 0 "t").message = "instance 0 has no export named `t`" := by
  decide +kernel

theorem test_contextType :
    ((ctxTest0.setContextType? .i32).bind (·.setContextType? .i64)).toOption.isNone = true := by
  decide

end Tests

end Tests

end Silmaril.Wasm.Component.Validation
