module

public import Silmaril.Wasm.Component.Reference.Validation.Defs.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Defs

-- Kernel computation uses the body of the upstream derived instance.
import all Batteries.Data.Except

public import Silmaril.Raw.Wasm.Component.Validation.DefTypes
public import Silmaril.Raw.Wasm.Component.Validation.Builtins
public import Silmaril.Raw.Wasm.Component.Validation.CoreModules
public import Silmaril.Raw.Wasm.Component.Types.Subtype
public import Silmaril.Raw.Wasm.Component.Engine.Lime1
public import Silmaril.Raw.Wasm.Component.Engine.Core3.Structural
public import Silmaril.Wasm.V1.Validation.Modules
public import Silmaril.Wasm.V1.ToCore.DefTypes
public import Silmaril.Wasm.Validation.Check.Validate
public import Silmaril.Wasm.Validation.Subtyping.Decide
public import Silmaril.Raw.Wasm.Component.Wasm.Lime1.Validation.FromV1

/-!
# Validation of definitions (relational)

The per-definition rules of component validation, transcribing `Explainer.md`/`Binary.md` at
component-model `a25fc0b`
(https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/Explainer.md)
as wasmparser's `ComponentState` implements them (`validator/component.rs`:
`instantiate_core_module`, `instantiate_component`, `alias_*`, `add_import`, `add_export`,
`add_start`, `add_value`). The executable checker and its soundness are `Validation/Check.lean`.

## Judgements

* `ValidDef feat P validCore sc s d s'` for every `Syntax.Definition` kind, threading the
  definition state `DefState X`: the declarator state `DState X` of `Validation/DefTypes.lean` (the
  context `Ctx X` plus the naming table used for external visibility) and the naming requirements of
  the component functions and values defined so far (`DefState.funcReqs`/`valueReqs`, keyed by
  index), under enclosing scopes `sc`:
  - `core module`: the supplied core validator `validCore m = some mt`; push `mt`.
  - `core instance (instantiate m args)`: unique argument names, arguments are core
    instances, every import `((mod, name), x)` of `mt` is provided by argument `mod`'s export
    `name` at a core subtype (`P.extSub`, `CoreExternType.sub` for V1/Lime1); push `mt`'s
    exports. `core instance (export ...)`: unique names, runtime sorts only.
  - `core type`: `ValidCoreTypeDecl`; `type`: `ValidDefType` (resources allowed,
    `kind = component`); `canon lift`/`lower`: `ValidCanon`; builtins: `ValidBuiltin`
    (`Validation/Builtins.lean`).
  - nested `component`: its definitions in a fresh scope (`Scopes.enter`), finished
    (`ComponentDone`: all values consumed, closed type), its type (`componentTypeOfDefs`)
    pushed; counters and naming table come back (`DState.returnTo`).
  - `instance (instantiate c args)`: unique argument names; the arguments' entity types
    (`itemEntity?`) satisfy `c`'s imports under a substitution `f` moving only `c`'s
    ∀-variables (`Entity.ListSub`, the subtyping of `Types/Subtype.lean`); value arguments consumed;
    `c`'s ∃-variables are renamed to fresh variables `nextVar, ...`, recorded as `definedRes (v,
    none)` (not local: `resource.new`/`rep` reject them), and the instance is pushed with fresh
    (unnamed) tokens (`DState.instantiate`). `instance (export ...)`: valid, strongly unique names;
    exportable sorts; tokens of the referenced types/instances kept.
  - aliases: `alias export` of any sort (identities kept, `Ctx.aliasInstanceExport?`; an
    aliased function or value records the naming requirement `aliasReq`),
    `alias core export` (core sort checked by `P.coreSort`), `alias outer` of `type` (no
    resources across a component boundary, `crossesComponent`), `core type`, `core module`
    and `component`; other outer sorts have no rule.
  - `import`: `ValidImportDecl` (name validity, strong uniqueness, resolution,
    visibility against `importedTokens`, resource binding with paths, naming).
  - `export n it et?`: valid, strongly unique name; `it` has an exportable entity type; the
    ascription `Ascribe` holds (`(sub resource)` on a resource keeps the resource; otherwise
    the inferred type is an `Entity.Sub` subtype of the resolved ascription, which is then
    exported); no `borrow` in exported values; the naming requirement `exportReq` holds
    against `importedTokens ++ exportedTokens` (for unascribed `func`/`value` items: the
    requirement recorded when the index was created); every free resource variable of the
    exported type is introduced by a preceding import or export or by this export
    (`resNamed`, Binary.md "all resource types transitively used in the type of an export are
    introduced by a preceding `importdecl` or `exportdecl`"); a value item is consumed; newly
    exported resources are recorded in `explicitRes` with their paths.
  - 🪙 `start` (any number, Explainer §Start Definitions "components can call start
    functions at multiple points during instantiation"; arguments consumed with the parameter
    types; result arity) and `value` (type without handles, `stream`, `future`,
    `error-context`), both gated by `feat.values`.
* `ValidComponent feat P validCore c ct`: the definitions fold from the empty component state
  (`initState`), the result is finished, and `ct = componentTypeOfDefs`: ∀-binders the
  imported resources, ∃-binders the defined resources that are explicitly exported.
* Profiles `DefProfile X` (declarator hooks, builtin view, Boolean core extern subtyping, core
  sort): `lime1Profile` (`Engine.CoreExternType`) and `core3Profile` (`Core3Extern`).
  `ValidComponentLime1` / `ValidComponentV1` use `lime1ModuleType` / `v1ModuleType` and
  conjoin core `ModuleValid` of every (nested) core module; `ValidComponentCore3` types core
  modules with the Core 3.0 validator `validate?` (`core3ModuleType?`), so every core module of
  a valid Core 3.0 component is `ModuleValid` (`ValidComponent.core3_moduleValid`; the
  conjunct is implied, `validComponentCore3_iff`).

## Core module types and engines (amendment)

* `coreModuleTypeAgrees_lime1 : CoreModuleTypeAgrees Engine.Lime1.lime1
  lime1ResolvedModuleType`, where `lime1ResolvedModuleType` is `lime1ModuleType` on modules
  whose function type indices resolve (`FuncTypesResolve`), and
  `lime1ResolvedModuleType_of_valid`: on valid modules it is `lime1ModuleType`.
  **Deviation:** the unrestricted statement `CoreModuleTypeAgrees lime1 lime1ModuleType` is
  FALSE (`not_coreModuleTypeAgrees_lime1_unrestricted`): the engine's export types read the
  Lime1 validation context, whose function space drops unresolved functions and shifts
  indices (`unresolvedModule`). Users of `lime1ModuleType` as the Lime1 core validator
  (`ValidComponentLime1`, `Validation/Check.lean`) get the engine agreement only through the
  `ModuleValid` conjunct and `lime1ResolvedModuleType_of_valid`; making `lime1ModuleType` return
  `none` unless `FuncTypesResolve` holds would make the unrestricted statement true.
* `core3ModuleType?_spec`: the Core 3.0 module type is `validate?`'s `CModuleType`, named by
  the module's imports and exports; `Validation/Core3.lean` shows that it is the Core 3.0
  engine's (`coreModuleTypeAgrees_core3`) and exists exactly for valid modules
  (`core3ModuleType?_isSome_iff`).
* `ValidComponent.v1_toLime`: if a V1 component is valid with `v1ModuleType`, its Lime1
  image is valid with `lime1ModuleType` and the same type (`ValidComponent.mapCore`, from
  `v1ModuleType_toLime`); `ValidComponentV1.toLime` adds the core `ModuleValid` transfer
  (`V1.Validation.ModuleValid.toLime`). Only this direction is proved.

## Deviations and choices

* The judgements thread `DState X` (not `Ctx X`) and take a profile `P` besides `validCore`:
  external visibility needs the naming table, and canon/declarator rules need the profile's
  core views and hooks.
* **Core 3.0 extern types.** `ValidComponentCore3` works over `Core3Extern`, closed extern
  types valid in the empty context (`{τ : CExternType // ExternTypeOk {} τ}`, the Core 3.0
  engine's extern types), not `Silmaril.Wasm.ExternType`, whose type indices are relative to a
  module's type section. Module types come from `validate?`, which closes every type index
  against the module's defined types. Module-type declarations (`core type (module ...)`) are
  closed against the closed defined types of their core type space (`core3CoreExtern?`; a
  component-level `rec` group's members carry their closed defined types,
  `CoreTypeSlot.ofRec`, so an `alias outer` keeps their meaning), and every `rec` group must
  pass `Type_ok` against the preceding core types (`core3RecOk`). Core extern subtyping is
  Core 3.0 import subtyping `ExternSub {}` (limits, defined-type subtyping of functions,
  concrete reference types, tags), decided by its checker (`core3Profile_XSub_iff`).
  Deviations: a flat signature (`canon lift`/`lower`, destructors) is only read from a
  singleton final recursion group (`core3FlatType?`, as the Core 3.0 engine's `flatType?`),
  while wasmparser compares the expanded function type; module-type imports and exports are
  checked by `Externtype_ok` without core feature gates.
* **Visibility of exports.** Component functions and values carry no naming tokens in `Ctx`, so
  `DefState` records a naming requirement per function/value index when the index is created:
  `canon lift` the contents of its function type (`contentsOf`), `import` and ascribed `export`
  the requirement of the `externtype` (`descReq`), unascribed `export` the requirement of the
  exported item, `value` that of its `valtype`, `start` results that of the started function. A
  function or value obtained by `alias export i n` gets `aliasReq`: each of its resource
  variables that instance `i` exports as a type must be named by the token of that type export
  (the first one, if several), as in wasmparser, where the aliased item's type keeps the type ids
  of the instance's type exports and a later `(export "r" (type ...))` of the aliased resource
  names only the new type id (`with_unique`), so the item must be re-exported with an ascription
  over the exported type. The instance's types are otherwise structural, so `aliasReq` OVER-
  ACCEPTS unnamed `record`/`variant`/`enum`/`flags` types and resources the instance does not
  export as types (e.g. a child's imported resource, which wasmparser identifies with the
  instantiation argument's type id), and the functions/values inside an exported instance are not
  re-checked (wasmparser `all_valtypes_named` tracks type ids). It may REJECT a component
  wasmparser accepts when an instance exports the same resource under type exports of different
  visibility and the aliased item's type uses a visible one (possible only for inline-export
  instances and for a child re-exporting an imported resource). Unascribed `component` and `core
  module` exports have no requirement (closed types, as in wasmparser). Resources are
  additionally checked by variable (`resNamed`), independently of tokens, including the
  "preceding" order.
* **Start.** Any number of 🪙 `start` definitions is allowed, following the normative
  Explainer; wasmparser additionally rejects a second one ("component cannot have more than
  one start function"), a restriction not modelled (the checker, `Validation/Check.lean`, must
  follow the Explainer for `ValidComponent → check` agreement). `Ctx.hasStart` is still set.
* The import substitution of `instantiate` is existential (as in the subtyping relation); the
  checker must infer it from resource paths.
* Inline component instances (`instance (export ...)`) require valid and strongly unique names
  (wasmparser builds them with an empty name context; only uniqueness is modelled).
* NOT modelled: `[constructor]`/`[method]`/`[static]`/`[get]`/`[set]` annotation typing and
  the resource name contexts `importResNames`/`exportResNames` (left untouched); feature gates
  on names and attributes (🏷️ `implements`, 🪺, 🔗, 📡) and attribute uniqueness; decoding of
  🪙 value payloads (and their canonical-NaN rule); `explicit_resources` of instance types;
  wasmtime's root-instantiation relaxations; error messages.

## Tests

Kernel-checked or proved by inversion: the Explainer adder (`Explainer.md` §Canonical ABI, over
the V1 `CoreModules.addModule`) is valid with type `adderType` (`adder_valid`);
`instantiate` without an argument for an import is invalid (`instantiate_missing_import`);
an outer alias of a resource type across a component boundary is invalid
(`alias_outer_resource_rejected`); an unconsumed 🪙 value makes a component invalid
(`unconsumed_value_rejected`); instantiation allocates a fresh, non-local variable for a
defined resource (`instantiate_fresh_resource`); an unascribed func export whose recorded
naming requirement is not visible is invalid ("func not valid to be used as export",
`export_unnamed_func_rejected`), as is one using a resource not yet imported or exported
(`export_unnamed_resource_rejected`); under the Core 3.0 profile `thread.new-indirect` accepts
tables of `(ref null nofunc)`, `(ref func)` (64-bit), a closed concrete function type and
`funcref`, and rejects an `externref` table (`core3_newIndirect_tables`,
`not_validBuiltin_core3_newIndirect_externref`). Upstream `.wast` cases are not replayed here.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Validation

open Silmaril.Wasm.Component.Types
open Silmaril.Wasm.Component.Engine (CoreExternType CoreEngine)

/-! ## Core module types and the core engines -/

section CoreAgreement

/-- `filterMap` of a function defined on every element commutes with indexing. -/
theorem filterMap_getElem?_of_isSome {α β : Type} (g : α → Option β) :
    ∀ (l : List α), (∀ a ∈ l, (g a).isSome = true) →
      ∀ i : Nat, (l.filterMap g)[i]? = (l[i]?).bind g
  | [], _, i => by simp
  | a :: l, h, i => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h a (by simp))
    have ih := filterMap_getElem?_of_isSome g l (fun x hx => h x (by simp [hx]))
    cases i with
    | zero => simp [hb]
    | succ i => simp [hb, ih]

/-- The function space of the Lime1 validation context is the type-section image of the
imports-first function index space (unresolved entries dropped). -/
theorem lime1_moduleContext_funcs (m : Lime1.Module) :
    (Lime1.Validation.moduleContext m).funcs =
      m.functionTypes.filterMap fun t => m.types[t.toNat]? := by
  simp only [Lime1.Validation.moduleContext, Scalar.Module.functionTypes,
    Scalar.Module.importedFunctions, List.filterMap_append, List.filterMap_filterMap,
    List.filterMap_map]
  congr 1
  apply List.filterMap_congr
  intro i _
  cases i.desc <;> rfl

theorem lime1FuncTypesResolve_of_valid {m : Lime1.Module}
    (h : Lime1.Validation.ModuleValid m) : FuncTypesResolve m := by
  intro t ht
  simp only [Scalar.Module.functionTypes, Scalar.Module.importedFunctions, List.mem_append,
    List.mem_filterMap, List.mem_map] at ht
  rcases ht with ⟨i, hi, hd⟩ | ⟨f, hf, rfl⟩
  · obtain ⟨et, het, _⟩ := h.imports i hi
    cases hdesc : i.desc with
    | func idx =>
      rw [hdesc] at hd het
      simp only [Option.some.injEq] at hd
      subst hd
      simp only [Lime1.Validation.importType?, Option.map_eq_some_iff] at het
      obtain ⟨ft, hft, _⟩ := het
      simp [hft]
    | _ => rw [hdesc] at hd; simp at hd
  · obtain ⟨ft, hft⟩ := Lime1.Validation.ModuleValid.function_type_exists h hf
    simp [hft]

/-- The engine's import types are the ones of `lime1ModuleType` (no hypothesis needed). -/
theorem lime1ImportTypes_eq_engine (m : Lime1.Module) :
    lime1ImportTypes m = Engine.Lime1.importTypes m := by
  simp only [lime1ImportTypes, Engine.Lime1.importTypes]
  apply List.filterMap_congr
  intro i _
  simp only [scalarImportEntry?, Option.map_map]
  cases i.desc <;> simp [scalarImportType?, Lime1.Validation.importType?,
    Engine.Lime1.ofExternType, scalarTableType, scalarMemoryType, scalarGlobalType,
    Function.comp_def]

/-- Export types agree with the engine's when every function type resolves. -/
theorem lime1ExportTypes_eq_engine {m : Lime1.Module} (h : FuncTypesResolve m) :
    lime1ExportTypes m = Engine.Lime1.exportTypes m := by
  simp only [lime1ExportTypes, Engine.Lime1.exportTypes]
  apply List.filterMap_congr
  intro e _
  simp only [scalarExportEntry?]
  cases e.index with
  | func i =>
    have hc := lime1_moduleContext_funcs m
    have hg := filterMap_getElem?_of_isSome (fun t : TypeIdx => m.types[t.toNat]?)
      m.functionTypes (fun a ha => h a ha) i.toNat
    simp only [scalarExportType?, Lime1.Validation.exportType?, hc, hg,
      Scalar.Module.functionType?, Option.bind_eq_bind, Option.map_map]
    cases m.functionTypes[i.toNat]? <;> simp [Function.comp_def, Engine.Lime1.ofExternType]
  | table i =>
    simp only [scalarExportType?, Lime1.Validation.exportType?, Option.map_map]
    rfl
  | memory i =>
    simp only [scalarExportType?, Lime1.Validation.exportType?, Option.map_map]
    rfl
  | global i =>
    simp only [scalarExportType?, Lime1.Validation.exportType?, Option.map_map]
    rfl

/-- `lime1ModuleType` agrees with the Lime1 engine's `importTypes`/`exportTypes` on every
module whose function types resolve (in particular on every valid module). -/
theorem lime1ModuleType_agrees {m : Lime1.Module} (hr : FuncTypesResolve m)
    {t : CoreModuleType CoreExternType} (h : lime1ModuleType m = some t) :
    t.imports.map (fun p => (p.1.1, p.1.2, p.2)) = Engine.Lime1.lime1.importTypes m ∧
      t.exports = Engine.Lime1.lime1.exportTypes m := by
  obtain ⟨hi, he⟩ := lime1ModuleType_importTypes m t h
  exact ⟨hi.trans (lime1ImportTypes_eq_engine m), he.trans (lime1ExportTypes_eq_engine hr)⟩

/-- The Lime1 engine agrees with the (resolving) Lime1 module type (the statement
`Validation/CoreModules.lean` leaves out). -/
theorem coreModuleTypeAgrees_lime1 :
    CoreModuleTypeAgrees Engine.Lime1.lime1 lime1ResolvedModuleType := by
  intro m t h
  simp only [lime1ResolvedModuleType] at h
  split at h
  · next hr => exact lime1ModuleType_agrees hr h
  · cases h

/-- On valid modules the resolving and the plain module type coincide. -/
theorem lime1ResolvedModuleType_of_valid {m : Lime1.Module}
    (h : Lime1.Validation.ModuleValid m) : lime1ResolvedModuleType m = lime1ModuleType m := by
  simp [lime1ResolvedModuleType, lime1FuncTypesResolve_of_valid h]

/-- Why the resolution hypothesis is needed: without it the agreement fails. -/
theorem not_coreModuleTypeAgrees_lime1_unrestricted :
    ¬ CoreModuleTypeAgrees Engine.Lime1.lime1 lime1ModuleType := by
  intro h
  have h1 : lime1ModuleType unresolvedModule = some ⟨[], [("f", .func ⟨[], []⟩)]⟩ := rfl
  have h2 : Engine.Lime1.lime1.exportTypes unresolvedModule = [] := rfl
  have := (h unresolvedModule _ h1).2
  rw [h2] at this
  cases this

end CoreAgreement

/-! ## Profiles -/

/-! ### The Core 3.0 profile

Core extern types are closed extern types valid in the empty context (`Core3Extern`), the
extern types of the concrete Core 3.0 engine (`Engine.core3`, `Engine.Core3.ExtT`). Module-type
declarations are closed against the closed defined types of their core type space
(`core3CoreExtern?`); recursion groups must pass `Type_ok` (`core3RecOk`); core extern
subtyping is `ExternSub {}` decided by its checker (`core3Profile_XSub_iff`); core modules
are typed by the Core 3.0 validator `validate?` (`core3ModuleType?`). -/

section Core3

open Wasm.Validation (CExternType ExternTypeOk DefType CValType)

/-- Closing a recursion group after closed types `dts` is `Type_ok`'s rolling of the group in
the context of `dts` (`Context.rollGroup`). -/
theorem CoreTypeSlot.closeRec_eq_rollGroup (dts : List DefType) (r : Wasm.RecType) :
    CoreTypeSlot.closeRec dts r = Wasm.Validation.Context.rollGroup { types := dts } r := rfl

theorem CoreTypeSlot.length_closeRec (dts : List DefType) (r : Wasm.RecType) :
    (CoreTypeSlot.closeRec dts r).length = r.types.length :=
  Wasm.Validation.Context.length_rollGroup { types := dts } r

/-- The slots of a recursion group carry exactly its closed defined types. -/
theorem CoreTypeSlot.defTypes_ofRec {X : Type} (prev : List (CoreTypeSlot X)) (r : Wasm.RecType) :
    CoreTypeSlot.defTypes (CoreTypeSlot.ofRec prev r) =
      CoreTypeSlot.closeRec (CoreTypeSlot.defTypes prev) r := by
  apply List.ext_getElem
  · simp [CoreTypeSlot.defTypes, CoreTypeSlot.length_closeRec]
  · intro i _ h2
    have h2' : i < (CoreTypeSlot.closeRec (prev.map CoreTypeSlot.defType) r).length := h2
    simp [CoreTypeSlot.defTypes, CoreTypeSlot.ofRec, CoreTypeSlot.defType,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2']

/-- An admitted recursion group extends the closed types of `prev` as `Types_ok` does: its
closed defined types are the ones of `Type_ok` in the context of the preceding types. -/
theorem core3RecOk_sound {X : Type} {prev : List (CoreTypeSlot X)} {r : Wasm.RecType}
    (h : core3RecOk prev r = true) :
    Wasm.Validation.TypesOk { types := CoreTypeSlot.defTypes prev } [r]
      (CoreTypeSlot.closeRec (CoreTypeSlot.defTypes prev) r) := by
  have h' := Wasm.Validation.TypesOk.cons (C := { types := CoreTypeSlot.defTypes prev }) (rts := [])
    (Wasm.Validation.RecTypeOkAt.check_sound h) .nil
  rwa [List.append_nil] at h'

/-- An admitted recursion group's slots carry the defined types `Types_ok` assigns to it after
the preceding types. -/
theorem core3RecOk_defTypes {X : Type} {prev : List (CoreTypeSlot X)} {r : Wasm.RecType}
    (h : core3RecOk prev r = true) :
    Wasm.Validation.TypesOk { types := CoreTypeSlot.defTypes prev } [r]
      (CoreTypeSlot.defTypes (CoreTypeSlot.ofRec prev r)) := by
  rw [CoreTypeSlot.defTypes_ofRec]
  exact core3RecOk_sound h

theorem core3NumOf?_mapM (ts : List NumType) :
    (ts.map Wasm.Validation.Ty.num).mapM core3NumOf? = some ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [List.mapM_cons, ih, core3NumOf?]

theorem core3FlatType?_toDefType (ft : V1.FuncType) : core3FlatType? ft.toDefType = some ft := by
  have hf : ft.toDefType.funcType? =
      some (ft.params.map Wasm.Validation.Ty.num, ft.results.map Wasm.Validation.Ty.num) := by
    simp [Wasm.Validation.DefType.funcType?, V1.FuncType.toDefType_expand]
  simp only [core3FlatType?, hf, Option.bind_eq_bind, Option.bind_some, core3NumOf?_mapM]
  simp

theorem core3FlatType?_sound {d : DefType} {ft : V1.FuncType} (h : core3FlatType? d = some ft) :
    ft.toDefType = d := by
  unfold core3FlatType? at h
  simp only [Option.bind_eq_bind] at h
  cases hd : d.funcType? with
  | none => simp [hd] at h
  | some p =>
    rcases p with ⟨ps, rs⟩
    simp only [hd, Option.bind_some] at h
    cases hp : ps.mapM core3NumOf? with
    | none => simp [hp] at h
    | some ps' =>
      cases hr : rs.mapM core3NumOf? with
      | none => simp [hp, hr] at h
      | some rs' =>
        simp only [hp, hr, Option.bind_some] at h
        split at h
        · rename_i heq; simp only [Option.some.injEq] at h; subst h; exact heq
        · simp at h

/-- `core3FuncTable?` accepts exactly the tables whose element type is a reference subtype of
`(ref null func)` (`Sub.check_iff`: the element type is valid by `Tabletype_ok`). -/
theorem core3FuncTable?_eq_some_iff {x : Core3Extern} {a : AddrType} :
    core3FuncTable? x = some a ↔ ∃ t, x.1 = .table t ∧ t.address = a ∧
      Wasm.Validation.Sub {} t.element Wasm.Validation.Ty.funcref := by
  obtain ⟨τ, hτ⟩ := x
  cases τ with
  | table t =>
    have hok : Wasm.Validation.TyOk {} t.element := by cases hτ with | table h => exact h.2
    have hf : Wasm.Validation.TyOk {} Wasm.Validation.Ty.funcref := .ref (.abs _)
    have hiff := Wasm.Validation.Sub.check_iff Wasm.Validation.TypeCtx.ok_empty rfl hok hf
    simp only [core3FuncTable?]
    split <;> rename_i h <;> simp_all
  | _ => simp [core3FuncTable?]

/-- Core extern subtyping of the Core 3.0 profile is `ExternSub {}` (sound by
`ExternSub.check_sound`; complete because both types are valid in the empty context,
`ExternSub.check_iff`, the procedure of `ExternSub.decideEmpty`). -/
theorem core3Profile_XSub_iff {a b : Core3Extern} :
    core3Profile.XSub a b ↔ Wasm.Validation.ExternSub {} a.1 b.1 :=
  Wasm.Validation.ExternSub.check_iff Wasm.Validation.TypeCtx.ok_empty rfl a.2 b.2

end Core3

/-! ## Lookups and state updates used by the definition rules -/

section Updates

variable {X : Type}

theorem consumeValue?_consumedAt {Γ : Ctx X} {i : Nat} {t : Types.ValType Nat}
    (h : Γ.value? i = some (t, false)) : Γ.consumeValue? i = .ok (t, consumedAt Γ i t) := by
  simp only [Ctx.value?] at h
  simp [Ctx.consumeValue?, h, consumedAt]

namespace DState

end DState

namespace DefState

end DefState

end Updates

/-! ## The judgements -/

section Judgements

variable {X : Type} {M : Type}

end Judgements

/-! ## Profile instances -/

/-! ## Basic properties -/

section Properties

variable {X : Type} {M N : Type} {feat : Features} {P : DefProfile X}

mutual
  /-- Validity only depends on the core modules through their module types: changing the core
  module type along `f` with `validCore' ∘ f = validCore` preserves it. -/
  theorem ValidDef.mapCore {validCore : M → Option (CoreModuleType X)}
      {validCore' : N → Option (CoreModuleType X)} (f : M → N)
      (hf : ∀ m, validCore' (f m) = validCore m) {sc : Scopes X} {s s' : DefState X}
      {d : Syntax.Definition M} :
      ValidDef feat P validCore sc s d s' →
        ValidDef feat P validCore' sc s (Syntax.Definition.map f d) s'
    | .coreModule h => .coreModule ((hf _).trans h)
    | .coreInstantiate hm hn ha hi => .coreInstantiate hm hn ha hi
    | .coreInstanceExports hn h => .coreInstanceExports hn h
    | .coreType h => .coreType h
    | .component h hd => .component (ValidDefs.mapCore f hf h) hd
    | .instantiate hc hn ha hfr hs hcons => .instantiate hc hn ha hfr hs hcons
    | .instanceExports hn hu he hc => .instanceExports hn hu he hc
    | .aliasExport h hs => .aliasExport h hs
    | .aliasCoreExport hi hx hs => .aliasCoreExport hi hx hs
    | .aliasOuterType hq hs hr => .aliasOuterType hq hs hr
    | .aliasOuterCoreType hq hs => .aliasOuterCoreType hq hs
    | .aliasOuterCoreModule hq hm => .aliasOuterCoreModule hq hm
    | .aliasOuterComponent hq hc => .aliasOuterComponent hq hc
    | .type h => .type h
    | .canon h => .canon h
    | .builtin h => .builtin h
    | .start h1 h2 h3 h4 h5 => .start h1 h2 h3 h4 h5
    | .import_ h => .import_ h
    | .export_ h1 h2 h3 h4 h5 h6 h7 h8 => .export_ h1 h2 h3 h4 h5 h6 h7 h8
    | .value h1 h2 h3 => .value h1 h2 h3

  /-- `ValidDef.mapCore` for definition lists. -/
  theorem ValidDefs.mapCore {validCore : M → Option (CoreModuleType X)}
      {validCore' : N → Option (CoreModuleType X)} (f : M → N)
      (hf : ∀ m, validCore' (f m) = validCore m) {sc : Scopes X} {s s' : DefState X}
      {ds : List (Syntax.Definition M)} :
      ValidDefs feat P validCore sc s ds s' →
        ValidDefs feat P validCore' sc s (Syntax.Definition.mapList f ds) s'
    | .nil => .nil
    | .cons h hs => .cons (ValidDef.mapCore f hf h) (ValidDefs.mapCore f hf hs)
end

theorem ValidComponent.mapCore {validCore : M → Option (CoreModuleType X)}
    {validCore' : N → Option (CoreModuleType X)} (f : M → N)
    (hf : ∀ m, validCore' (f m) = validCore m) {c : Syntax.Component M}
    {ct : ComponentType Nat X} (h : ValidComponent feat P validCore c ct) :
    ValidComponent feat P validCore' (Syntax.Component.map f c) ct :=
  let ⟨s, hs, hd, he⟩ := h
  ⟨s, ValidDefs.mapCore f hf hs, hd, he⟩

/-- 🪙 `value` definitions and `start` require the values feature. -/
theorem ValidDef.values_of_value {validCore : M → Option (CoreModuleType X)} {sc : Scopes X}
    {s s' : DefState X} {t : Syntax.VT} {p : List UInt8}
    (h : ValidDef feat P validCore sc s (.value t p) s') : feat.values = true := by
  cases h with
  | value hf _ _ => exact hf

theorem ValidDef.values_of_start {validCore : M → Option (CoreModuleType X)} {sc : Scopes X}
    {s s' : DefState X} {f : Nat} {args : List Nat} {r : Nat}
    (h : ValidDef feat P validCore sc s (.start f args r) s') : feat.values = true := by
  cases h with
  | start hf _ _ _ _ => exact hf

/-- Core functions, tables, memories, globals and tags can never be exported. -/
theorem ValidDef.not_export_core {validCore : M → Option (CoreModuleType X)} {sc : Scopes X}
    {s s' : DefState X} {n : Syntax.ExternName} {so : Syntax.CoreSort} {i : Nat}
    {asc : Option Syntax.ExternDesc} (hs : so ≠ .module_)
    (h : ValidDef feat P validCore sc s (.export_ n ⟨.core so, i⟩ asc) s') : False := by
  cases h with
  | export_ _ _ hitem _ _ _ _ _ =>
    cases so <;> first | exact hs rfl | simp [itemEntity?] at hitem

end Properties

/-- If a V1 component is valid (with `v1ModuleType`), its Lime1 image is valid with
`lime1ModuleType` and the same type. Only this direction is proved. -/
theorem ValidComponent.v1_toLime {feat : Features} {c : Syntax.Component V1.Module}
    {ct : ComponentType Nat CoreExternType}
    (h : ValidComponent feat lime1Profile v1ModuleType c ct) :
    ValidComponent feat lime1Profile lime1ModuleType (c.map V1.Module.toLime) ct :=
  ValidComponent.mapCore V1.Module.toLime v1ModuleType_toLime h

/-- `ValidComponent.v1_toLime` with the core `ModuleValid` conjunct: a valid V1 component's
Lime1 image is a valid Lime1 component of the same type. -/
theorem ValidComponentV1.toLime {feat : Features} {c : Syntax.Component V1.Module}
    {ct : ComponentType Nat CoreExternType} (h : ValidComponentV1 feat c ct) :
    ValidComponentLime1 feat (c.map V1.Module.toLime) ct := by
  refine ⟨ValidComponent.v1_toLime h.1, ?_⟩
  simp only [Syntax.Component.coreModules_map, List.mem_map]
  rintro _ ⟨m, hm, rfl⟩
  exact V1.Validation.ModuleValid.toLime (h.2 m hm)

/-! ## Tests -/

namespace DefsTests

open DefTypesTests (errMsg?)
open CanonOptsTests (okVal?)

-- FLAG(statement-change): moved from `DefTypesTests`; `core3Hooks` are now the hooks over closed
-- extern types (statement text unchanged).
/-- `core-modules.wast` 50-56 under the Core 3.0 hooks: a module-type memory import above 65536
pages. -/
theorem core_module_type_memory_too_large_core3 :
    errMsg? (checkCoreModuleType? core3Hooks []
      [.import_ "" "" (.memory ⟨.i32, ⟨70000, none⟩⟩)]) =
      some "memory size must be at most 65536 pages (4GiB)" := by decide +kernel

-- FLAG(statement-change): moved from `DefTypesTests`; `core3Hooks` are now the hooks over closed
-- extern types (statement text unchanged).
/-- A `rec` group of two subtypes defines two local type indices (Core 3.0 hooks). -/
theorem core_module_type_rec_group_indices :
    (checkCoreModuleType? core3Hooks [] [.type recTwo,
       .export_ "f" (.func ⟨1⟩)]).toOption.isSome = true := by decide +kernel

/-- A tag import must name a function type without results (`Tagtype_ok`). -/
theorem core_module_type_tag_results_core3 :
    (checkCoreModuleType? core3Hooks []
      [.type (V1.FuncType.toCoreRec ⟨[], [.int .i32]⟩), .import_ "" "t" (.tag ⟨0⟩)]).toOption.isNone
      = true := by decide +kernel

/-- A recursion group declaring a supertype whose body it does not match fails `Type_ok`
(Wasm 3.0 spec §2.4 "Types", `Subtype_ok`: `func [] -> []` is not a subtype of
`func [i32] -> []`); one that matches passes. -/
theorem rec_super_mismatch_core3 :
    errMsg? (checkCoreModuleType? core3Hooks [] [.type openI32,
      .type ⟨[⟨true, [⟨0⟩], .func ⟨[], []⟩⟩]⟩]) =
      some "core type is not valid in this profile" ∧
    errMsg? (checkCoreModuleType? core3Hooks [] [.type openI32,
      .type ⟨[⟨true, [⟨0⟩], .func ⟨[.num (.int .i32)], []⟩⟩]⟩]) = none := by decide +kernel

/-- The adder is a valid component (V1 module types, WASI 0.2 features) with type
`adderType`. -/
theorem adder_valid : ValidComponent Features.p2 lime1Profile v1ModuleType adder adderType := by
  refine ⟨_, .cons (.coreModule rfl) (.cons (.coreInstantiate rfl (by decide) (by simp)
    (fun _ h => by cases h)) (.cons (.aliasCoreExport rfl rfl rfl)
    (.cons (.type (.func (t := adderFunc) (checkFuncType?_sound (by decide +kernel))))
    (.cons (.canon (.lift (ft := adderFunc) rfl (by decide +kernel)))
    (.cons (.export_ rfl (fun _ hp => by cases hp) rfl .none rfl (by decide +kernel) rfl (.nil _))
    .nil))))), ?_, ?_⟩
  · decide +kernel
  · rfl

/-- `(instance (instantiate 0))` without the argument for import `a` is invalid
("missing import named `a`"). -/
theorem instantiate_missing_import (st' : DefState CoreExternType) :
    ¬ ValidDef Features.p2 lime1Profile v1ModuleType [] stImp
      (.instance_ (.instantiate 0 [])) st' := by
  intro h
  cases h with
  | instantiate hc _ ha _ hs _ =>
    have hct := (Option.some.inj hc).symm
    subst hct
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at ha
    subst ha
    cases hs with
    | cons hmem _ _ => cases hmem

/-- `(alias outer 1 0 (type))` of a resource type across a component boundary is invalid
("transitively refers to resources"). -/
theorem alias_outer_resource_rejected (st' : DefState CoreExternType) :
    ¬ ValidDef Features.p2 lime1Profile v1ModuleType [parentCtx]
      { st := { ctx := Ctx.empty .component 1 1 } } (.alias (.outer 1 0 .type)) st' := by
  intro h
  cases h with
  | aliasOuterType hq hslot hres =>
    have hq' := hq
    simp only [Scopes.outer?, List.getElem?_cons_zero, Except.ok.injEq] at hq'
    subst hq'
    have hs := (Option.some.inj hslot).symm
    subst hs
    have := hres rfl
    simp [TypeDef.fv] at this

/-- A value definition that is never consumed makes the component invalid (🪙 linearity). -/
theorem unconsumed_value_rejected (ct : ComponentType Nat CoreExternType) :
    ¬ ValidComponent { values := true } lime1Profile v1ModuleType
      ([.value (.prim .u32) [0, 0, 0, 0]] : Syntax.Component V1.Module) ct := by
  rintro ⟨st, hs, hd, _⟩
  cases hs with
  | cons h hs' =>
    cases hs'
    cases h with
    | value _ _ _ =>
      have h1 := hd.1
      simp [DefState.step, DState.withCtx, Ctx.pushValue, Ctx.pushList, Ctx.allValuesConsumed,
        initState, Ctx.empty] at h1

/-- Generativity: instantiating allocates the fresh variable `3` for the defined resource,
records it as `definedRes (3, none)` (so it is not a local resource: `localRep? 3 = none`,
and `resource.new` on it is rejected by `ValidBuiltin`), and advances `nextVar`. -/
theorem instantiate_fresh_resource :
    resInstFresh = true ∧ resInst.ctx.definedRes = [(3, none)] ∧
      resInst.ctx.localRep? 3 = none ∧ resInst.ctx.nextVar = 4 := by
  decide +kernel

/-- An unascribed export of a function whose type uses an unnamed nominal type is invalid
(wasmparser "func not valid to be used as export"). -/
theorem export_unnamed_func_rejected (s' : DefState CoreExternType) :
    ¬ ValidDef Features.p2 lime1Profile v1ModuleType [] stUnnamed
      (.export_ { name := "f" } ⟨.func, 0⟩ none) s' := by
  intro h
  cases h with
  | export_ _ _ _ _ _ hvis _ _ => exact absurd hvis (by decide +kernel)

/-- Exporting a function whose type uses a resource before the resource is exported is invalid
(Binary.md: resources used by an export must be introduced by a *preceding* import/export),
even though exporting the resource afterwards would close the component type. -/
theorem export_unnamed_resource_rejected (s' : DefState CoreExternType) :
    ¬ ValidDef Features.p2 lime1Profile v1ModuleType [] stRes
      (.export_ { name := "f" } ⟨.func, 0⟩ none) s' := by
  intro h
  cases h with
  | export_ _ _ hitem hasc _ _ hres _ =>
    cases hasc
    simp only [itemEntity?, stRes, Ctx.func?, Option.map_eq_some_iff] at hitem
    obtain ⟨ft, hft, rfl⟩ := hitem
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hft
    subst hft
    exact absurd hres (by decide +kernel)

/-! ### `thread.new-indirect` tables under the Core 3.0 profile -/

/-- `thread.new-indirect` under the Core 3.0 profile: the table's element type must match
`funcref` by reference subtyping (`CanonicalABI.md`), so a `(ref null nofunc)` table, a `(ref
func)` table (64-bit, under 🐘), a table of a concrete function type and a `funcref` table are
accepted, while an `externref` table is rejected (all five tables are valid, so the context has
five entries). -/
theorem core3_newIndirect_tables :
    core3TblCtx.coreTables.length = 5 ∧
    (okVal? (checkBuiltin? Features.p3plus core3Profile.view core3TblCtx
      (.threadNewIndirect 0 0))).isSome = true ∧
    (okVal? (checkBuiltin? Features.p3plus core3Profile.view core3TblCtx
      (.threadNewIndirect 0 1))).isSome = true ∧
    CanonOptsTests.canonErr? (checkBuiltin? Features.p3plus core3Profile.view core3TblCtx
      (.threadNewIndirect 0 2)) = some "table is not a table of (ref null (func))" ∧
    (okVal? (checkBuiltin? Features.p3plus core3Profile.view core3TblCtx
      (.threadNewIndirect 0 3))).isSome = true ∧
    (okVal? (checkBuiltin? Features.p3plus core3Profile.view core3TblCtx
      (.threadNewIndirect 0 4))).isSome = true := by
  decide +kernel

/-- The `externref` table is rejected by the relational judgement too. -/
theorem not_validBuiltin_core3_newIndirect_externref (x : Core3Extern) (Γ' : Ctx Core3Extern) :
    ¬ ValidBuiltin Features.p3plus core3Profile.view core3TblCtx (.threadNewIndirect 0 2) x Γ' :=
  fun h => by
    have hk : (okVal? (checkBuiltin? Features.p3plus core3Profile.view core3TblCtx
        (.threadNewIndirect 0 2))).isNone = true := by
      decide +kernel
    simp [checkBuiltin?_complete h, okVal?] at hk

end DefsTests

end Silmaril.Wasm.Component.Validation
