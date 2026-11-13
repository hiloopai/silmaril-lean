module

import all Batteries.Data.Except
public import Silmaril.Wasm.Component.Reference.Validation.DefTypes.Defs
public import Silmaril.Wasm.Component.Reference.Validation.Builtins.Defs
public import Silmaril.Wasm.Component.Reference.Validation.CoreModules.Defs
public import Silmaril.Wasm.Component.Reference.Types.Subtype.Defs
public import Silmaril.Wasm.Component.Reference.Engine.Lime1.Defs
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Structural.Defs
public import Silmaril.Wasm.V1.Validation.Modules
public import Silmaril.Wasm.V1.ToCore.DefTypes
public import Silmaril.Wasm.Validation.Check.Validate
public import Silmaril.Wasm.Validation.Subtyping.Decide
public import Silmaril.Wasm.Component.Reference.Wasm.Lime1.Validation.FromV1.Defs

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

/-- The function types of every function of the imports-first function index space resolve
in the type section (true of every valid module, `lime1FuncTypesResolve_of_valid`). -/
def FuncTypesResolve (m : Lime1.Module) : Prop :=
  ∀ t ∈ m.functionTypes, (m.types[t.toNat]?).isSome = true

instance (m : Lime1.Module) : Decidable (FuncTypesResolve m) :=
  inferInstanceAs (Decidable (∀ t ∈ m.functionTypes, (m.types[t.toNat]?).isSome = true))

/-- `lime1ModuleType` restricted to modules whose function types resolve. -/
def lime1ResolvedModuleType (m : Lime1.Module) : Option (CoreModuleType CoreExternType) :=
  if FuncTypesResolve m then lime1ModuleType m else none

/-- A module whose first defined function has an unresolved type index: `lime1ModuleType`
resolves the export of the second function (index 1), while the engine's validation context
drops the unresolved function and shifts the index space. -/
def unresolvedModule : Lime1.Module where
  types := [⟨[], []⟩]
  funcs := [⟨⟨5⟩, [], []⟩, ⟨⟨0⟩, [], []⟩]
  exports := [⟨"f", .func ⟨1⟩⟩]

end CoreAgreement

/-! ## Profiles -/

/-- The profile-specific parts of definition validation: the declarator hooks, the
core views of canonical definitions, core extern subtyping (Boolean, for
`core instance` instantiation and core module subtyping) and the core sort of an extern type
(for `alias core export`). -/
structure DefProfile (X : Type) where
  decl : DeclHooks X
  view : BuiltinView X
  extSub : X → X → Bool
  coreSort : X → Syntax.CoreSort

/-- Core extern subtyping of a profile as a relation. -/
def DefProfile.XSub {X : Type} (P : DefProfile X) (a b : X) : Prop := P.extSub a b = true

/-- The core sort of a `CoreExternType`. -/
def coreExternSort : CoreExternType → Syntax.CoreSort
  | .func _ => .func
  | .table .. => .table
  | .memory .. => .memory
  | .global .. => .global
  | .tag _ => .tag

/-- The V1/Lime1 profile: `lime1Hooks`, `coreExternBuiltinView`, `CoreExternType.sub`. -/
def lime1Profile : DefProfile CoreExternType where
  decl := lime1Hooks
  view := coreExternBuiltinView
  extSub := CoreExternType.sub
  coreSort := coreExternSort

/-! ### The Core 3.0 profile

Core extern types are closed extern types valid in the empty context (`Core3Extern`), the
extern types of the concrete Core 3.0 engine (`Engine.core3`, `Engine.Core3.ExtT`). Module-type
declarations are closed against the closed defined types of their core type space
(`core3CoreExtern?`); recursion groups must pass `Type_ok` (`core3RecOk`); core extern
subtyping is `ExternSub {}` decided by its checker (`core3Profile_XSub_iff`); core modules
are typed by the Core 3.0 validator `validate?` (`core3ModuleType?`). -/

section Core3

open Wasm.Validation (CExternType ExternTypeOk DefType CValType)

/-- Core extern types of the Core 3.0 profile: closed extern types (`CExternType`: every type
use is a closed defined type, Wasm 3.0 spec §2.0 "closed types") valid in the empty context
(`Externtype_ok`). The same carrier as the Core 3.0 engine's extern types (`Engine.Core3.ExtT`),
so a component accepted here is typed with the types the engine checks at instantiation. -/
abbrev Core3Extern : Type := {τ : CExternType // ExternTypeOk {} τ}

/-- A closed extern type as a `Core3Extern`, when the checker `ExternTypeOk.check {}`
(sound, `ExternTypeOk.check_sound`) accepts it. -/
def core3Ext? (τ : CExternType) : Option Core3Extern :=
  if h : Wasm.Validation.ExternTypeOk.check {} τ = true then
    some ⟨τ, Wasm.Validation.ExternTypeOk.check_sound h⟩
  else none

/-- A module-type import or export of the Core 3.0 profile: the syntactic extern type closed
against the closed defined types of the core type space `ts` (`$clos_externtype`,
`Context.closeExtern?`; type indices out of range give `none`), kept when it is valid in the
empty context (`Externtype_ok`: a function or tag index must name a function type, a tag type
has no results, limits are within their bounds, reference types are valid). -/
def core3CoreExtern? (ts : List (CoreTypeSlot Core3Extern)) (e : Wasm.ExternType) :
    Option Core3Extern :=
  (Wasm.Validation.Context.closeExtern? { types := CoreTypeSlot.defTypes ts } e).bind core3Ext?

/-- `Type_ok` of a recursion group `r` defined after the core types `prev` (Wasm 3.0 spec §2.4
"Types"; wasmparser `canonicalize_and_intern_rec_group` in a component's core type space): the
group closed at index `|prev|` against the closed types of `prev` (`CoreTypeSlot.closeRec`)
passes `Rectype_ok`, decided by `RecTypeOkAt.check` (sound, `core3RecOk_sound`). -/
def core3RecOk {X : Type} (prev : List (CoreTypeSlot X)) (r : Wasm.RecType) : Bool :=
  Wasm.Validation.RecTypeOkAt.check
    ({ types := CoreTypeSlot.defTypes prev ++ CoreTypeSlot.closeRec (CoreTypeSlot.defTypes prev) r }
      : Wasm.Validation.Context)
    r.types (CoreTypeSlot.defTypes prev).length

/-- A numeric value type. -/
def core3NumOf? : CValType → Option NumType
  | .num t => some t
  | _ => none

/-- The flat signature of a closed defined type: `some ft` iff the type is
`V1.FuncType.toDefType ft`, a singleton final recursion group of a numeric function type (the
Core 3.0 engine's `flatType?`, `SingleThreaded.flatType?`). -/
def core3FlatType? (d : DefType) : Option V1.FuncType := do
  let (ps, rs) ← d.funcType?
  let ft : V1.FuncType := ⟨← ps.mapM core3NumOf?, ← rs.mapM core3NumOf?⟩
  if ft.toDefType = d then some ft else none

theorem tyOk_ofList_num (Δ : Wasm.Validation.TypeCtx) (ts : List NumType) :
    Wasm.Validation.TyOk Δ (Wasm.Validation.Ty.ofList (ts.map Wasm.Validation.Ty.num)) := by
  induction ts with
  | nil => exact .nil
  | cons t ts ih => exact .cons (.num t) ih

/-- The defined type of a flat signature is a valid function extern type. -/
theorem externTypeOk_toDefType (ft : V1.FuncType) : ExternTypeOk {} (.func ft.toDefType) := by
  have hok : Wasm.Validation.TyOk {} ft.toDefType := by
    unfold V1.FuncType.toDefType
    simp only [Wasm.Validation.liftRec, V1.FuncType.toCoreRec, List.map_cons, List.map_nil,
      Wasm.Validation.liftSub, Wasm.Validation.liftComp, V1.FuncType.toCore,
      V1.liftResult_toCore]
    exact .defn (.cons (.noSuper (.func (tyOk_ofList_num _ _) (tyOk_ofList_num _ _))) .nil)
      (by simp [Wasm.Validation.Ty.length])
  exact .func hok (Wasm.Validation.Expand.iff.mpr (V1.FuncType.toDefType_expand ft))

/-- The core function type of a flat signature (`canon lower`, builtins): the closed defined
type `V1.FuncType.toDefType ft` (the Core 3.0 engine's `ofFlatType`). -/
def core3OfFlat (ft : V1.FuncType) : Core3Extern := ⟨.func ft.toDefType, externTypeOk_toDefType ft⟩

/-- The table view of `thread.new-indirect` (`CanonicalABI.md` §`canon thread.new-indirect`:
the table's element type must match `funcref`): the address type of a table whose element
reference type is a subtype of `(ref null func)` (Wasm 3.0 spec §2.3 "Subtyping", `Reftype_sub`,
decided by `Sub.check {}`; complete on valid types, `core3FuncTable?_eq_some_iff`). So
`(ref null? func)`, `(ref null? nofunc)` and `(ref null? $t)` for a closed function type `$t`
match; limits are not inspected. -/
def core3FuncTable? (x : Core3Extern) : Option AddrType :=
  match x.1 with
  | .table t =>
    if Wasm.Validation.Sub.check {} t.element Wasm.Validation.Ty.funcref then some t.address
    else none
  | _ => none

/-- Hooks of the Core 3.0 profile: module-type imports/exports are closed and validated
(`core3CoreExtern?`); a destructor has exactly the closed type `[rep] -> []` (a singleton
final group, `V1.FuncType.toDefType`); a recursion group must pass `Type_ok` against the
preceding core types (`core3RecOk`). -/
def core3Hooks : DeclHooks Core3Extern where
  coreExtern? := core3CoreExtern?
  dtorOk rep x := decide (x.1 = .func (V1.FuncType.toDefType ⟨[.int rep.intType], []⟩))
  recOk := core3RecOk

/-- The Core 3.0 profile. Core extern subtyping is the checker `ExternSub.check {}` of Core
3.0 import matching (Wasm 3.0 spec §2.2 "External types" / "Import subtyping": limits
subtyping, defined-type subtyping of functions, equivalence of table element and mutable
global types); it is sound, and complete on valid types (`core3Profile_XSub_iff`). Canonical
definitions see a memory's address type, the flat signature of a function type
(`core3FlatType?`) and a table whose element type matches `funcref` by reference subtyping
(`core3FuncTable?`, `CanonicalABI.md`; not table subtyping, which would demand an equivalent
element type). -/
def core3Profile : DefProfile Core3Extern where
  decl := core3Hooks
  view :=
    { core :=
        { memAddr? x := match x.1 with
            | .mem m => some m.address
            | _ => none
          funcType? x := match x.1 with
            | .func d => core3FlatType? d
            | _ => none
          ofFlat := core3OfFlat }
      funcTable? := core3FuncTable? }
  extSub a b := Wasm.Validation.ExternSub.check {} a.1 b.1
  coreSort x := match x.1 with
    | .func _ => .func
    | .tag _ => .tag
    | .table _ => .table
    | .mem _ => .memory
    | .global _ => .global

/-- The Core 3.0 module type: `validate?`'s `CModuleType` (so only valid modules are typed),
with the import types keyed by the `(module, name)` of `m.imports` and the export types by the
names of `m.exports`, in order. Every type is checked valid in the empty context
(`core3Ext?`), which never fails on a module `validate?` accepts. -/
def core3ModuleType? (m : Wasm.Module) : Option (CoreModuleType Core3Extern) := do
  let mt ← Wasm.Validation.validate? m
  let is ← (m.imports.zip mt.imports).mapM fun p =>
    (core3Ext? p.2).map ((p.1.moduleName, p.1.name), ·)
  let es ← (m.exports.zip mt.exports).mapM fun p => (core3Ext? p.2).map (p.1.name, ·)
  pure ⟨is, es⟩

end Core3

/-! ## Lookups and state updates used by the definition rules -/

section Updates

variable {X : Type}

/-- The entity type of a component-level `sortidx` (the sorts that may be exported, passed to
`instantiate`, or put in an inline-export instance: `core module` and the five component
sorts). Values are looked up regardless of their consumption flag (consumption is
`ConsumeValues`). Other core sorts have no entity type. -/
def itemEntity? (Γ : Ctx X) (it : Syntax.SortIdx Syntax.Sort_) : Option (Entity Nat X) :=
  match it.sort with
  | .core .module_ => (Γ.coreModule? it.idx).map .module
  | .func => (Γ.func? it.idx).map .func
  | .value => (Γ.value? it.idx).map fun p => .value p.1
  | .type => (Γ.type? it.idx).map .type
  | .instance_ => (Γ.instance? it.idx).map .instance
  | .component => (Γ.component? it.idx).map .component
  | .core _ => none

/-- The value indices among some `sortidx`s (these are consumed, 🪙). -/
def valueIdxs (its : List (Syntax.SortIdx Syntax.Sort_)) : List Nat :=
  its.filterMap fun it => if it.sort = .value then some it.idx else none

/-- The extern type of a core `sortidx` of a runtime sort (func, table, memory, global,
tag). -/
def coreItem? (Γ : Ctx X) (it : Syntax.SortIdx Syntax.CoreSort) : Option X :=
  match it.sort with
  | .func => Γ.coreFunc? it.idx
  | .table => Γ.coreTable? it.idx
  | .memory => Γ.coreMem? it.idx
  | .global => Γ.coreGlobal? it.idx
  | .tag => Γ.coreTag? it.idx
  | _ => none

/-- Push a core extern type into the core index space of sort `s` (runtime sorts only; the
other sorts leave the context unchanged and never arise from `DefProfile.coreSort`). -/
def pushCoreItem (Γ : Ctx X) : Syntax.CoreSort → X → Ctx X
  | .func, x => (Γ.pushCoreFunc x).2
  | .table, x => (Γ.pushCoreTable x).2
  | .memory, x => (Γ.pushCoreMem x).2
  | .global, x => (Γ.pushCoreGlobal x).2
  | .tag, x => (Γ.pushCoreTag x).2
  | _, _ => Γ

/-- Mark value `i` (of type `t`) consumed; exactly the context `Ctx.consumeValue?` returns
(`consumeValue?_consumedAt`). -/
def consumedAt (Γ : Ctx X) (i : Nat) (t : Types.ValType Nat) : Ctx X :=
  { Γ with values := Γ.values.set i (t, true) }

/-- Consume the values `is`, in order, each exactly once (🪙 linearity), returning their
types. -/
inductive ConsumeValues : Ctx X → List Nat → List (Types.ValType Nat) → Ctx X → Prop
  | nil (Γ : Ctx X) : ConsumeValues Γ [] [] Γ
  | cons {Γ Γ' : Ctx X} {i : Nat} {is : List Nat} {t : Types.ValType Nat}
      {ts : List (Types.ValType Nat)} (h : Γ.value? i = some (t, false))
      (hs : ConsumeValues (consumedAt Γ i t) is ts Γ') : ConsumeValues Γ (i :: is) (t :: ts) Γ'

/-- The renaming applied to the exports of an instantiated component type: its ∃-binders
`ds` go to the fresh variables `base, base + 1, ...` (generativity), every other variable
through the import substitution `f`. -/
def instRename (ds : List Nat) (base : Nat) (f : Nat → Nat) (r : Nat) : Nat :=
  match ds.idxOf? r with
  | some k => base + k
  | none => f r

/-- The instance type of `instantiate c` for a component of type `ct`, import substitution
`f` and fresh base variable `base` (wasmparser `instantiate_component`: remapped exports,
no ∃-binders left, the fresh variables belonging to the enclosing component). -/
def instantiateType (ct : ComponentType Nat X) (f : Nat → Nat) (base : Nat) :
    InstanceType Nat X :=
  ⟨[], Entity.mapList (instRename ct.defined base f) ct.exports⟩

/-- The component type of a finished component body (`Explainer.md` §Type Checking): ∀-binders are
the imported resources, ∃-binders the defined resources (local or from child instances) that are
explicitly exported. -/
def componentTypeOfDefs (Γ : Ctx X) : ComponentType Nat X :=
  ⟨Γ.importedRes.map (·.1), Γ.imports,
   (Γ.definedRes.map (·.1)).filter (fun r => Γ.explicitRes.any (·.1 == r)), Γ.exports⟩

/-- The checks after the last definition of a component: every value consumed (🪙), and the
component type is closed (every resource it mentions is bound; for valid components this is
the resource part of the external-visibility rule, and nested components are closed except
for outer aliases, which may not carry resources across a component boundary). -/
def ComponentDone (Γ : Ctx X) : Prop :=
  Γ.allValuesConsumed = true ∧ (componentTypeOfDefs Γ).WellScoped []

instance (Γ : Ctx X) : Decidable (ComponentDone Γ) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The entity a `canon lift`/`lower` definition pushes. -/
def pushCanonEntity (Γ : Ctx X) : CanonEntity X → Ctx X
  | .func t => (Γ.pushFunc t).2
  | .coreFunc x => (Γ.pushCoreFunc x).2

/-- 🪙 `start`: the result values are pushed and the component has a start function. -/
def startCtx (Γ : Ctx X) (rs : List (Types.ValType Nat)) : Ctx X :=
  rs.foldl (fun g t => (g.pushValue t).2) { Γ with hasStart := true }

/-- 🪙 A `value` definition's type may not (transitively) contain handles, `stream`,
`future` or `error-context` (`Explainer.md` §🪙 Value Definitions). -/
def valueForbidden : WIT.ClosedType Nat → Bool
  | .own _ | .borrow _ | .stream _ | .future _ | .errorContext => true
  | _ => false

/-- The type of a 🪙 `value` definition is allowed. -/
def valueDefTypeOk (t : Types.ValType Nat) : Bool := !ABI.contains valueForbidden t

mutual
  /-- The resource type exports `(r, path)` of an entity type (a type export `resource r`
  at the empty path, or inside nested instance exports at their positions). -/
  def Entity.resEntries : Entity Nat X → List (Nat × List Nat)
    | .type (.resource r) => [(r, [])]
    | .instance t => InstanceType.resEntries t
    | _ => []

  /-- `Entity.resEntries` of an instance type. -/
  def InstanceType.resEntries : InstanceType Nat X → List (Nat × List Nat)
    | ⟨_, es⟩ => Entity.resEntriesList 0 es

  /-- `Entity.resEntries` of an export list, `k` the position of the head. -/
  def Entity.resEntriesList (k : Nat) : List (String × Entity Nat X) → List (Nat × List Nat)
    | [] => []
    | (_, e) :: es =>
      (Entity.resEntries e).map (fun q => (q.1, k :: q.2)) ++ Entity.resEntriesList (k + 1) es
end

/-- The instance-slot tokens contributed by an inline export `n` of item `it`: a type keeps its
token, an instance the tokens of its type exports (prefixed by `n`). -/
def itemTokens (Γ : Ctx X) (n : String) (it : Syntax.SortIdx Syntax.Sort_) :
    List (List String × Nat) :=
  match it.sort with
  | .type => ((Γ.typeSlot? it.idx).map fun s => ([n], s.token)).toList
  | .instance_ =>
    ((Γ.instanceSlot? it.idx).map fun s => s.tokens.map fun q => (n :: q.1, q.2)).getD []
  | _ => []

/-- Naming information for the tokens allocated by exporting item `it` at new index `j`
(`Γ` before, `Γ'` after the push): a type export inherits the information of the exported
type's token, an instance export that of the source instance's type-export tokens (renamed
path-wise, as `registerNames` does for instance imports). -/
def exportNames (tbl : NameTable) (Γ Γ' : Ctx X) (it : Syntax.SortIdx Syntax.Sort_) (j : Nat) :
    NameTable :=
  match it.sort with
  | .type =>
    match Γ'.typeSlot? j, Γ.typeSlot? it.idx with
    | some s, some s0 => (s.token, tokInfo tbl s0.token) :: tbl
    | _, _ => tbl
  | .instance_ =>
    match Γ'.instanceSlot? j, Γ.instanceSlot? it.idx with
    | some s, some s0 =>
      let g := renameTok s0.tokens s.tokens
      (s.tokens.filterMap fun q => (s0.tokens.lookup q.1).map fun it0 =>
        let inf := tokInfo tbl it0
        (q.2, { inf with contents := inf.contents.rename g })) ++ tbl
    | _, _ => tbl
  | _ => tbl

namespace DState

/-- `instance (instantiate c args)`: allocate the fresh ∃ variables `nextVar, ...` for the
component's defined resources, record them as `definedRes (v, none)` (owned by this
component's existential, not local), and push the instantiated instance type with fresh
(unnamed) tokens. -/
def instantiate (st : DState X) (ct : ComponentType Nat X) (f : Nat → Nat) : DState X :=
  let base := st.ctx.nextVar
  let Γ1 : Ctx X := { st.ctx with nextVar := base + ct.defined.length }
  let Γ2 := (List.range' base ct.defined.length).foldl (fun g v => g.addDefinedRes v none) Γ1
  st.withCtx (Γ2.pushInstance (instantiateType ct f base)).2

/-- `instance (export ...)*`: push the inline-export instance, keeping the tokens of the
referenced types and instances (`pushInstanceSlot`). -/
def inlineInstance (st : DState X) (items : List (Syntax.ExternName × Syntax.SortIdx Syntax.Sort_))
    (ents : List (String × Entity Nat X)) : DState X :=
  let toks := items.flatMap fun it => itemTokens st.ctx it.1.name it.2
  st.withCtx (st.ctx.pushInstanceSlot ⟨⟨[], ents⟩, toks⟩).2

/-- A nested `component` definition: return from the child scope and push its type. -/
def closeComponentDef (st ch : DState X) : DState X :=
  let r := st.returnTo ch
  r.withCtx (r.ctx.pushComponent (componentTypeOfDefs ch.ctx)).2

/-- `export n it` of entity type `e`: push the new index with fresh tokens registered as
exported, record the export, record every resource type export of `e` not yet explicitly
exported in `explicitRes` (with its path), and register the naming information of the new
tokens. -/
def exportItem (st : DState X) (n : String) (it : Syntax.SortIdx Syntax.Sort_)
    (e : Entity Nat X) : DState X :=
  let k := st.ctx.exports.length
  let p := st.ctx.pushExportEntity e
  let Γ2 := p.2.addExport n e
  let Γ3 := (Entity.resEntries e).foldl
    (fun g q => if g.explicitRes.any (·.1 == q.1) then g else g.addExplicitRes q.1 (k :: q.2))
    Γ2
  { st with ctx := Γ3, names := exportNames st.names st.ctx Γ3 it p.1 }

end DState

/-- The definition-validation state: the declarator state plus the naming requirements
of the component functions and 🪙 values created so far, keyed by index (external visibility
of unascribed `func`/`value` exports, `Explainer.md` §External Visibility of Types; wasmparser
`all_valtypes_named`). Indices without an entry carry no requirement. -/
structure DefState (X : Type) where
  st : DState X
  funcReqs : List (Nat × NameReq) := []
  valueReqs : List (Nat × NameReq) := []

namespace DefState

/-- The validation context. -/
abbrev ctx (s : DefState X) : Ctx X := s.st.ctx

/-- The naming table. -/
abbrev names (s : DefState X) : NameTable := s.st.names

/-- The recorded naming requirement of component function `i`. -/
def funcReq (s : DefState X) (i : Nat) : NameReq := (s.funcReqs.lookup i).getD .tt

/-- The recorded naming requirement of value `i`. -/
def valueReq (s : DefState X) (i : Nat) : NameReq := (s.valueReqs.lookup i).getD .tt

/-- Requirement `r` for the new indices `[a, b)`. -/
def newReqs (a b : Nat) (r : NameReq) : List (Nat × NameReq) :=
  (List.range' a (b - a)).map (·, r)

/-- Move to declarator state `st'`, recording `fr` for every component function index and
`vr` for every value index created by the step. -/
def step (s : DefState X) (st' : DState X) (fr vr : NameReq := .tt) : DefState X :=
  { st := st',
    funcReqs := newReqs s.ctx.funcs.length st'.ctx.funcs.length fr ++ s.funcReqs,
    valueReqs := newReqs s.ctx.values.length st'.ctx.values.length vr ++ s.valueReqs }

end DefState

/-- The naming requirement of an export (`Explainer.md` §External Visibility of Types): that of the
ascribed `externtype` if present; otherwise, for a `type` item, the contents of the exported type
(the export names the type itself), for an `instance` item the contents of its type exports with its
own type exports visible, for a `func`/`value` item the requirement recorded when the index was
created. Unascribed `component` and `core module` exports carry no requirement (closed types). -/
def exportReq (s : DefState X) (it : Syntax.SortIdx Syntax.Sort_) :
    Option Syntax.ExternDesc → NameReq
  | some d => descReq s.names s.ctx d
  | none =>
    match it.sort with
    | .type => contentsOf s.names s.ctx it.idx
    | .instance_ =>
      match s.ctx.instanceSlot? it.idx with
      | some sl =>
        .scoped sl.allTokens (.all (sl.tokens.map fun q => (tokInfo s.names q.2).contents))
      | none => .tt
    | .func => s.funcReq it.idx
    | .value => s.valueReq it.idx
    | _ => .tt

mutual
  /-- The resource type exports `(r, path)` of an entity type, keyed by export-name path (the
  paths of `InstanceSlot.tokens`): a type export `resource r` at the empty path, or inside
  nested instance exports under their names. -/
  def Entity.resNamePaths : Entity Nat X → List (Nat × List String)
    | .type (.resource r) => [(r, [])]
    | .instance t => InstanceType.resNamePaths t
    | _ => []

  /-- `Entity.resNamePaths` of an instance type. -/
  def InstanceType.resNamePaths : InstanceType Nat X → List (Nat × List String)
    | ⟨_, es⟩ => Entity.resNamePathsList es

  /-- `Entity.resNamePaths` of an export list. -/
  def Entity.resNamePathsList : List (String × Entity Nat X) → List (Nat × List String)
    | [] => []
    | (n, e) :: es =>
      (Entity.resNamePaths e).map (fun q => (q.1, n :: q.2)) ++ Entity.resNamePathsList es
end

/-- The naming requirement recorded for a function or value obtained by `alias export i n`
(`Explainer.md` §External Visibility of Types; wasmparser `all_valtypes_named`, where the type
of an aliased item keeps the type ids of the instance's type exports): every resource variable
of the aliased item that instance `i` exports as a type (first such export path) must be named
by that export's token. A type export of the aliased resource made later by this component has a
fresh token (`with_unique`), so it does not name the resource as the aliased item's type does:
the item must be re-exported with an ascription over that export. Variables the instance does
not export as a type carry no requirement (`resNamed` still applies). -/
def aliasReq (Γ : Ctx X) (i : Nat) (n : String) : NameReq :=
  match Γ.instanceSlot? i with
  | none => .tt
  | some sl =>
    match sl.ty.exports.lookup n with
    | none => .tt
    | some e =>
      let paths := Entity.resNamePathsList sl.ty.exports
      .all (e.fv.filterMap fun r =>
        ((paths.lookup r).bind sl.tokenAt?).map fun t => .use t false .tt)

/-- The naming requirement recorded for the function created by a canonical definition:
`canon lift` the contents of its function type; others create no component function. -/
def canonReq (tbl : NameTable) (Γ : Ctx X) : Syntax.Canon → NameReq
  | .lift _ _ t => contentsOf tbl Γ t
  | _ => .tt

/-- Every free resource variable of an exported entity type is introduced by a preceding
import (`importedRes`) or export (`explicitRes`), or by this export itself
(Binary.md, notes to Import and Export Definitions). -/
def resNamed (Γ : Ctx X) (e : Entity Nat X) : Bool :=
  e.fv.all fun r => Γ.importedRes.any (·.1 == r) || Γ.explicitRes.any (·.1 == r) ||
    (Entity.resEntries e).any (·.1 == r)

/-- The initial state of a component. -/
def initState : DefState X := { st := { ctx := Ctx.empty .component } }

end Updates

/-! ## The judgements -/

section Judgements

variable {X : Type} {M : Type}

/-- Export ascription (`Explainer.md` §Import and Export Definitions): none; `(type (sub resource))`
on a resource type (∃-introduction; the exported entity keeps the resource, wasmparser); otherwise
the ascribed `externtype` resolves to `e'` and the inferred type is a subtype of it. -/
inductive Ascribe (feat : Features) (P : DefProfile X) (Γ : Ctx X) :
    Entity Nat X → Option Syntax.ExternDesc → Entity Nat X → Prop
  | none {e : Entity Nat X} : Ascribe feat P Γ e none e
  | subResource {r : Nat} :
      Ascribe feat P Γ (.type (.resource r)) (some (.type .subResource)) (.type (.resource r))
  | desc {e e' : Entity Nat X} {d : Syntax.ExternDesc} (hd : d ≠ .type .subResource)
      (h : ResolveDesc feat Γ d e') (hs : Entity.Sub P.XSub e e') :
      Ascribe feat P Γ e (some d) e'

mutual
  /-- A valid component-level definition, threading the definition state `DefState X` (context,
  naming table, per-index naming requirements of functions and values) with enclosing scopes `sc`.
  -/
  inductive ValidDef (feat : Features) (P : DefProfile X)
      (validCore : M → Option (CoreModuleType X)) :
      Scopes X → DefState X → Syntax.Definition M → DefState X → Prop
    /-- `core module m`: the supplied core validator yields its module type. -/
    | coreModule {sc : Scopes X} {s : DefState X} {m : M} {mt : CoreModuleType X}
        (h : validCore m = some mt) :
        ValidDef feat P validCore sc s (.coreModule m)
          (s.step (s.st.withCtx (s.ctx.pushCoreModule mt).2))
    /-- `core instance (instantiate m args)` (wasmparser `instantiate_core_module`): unique
    argument names, every argument a core instance, and every import `(mod, name)` of the
    module type provided by argument `mod`'s export `name` at a subtype. -/
    | coreInstantiate {sc : Scopes X} {s : DefState X} {mod : Nat} {args : List (String × Nat)}
        {mt : CoreModuleType X} (hm : s.ctx.coreModule? mod = some mt)
        (hnames : (args.map (·.1)).Nodup)
        (hargs : ∀ a ∈ args, a.2 < s.ctx.coreInstances.length)
        (himports : ∀ imp ∈ mt.imports, ∃ i ex y, args.lookup imp.1.1 = some i ∧
          s.ctx.coreInstance? i = some ex ∧ ex.lookup imp.1.2 = some y ∧
          P.extSub y imp.2 = true) :
        ValidDef feat P validCore sc s (.coreInstance (.instantiate mod args))
          (s.step (s.st.withCtx (s.ctx.pushCoreInstance mt.exports).2))
    /-- `core instance (export n (core s i))*`: unique names, runtime sorts only. -/
    | coreInstanceExports {sc : Scopes X} {s : DefState X}
        {items : List (String × Syntax.SortIdx Syntax.CoreSort)} {ex : List (String × X)}
        (hnames : (items.map (·.1)).Nodup)
        (h : items.mapM (fun it => (coreItem? s.ctx it.2).map (it.1, ·)) = some ex) :
        ValidDef feat P validCore sc s (.coreInstance (.exports items))
          (s.step (s.st.withCtx (s.ctx.pushCoreInstance ex).2))
    /-- `core type`: the core type declarator (module types in a fresh core type space). -/
    | coreType {sc : Scopes X} {s : DefState X} {st' : DState X} {t : Syntax.CoreTypeDef}
        (h : ValidCoreTypeDecl P.decl sc s.st t st') :
        ValidDef feat P validCore sc s (.coreType t) (s.step st')
    /-- A nested `component`: its definitions are valid in a fresh scope (this one outer, no
    recorded requirements), it is finished (`ComponentDone`), and its type is pushed. -/
    | component {sc : Scopes X} {s ch : DefState X} {defs : List (Syntax.Definition M)}
        (h : ValidDefs feat P validCore (Scopes.enter sc s.ctx .component).1
          { st := s.st.child (Scopes.enter sc s.ctx .component).2 } defs ch)
        (hdone : ComponentDone ch.ctx) :
        ValidDef feat P validCore sc s (.component defs) (s.step (s.st.closeComponentDef ch.st))
    /-- `instance (instantiate c args)` (`Explainer.md` §Instance Definitions, §Type Checking):
    unique argument names; the arguments' entity types satisfy the imports of `c` after substituting
    the
    import resources (`f` moves only `c`'s ∀-variables); value arguments are consumed; the
    defined resources become fresh variables (`DState.instantiate`). -/
    | instantiate {sc : Scopes X} {s : DefState X} {c : Nat}
        {args : List (String × Syntax.SortIdx Syntax.Sort_)} {ct : ComponentType Nat X}
        {argEs : List (String × Entity Nat X)} {f : Nat → Nat} {ts : List (Types.ValType Nat)}
        {Γc : Ctx X} (hc : s.ctx.component? c = some ct) (hnames : (args.map (·.1)).Nodup)
        (hargs : args.mapM (fun a => (itemEntity? s.ctx a.2).map (a.1, ·)) = some argEs)
        (hf : ∀ r, r ∉ ct.imported → f r = r)
        (hsub : Entity.ListSub P.XSub argEs (Entity.mapList f ct.imports))
        (hcons : ConsumeValues s.ctx (valueIdxs (args.map (·.2))) ts Γc) :
        ValidDef feat P validCore sc s (.instance_ (.instantiate c args))
          (s.step ((s.st.withCtx Γc).instantiate ct f))
    /-- `instance (export n i)*`: valid, strongly unique names; exportable sorts only; value
    items consumed. -/
    | instanceExports {sc : Scopes X} {s : DefState X}
        {items : List (Syntax.ExternName × Syntax.SortIdx Syntax.Sort_)}
        {ents : List (String × Entity Nat X)} {ts : List (Types.ValType Nat)} {Γc : Ctx X}
        (hnames : ∀ it ∈ items, it.1.valid = true)
        (huniq : (items.map fun it => Syntax.strongCanonChars it.1.name.toList).Nodup)
        (hents : items.mapM (fun it => (itemEntity? s.ctx it.2).map (it.1.name, ·)) = some ents)
        (hcons : ConsumeValues s.ctx (valueIdxs (items.map (·.2))) ts Γc) :
        ValidDef feat P validCore sc s (.instance_ (.exports items))
          (s.step ((s.st.withCtx Γc).inlineInstance items ents))
    /-- `alias export i n (s)`: export `n` of instance `i` exists with sort `s`; identities
    are kept (`Ctx.aliasInstanceExport?`). An aliased function or value gets the naming
    requirement `aliasReq` (the tokens of the instance's type exports of its resources). -/
    | aliasExport {sc : Scopes X} {s : DefState X} {i : Nat} {n : String} {so : Syntax.Sort_}
        {p : Nat × Ctx X} (h : s.ctx.aliasInstanceExport? i n = .ok p)
        (hs : exportSortOk s.ctx i n so = true) :
        ValidDef feat P validCore sc s (.alias (.export_ i n so))
          (s.step (s.st.withCtx p.2) (aliasReq s.ctx i n) (aliasReq s.ctx i n))
    /-- `alias core export i n (core s)`: core instance `i` exports `n` with core sort `s`. -/
    | aliasCoreExport {sc : Scopes X} {s : DefState X} {i : Nat} {n : String}
        {so : Syntax.CoreSort} {ex : List (String × X)} {x : X}
        (hi : s.ctx.coreInstance? i = some ex) (hx : ex.lookup n = some x)
        (hs : P.coreSort x = so) :
        ValidDef feat P validCore sc s (.alias (.coreExport i n so))
          (s.step (s.st.withCtx (pushCoreItem s.ctx so x)))
    /-- `alias outer ct i (type)`: across a component boundary the type may not refer to
    resources ("transitively refers to resources"). -/
    | aliasOuterType {sc : Scopes X} {s : DefState X} {ct idx : Nat} {q : Ctx X}
        {slot : TypeSlot X} (hq : Scopes.outer? sc s.ctx ct = .ok q)
        (hslot : q.typeSlot? idx = some slot)
        (hres : crossesComponent sc s.ctx ct = true → slot.def_.fv = []) :
        ValidDef feat P validCore sc s (.alias (.outer ct idx .type))
          (s.step (s.st.withCtx (s.ctx.pushTypeSlot slot).2))
    /-- `alias outer ct i (core type)`. -/
    | aliasOuterCoreType {sc : Scopes X} {s : DefState X} {ct idx : Nat} {q : Ctx X}
        {slot : CoreTypeSlot X} (hq : Scopes.outer? sc s.ctx ct = .ok q)
        (hslot : q.coreType? idx = some slot) :
        ValidDef feat P validCore sc s (.alias (.outer ct idx (.core .type)))
          (s.step (s.st.withCtx (s.ctx.pushCoreType slot).2))
    /-- `alias outer ct i (core module)` (always substitutable). -/
    | aliasOuterCoreModule {sc : Scopes X} {s : DefState X} {ct idx : Nat} {q : Ctx X}
        {mt : CoreModuleType X} (hq : Scopes.outer? sc s.ctx ct = .ok q)
        (hm : q.coreModule? idx = some mt) :
        ValidDef feat P validCore sc s (.alias (.outer ct idx (.core .module_)))
          (s.step (s.st.withCtx (s.ctx.pushCoreModule mt).2))
    /-- `alias outer ct i (component)` (always substitutable). -/
    | aliasOuterComponent {sc : Scopes X} {s : DefState X} {ct idx : Nat} {q : Ctx X}
        {t : ComponentType Nat X} (hq : Scopes.outer? sc s.ctx ct = .ok q)
        (hc : q.component? idx = some t) :
        ValidDef feat P validCore sc s (.alias (.outer ct idx .component))
          (s.step (s.st.withCtx (s.ctx.pushComponent t).2))
    /-- `type dt`: `ValidDefType` (resources allowed, `kind = component`). -/
    | type {sc : Scopes X} {s : DefState X} {st' : DState X} {t : Syntax.DefType}
        (h : ValidDefType feat P.decl sc s.st t st') :
        ValidDef feat P validCore sc s (.type t) (s.step st')
    /-- `canon lift` / `canon lower`: `ValidCanon`. A lifted function records the contents
    requirement of its type (`canonReq`). -/
    | canon {sc : Scopes X} {s : DefState X} {c : Syntax.Canon} {e : CanonEntity X}
        (h : ValidCanon feat P.view.core s.ctx c e) :
        ValidDef feat P validCore sc s (.canon c)
          (s.step (s.st.withCtx (pushCanonEntity s.ctx e)) (canonReq s.names s.ctx c))
    /-- `canon b` of a builtin: `ValidBuiltin` (pushes a core function; `context.*` fixes the
    context type). -/
    | builtin {sc : Scopes X} {s : DefState X} {b : Syntax.Builtin} {x : X} {Γ' : Ctx X}
        (h : ValidBuiltin feat P.view s.ctx b x Γ') :
        ValidDef feat P validCore sc s (.canon (.builtin b))
          (s.step (s.st.withCtx (Γ'.pushCoreFunc x).2))
    /-- 🪙 `start f (value v)* (result (value))^r`: any number per component (Explainer
    §Start Definitions); the arguments are consumed and have the parameter types; `r` is the
    result arity; the results are pushed, recording the started function's requirement. -/
    | start {sc : Scopes X} {s : DefState X} {f : Nat} {args : List Nat} {results : Nat}
        {ft : Types.FuncType Nat} {ts : List (Types.ValType Nat)} {Γc : Ctx X}
        (hfeat : feat.values = true)
        (hf : s.ctx.func? f = some ft) (hcons : ConsumeValues s.ctx args ts Γc)
        (hargs : ts = ft.params.map (·.2)) (hres : results = ft.result.toList.length) :
        ValidDef feat P validCore sc s (.start f args results)
          (s.step (s.st.withCtx (startCtx Γc ft.result.toList)) .tt (s.funcReq f))
    /-- `import n et`: the import declarator (name validity, strong uniqueness, resolution,
    visibility against the imported types, resource binding, naming); the imported
    function/value records the requirement of `et`. -/
    | import_ {sc : Scopes X} {s : DefState X} {st' : DState X} {n : Syntax.ExternName}
        {d : Syntax.ExternDesc} (h : ValidImportDecl feat s.st n d st') :
        ValidDef feat P validCore sc s (.import_ n d)
          (s.step st' (descReq s.names s.ctx d) (descReq s.names s.ctx d))
    /-- `export n it et?`: valid, strongly unique name; `it` has an exportable entity type;
    the ascription holds; no `borrow` in an exported value; the naming requirement holds
    against the imported and exported types; the resources of the exported type are
    introduced by a preceding import/export or by this export (`resNamed`); a value item is
    consumed. The new index records the export's requirement. -/
    | export_ {sc : Scopes X} {s : DefState X} {n : Syntax.ExternName}
        {it : Syntax.SortIdx Syntax.Sort_} {asc : Option Syntax.ExternDesc}
        {e e' : Entity Nat X} {ts : List (Types.ValType Nat)} {Γc : Ctx X}
        (hname : n.valid = true) (hfresh : NameFresh (s.ctx.exports.map (·.1)) n.name)
        (hitem : itemEntity? s.ctx it = some e) (hasc : Ascribe feat P s.ctx e asc e')
        (hval : exportValueOk e' = true)
        (hvis : (exportReq s it asc).eval
          (s.ctx.importedTokens ++ s.ctx.exportedTokens) = true)
        (hres : resNamed s.ctx e' = true)
        (hcons : ConsumeValues s.ctx (valueIdxs [it]) ts Γc) :
        ValidDef feat P validCore sc s (.export_ n it asc)
          (s.step ((s.st.withCtx Γc).exportItem n.name it e') (exportReq s it asc)
            (exportReq s it asc))
    /-- 🪙 `value t payload`: a value type without handles/async/error-context, recording the
    requirement of `t`. The payload is opaque (not decoded, see the module docstring). -/
    | value {sc : Scopes X} {s : DefState X} {t : Syntax.VT} {payload : List UInt8}
        {ty : Types.ValType Nat} (hfeat : feat.values = true) (h : ResolveVT s.ctx t ty)
        (hok : valueDefTypeOk ty = true) :
        ValidDef feat P validCore sc s (.value t payload)
          (s.step (s.st.withCtx (s.ctx.pushValue ty).2) .tt (vtReq s.names s.ctx t))

  /-- Valid definitions in order. -/
  inductive ValidDefs (feat : Features) (P : DefProfile X)
      (validCore : M → Option (CoreModuleType X)) :
      Scopes X → DefState X → List (Syntax.Definition M) → DefState X → Prop
    | nil {sc : Scopes X} {s : DefState X} : ValidDefs feat P validCore sc s [] s
    | cons {sc : Scopes X} {s s' s'' : DefState X} {d : Syntax.Definition M}
        {ds : List (Syntax.Definition M)} (h : ValidDef feat P validCore sc s d s')
        (hs : ValidDefs feat P validCore sc s' ds s'') :
        ValidDefs feat P validCore sc s (d :: ds) s''
end

/-- A valid component and its type: fold the definitions from the empty component state, then close.
-/
def ValidComponent (feat : Features) (P : DefProfile X)
    (validCore : M → Option (CoreModuleType X)) (c : Syntax.Component M)
    (ct : ComponentType Nat X) : Prop :=
  ∃ s, ValidDefs feat P validCore [] initState c s ∧ ComponentDone s.ctx ∧
    ct = componentTypeOfDefs s.ctx

end Judgements

/-! ## Profile instances -/

/-- Lime1 components: `lime1ModuleType` types the core modules, which must also be valid
Lime1 modules. -/
def ValidComponentLime1 (feat : Features) (c : Syntax.Component Lime1.Module)
    (ct : ComponentType Nat CoreExternType) : Prop :=
  ValidComponent feat lime1Profile lime1ModuleType c ct ∧
    ∀ m ∈ c.coreModules, Lime1.Validation.ModuleValid m

/-- WebAssembly 1.0 components: `v1ModuleType` types the core modules, which must also be
valid V1 modules. -/
def ValidComponentV1 (feat : Features) (c : Syntax.Component V1.Module)
    (ct : ComponentType Nat CoreExternType) : Prop :=
  ValidComponent feat lime1Profile v1ModuleType c ct ∧
    ∀ m ∈ c.coreModules, V1.Validation.ModuleValid m

/-- Core 3.0 components: the Core 3.0 profile over closed extern types, core modules typed by
the Core 3.0 validator (`core3ModuleType?`), and every core module a valid Core 3.0 module.
The second conjunct follows from the first (`validComponentCore3_iff`). -/
def ValidComponentCore3 (feat : Features) (c : Syntax.Component Wasm.Module)
    (ct : ComponentType Nat Core3Extern) : Prop :=
  ValidComponent feat core3Profile core3ModuleType? c ct ∧
    ∀ m ∈ c.coreModules, Wasm.Validation.ModuleValid m

/-! ## Basic properties -/

section Properties

variable {X : Type} {M N : Type} {feat : Features} {P : DefProfile X}

end Properties

/-! ## Tests -/

namespace DefsTests

open DefTypesTests (errMsg?)
open CanonOptsTests (okVal?)

-- FLAG(statement-change): moved from `DefTypesTests`; `core3Hooks` are now the hooks over closed
-- extern types (statement text unchanged).
/-- A `rec` group of two function subtypes. -/
def recTwo : Silmaril.Wasm.RecType :=
  ⟨(V1.FuncType.toCoreRec ⟨[], []⟩).types ++ (V1.FuncType.toCoreRec ⟨[], []⟩).types⟩

-- FLAG(statement-change): moved from `DefTypesTests`; `core3Hooks` are now the hooks over closed
-- extern types (statement text unchanged).
/-- `(type (sub (func (param i32))))`, a non-final function type. -/
def openI32 : Silmaril.Wasm.RecType := ⟨[⟨false, [], .func ⟨[.num (.int .i32)], []⟩⟩]⟩

/-- The Explainer adder (`Explainer.md` §Canonical ABI) over the V1 module `CoreModules.addModule`:
`(core module $M ...) (core instance $m (instantiate $M)) (alias core export $m "add" (core func))
(type (func (param "a" u32) (param "b" u32) (result u32))) (canon lift ...) (export "add" (func
0))`. -/
def adder : Syntax.Component V1.Module :=
  [.coreModule CoreModules.addModule,
   .coreInstance (.instantiate 0 []),
   .alias (.coreExport 0 "add" .func),
   .type (.func { params := [("a", .prim .u32), ("b", .prim .u32)], result := some (.prim .u32) }),
   .canon (.lift 0 [] 0),
   .export_ { name := "add" } ⟨.func, 0⟩ none]

/-- The adder's function type. -/
def adderFunc : Types.FuncType Nat :=
  { params := [("a", .prim .u32), ("b", .prim .u32)], result := some (.prim .u32) }

/-- The adder's component type: no imports, one export `add`. -/
def adderType : ComponentType Nat CoreExternType := ⟨[], [], [], [("add", .func adderFunc)]⟩

/-- A state whose component index space holds a component importing `a : func`. -/
def stImp : DefState CoreExternType :=
  { st := { ctx := { kind := .component,
                     components := [⟨[], [("a", .func adderFunc)], [], []⟩] } } }

/-- A parent component defining resource `0` at type index 0, and an empty child component
scope. -/
def parentCtx : Ctx CoreExternType :=
  { kind := .component, types := [⟨.resource 0, 0⟩], definedRes := [(0, some .i32)],
    nextVar := 1, nextToken := 1 }

/-- A component type with one defined (∃) resource `7`, exported as `r`. -/
def resComp : ComponentType Nat CoreExternType := ⟨[], [], [7], [("r", .type (.resource 7))]⟩

/-- The instantiated instance of `resComp` from a state with `nextVar = 3`. -/
def resInst : DState CoreExternType :=
  DState.instantiate { ctx := Ctx.empty .component 3 0 } resComp id

/-- The exported resource of the instance is the fresh variable `3`. -/
def resInstFresh : Bool :=
  match resInst.ctx.instance? 0 with
  | some ⟨[], [("r", .type (.resource v))]⟩ => v == 3
  | _ => false

/-- A state whose function 0 carries the naming requirement of a use of the nominal token `5`
(e.g. a locally defined `record` that was never exported), nothing imported or exported. -/
def stUnnamed : DefState CoreExternType :=
  { st := { ctx := { kind := .component, funcs := [adderFunc] } },
    funcReqs := [(0, .use 5 false .tt)] }

/-- A function taking `own 0`, for a resource `0` defined here. -/
def resFunc : Types.FuncType Nat := { params := [("x", .own 0)], result := none }

/-- Resource `0` is defined locally but neither imported nor exported; function 0 uses it. -/
def stRes : DefState CoreExternType :=
  { st := { ctx := { kind := .component, funcs := [resFunc], definedRes := [(0, some .i32)],
                     nextVar := 1 } } }

/-! ### `thread.new-indirect` tables under the Core 3.0 profile -/

/-- A closed table `(table a lim r)` as a `Core3Extern` (empty when it is not valid). -/
def core3Tbl (a : AddrType) (lim : Silmaril.Wasm.Limits) (r : Wasm.Validation.CRefType) : List Core3Extern :=
  (core3Ext? (.table ⟨a, lim, r⟩)).toList

/-- Tables 0 `(table 0 (ref null nofunc))`, 1 `(table i64 1 (ref func))`, 2 `(table 0
externref)`, 3 `(table 0 (ref null $t))` for the closed `$t = (func)`, 4 `(table 0 funcref)`;
core type 0 `(func (param i32))`. -/
def core3TblCtx : Ctx Core3Extern :=
  { kind := .component
    coreTypes := [BuiltinsTests.startGroup [.i32] []]
    coreTables := core3Tbl .i32 ⟨0, none⟩ (.ref true (.abs .nofunc)) ++
      core3Tbl .i64 ⟨1, none⟩ (.ref false (.abs .func)) ++
      core3Tbl .i32 ⟨0, none⟩ Wasm.Validation.Ty.externref ++
      core3Tbl .i32 ⟨0, none⟩
        (.ref true (Wasm.Validation.Ty.defHeap (V1.FuncType.toDefType ⟨[], []⟩))) ++
      core3Tbl .i32 ⟨0, none⟩ Wasm.Validation.Ty.funcref }

end DefsTests

end Silmaril.Wasm.Component.Validation
