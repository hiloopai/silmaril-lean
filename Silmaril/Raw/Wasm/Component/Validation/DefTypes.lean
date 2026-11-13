module

public import Silmaril.Wasm.Component.Reference.Validation.DefTypes.Thms
public import Silmaril.Wasm.Component.Reference.Validation.DefTypes.Defs

-- Kernel computation uses the body of the upstream derived instance.
import all Batteries.Data.Except

public import Silmaril.Raw.Wasm.Component.Validation.ValTypes
public import Silmaril.Raw.Wasm.Component.Syntax.Names
public import Silmaril.Wasm.Component.Engine.Interface
public import Silmaril.Wasm.V1.ToCore.Types
public import Silmaril.Wasm.Validation.Types
import all Init.Data.String.Defs
import all Init.Data.Repr

/-!
# Validation of type definitions: resources and component/instance type declarators

The `deftype` rules of `Binary.md` §Type Definitions at component-model `a25fc0b`
(https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/Binary.md),
with `Explainer.md` §Declarators, §Type Checking and §External Visibility of Types, following
wasmparser's `ComponentState` (`crates/wasmparser/src/validator/component.rs`).

A type definition `Syntax.DefType` is checked against a *declarator state* `DState X`: the
validation context `Ctx X` (`Validation/Context.lean`), the global naming table `NameTable` (see
below), and the naming data of the exports declared so far in the current scope. The judgements are:

* `ValidDefType feat hk sc st d st'`: definition `d` is valid in `st` (with enclosing scopes
  `sc`) and pushes one entry into the type index space, giving `st'`.
  - `val`/`func`: the judgements `ValidDefValType` / `ValidFuncType` of `Validation/ValTypes.lean`.
  - `resource rep dtor`: only when `kind = component` ("resources can only be defined within a
    concrete component"); `rep = i32`, or `i64` under 🐘; the destructor, if any, is a core
    function whose type passes the profile hook `DeclHooks.dtorOk rep` (`[rep] -> []`,
    "wrong signature for a destructor"). A fresh variable `v = nextVar` is allocated,
    recorded as `definedRes (v, some rep)`, and `resource v` is pushed.
  - `instance_ ds` / `component ds`: the declarators are checked in a *fresh* scope
    (`Scopes.enter`, all index spaces empty, kind `instanceType`/`componentType`); the
    resulting type is `⟨definedRes, exports⟩` resp. `⟨importedRes, imports, definedRes,
    exports⟩` of the child context; counters are handed back to the parent.
* `ValidInstanceDecl`, `ValidComponentDecl` and their list forms: the declarators.
  - `core type`: a `rec` group is pushed unchecked; a core module type is validated by
    `ValidCoreModuleType` in an *empty* core type space: module-local `type` decls (a group of
    `n` subtypes occupies `n` local indices); outer aliases of count 0 (the module type) or
    `c + 1` (the `c`-th enclosing scope, innermost first, starting with the scope containing
    the `core type`; wasmparser `check_alias_count(components, count - 1)`), which may only
    target recursion groups, never module types (Explainer.md l.549, "validation will also
    reject `core:moduletype` defining or aliasing other `core:moduletype`s"); imports/exports
    resolved by the profile hook `DeclHooks.coreExtern?`, which also validates memory, table
    and global types; duplicate `(module, name)` imports and duplicate export names
    rejected.
  - `type`: `ValidDefType` recursively (so a `resource` definition is rejected).
  - `alias`: `alias export i "n" (s)` only for `s ∈ {instance, type}` (the export must exist
    with that sort; identities are kept by `Ctx.aliasInstanceExport?`); `alias outer ct i (s)`
    only for `s ∈ {core type, type}`; an outer `type` alias that crosses a `component`
    boundary must not transitively refer to resources (`TypeDef.fv = []`). Every other alias is
    rejected ("may only refer to types or instances").
  - `import`/`export` decls: the name is a valid `externname` and strongly unique among the
    imports (resp. exports) of the scope; the `externtype` resolves (`ResolveDesc`); the entity
    is pushed into the index space of its sort (`Ctx.pushImportEntity` /
    `Ctx.pushExportEntity`). `(eq i)` pushes the type of `i` (an alias: same resource
    variable); `(sub resource)` allocates the fresh variable `nextVar`. Imported resources
    (the `(sub resource)` variable, and the ∃-binders of an imported instance type, renamed to
    fresh variables) become `importedRes` with their path; exported ones become
    `definedRes (v, none)` and `explicitRes`. Imported/exported instance types are pushed with
    `defined = []` (binder hoisting, the convention of `Types/Basic.lean`).
  - External visibility (`Explainer.md` §External Visibility of Types): outside instance types, an
    import's naming requirement must hold against `importedTokens`, an export's against
    `importedTokens ++ exportedTokens`, with wasmparser's messages "{sort} not valid to be used as
    {import|export}".

**Naming requirements.** Types are index-free, so which *index* a nested type came from (and
hence whether it has an externally visible name) is not recoverable from the semantic type.
Each naming token (`TypeSlot.token`) therefore gets a `TokInfo` in a global table
`NameTable` (tokens are globally fresh): whether the type is *transparent* (not
`record`/`variant`/`enum`/`flags`/`resource`, so it needs no name of its own), the requirement
`contents : NameReq` on the types it refers to one layer down, and, for instance/component
types, the inner tokens of their type exports by path. `NameReq.eval S` decides a requirement
against a visibility set `S`: a use of token `t` holds iff `t ∈ S` or (the type is
transparent and its contents hold). An instance type's contents are checked with its own
exported tokens visible (`NameReq.scoped`). When an instance type is imported/exported, the
tokens of its type exports are re-registered under the fresh tokens allocated by the push,
with inner tokens renamed (`registerNames`). Tokens without an entry are treated as nominal
with no contents (conservative).

**Executable checkers.** `checkDefType?` (with `checkInstanceDecl?`, `checkComponentDecl?`
and the list forms, structurally recursive) and `checkCoreModuleType?`. Soundness:
`checkDefType?_sound`, `checkInstanceDecls?_sound`, `checkComponentDecls?_sound` (and the
single-declarator forms). Completeness: `checkDefType?_complete`,
`checkInstanceDecl(s)?_complete`, `checkComponentDecl(s)?_complete`, hence
`checkDefType?_iff`; the leaves are complete too (`importDecl?_complete`,
`exportDecl?_complete`, `aliasDecl?_complete`, `coreTypeDecl?_iff`,
`checkCoreModuleType?_iff`, `resolveDesc?_iff`, `resourceDef?_iff`).

**Profile hooks** `DeclHooks X`: `lime1Hooks` for `Engine.CoreExternType` (function types
must be a final, parent-free one-type recursion group of numeric types; tables funcref;
globals numeric; memories and tables with address type `i32` and valid limits
(`MemoryType.Valid`, `TableType.Valid`); tags rejected, since Lime1/V1 have no exception
handling; destructors exactly `[rep] -> []`; recursion groups (component level and inside
module types) only numeric one-type function groups). The Core 3.0 hooks `core3Hooks`, over
closed extern types, are in `Validation/Defs.lean` (they need the Core 3.0 type checkers).

Error messages: wasmparser's (matched by `test/validation/*.wast` substrings) for
"resources can only be defined within a concrete component", "wrong signature for a
destructor", "... not valid to be used as import/export", "may only refer to types or
instances", "transitively refers to resources", "invalid outer alias count", "export name
`a` conflicts with previous name `a`", "duplicate import name `m:n`", "name `n` already
defined", "type index out of bounds", "memory size must be at most 65536 pages (4GiB)" / "...
2**48 pages", "size minimum must not be greater than maximum"; the others ("is not a function
type", ...) are descriptive and not verified.

Design notes and deviations:

* Resource paths (`importedRes`/`explicitRes`) are the declarator's import/export index
  followed by the export positions inside the (nested) instance type (`Entity.resPath?`).
* The visibility check at the top of an import/export uses the *contents* of the referenced
  type (the declarator names the type itself). `(sub resource)`, core modules and components
  (closed) have no requirement.
* The outer-alias resource check is `TypeDef.fv ≠ []` (free variables; binders of nested
  component/instance types excluded).
* 🪙 values in declarators: gated by `feat.values`, pushed without linearity tracking; an
  exported value type must not contain `borrow`.
* Resource names for `[method]`/`[constructor]` annotation typing, feature gates on names (🏷️, 🪺, 🔗,
  📡) and `implements` attributes are NOT checked here.
* Core `rec` groups pass the structural check of `recGroupError?` and the profile hook
  `DeclHooks.recOk`, which sees the preceding core types (the Core 3.0 hook runs `Type_ok`).
* Core type indices: a `rec` group of `n` subtypes occupies `n` indices, both inside a module
  type and in the component-level core type space `Ctx.coreTypes` (which outer aliases read).
  Slot `k` holds the whole group, the member index and the member's closed defined type
  (`CoreTypeSlot.ofRec`), which an outer alias copies unchanged.
* Module-type messages "module types cannot define or alias other module types" and
  "table size must be at most ... elements" are descriptive.

Tests (kernel-checked, `decide +kernel`, plus two relational corollaries): an instance type
with a `(sub resource)` export yields the fresh variable `nextVar` as its ∃-binder (and two such
exports two distinct variables; `instance_sub_resource_valid` obtains the relational judgement
via soundness); a resource definition inside a component type and inside an instance type is
rejected with "resources can only be defined within a concrete component"
(`resources.wast` 729-739; `not_valid_resource_in_component_type` refutes the relation
directly); resource definitions at component level with a destructor of the right/wrong
signature (`resources.wast` 750-756) and the 🐘 `rep i64` gate; a component type importing a
`(sub resource)` and exporting a function over it; importing an instance type, aliasing its
resource and exporting a function over it; `external-visibility.wast` 394-399 (import referring
to a preceding export's resource), 385-390 (export of an unnamed record, and the instance-type
variant 322-326 that skips the check), 306-310 / 312-317 (type imports enforcing naming, inside a
component type); `outer-alias.wast` 173-180 (alias export of a func) and 196-201 (outer alias
of a component), an outer resource alias crossing a component boundary (shape of 69-76), an
invalid outer alias count; `core-modules.wast` 36-42 and 72-81 (inside an instance type),
50-56 (memory of 70000 pages) and 110-117 (module-type imports);
module types aliasing a module type (rejected), an outer alias of count 2 into the enclosing
component (accepted) and count 3 (rejected); limits with minimum above maximum; Lime1
rejection of tags and 64-bit memories; strong
uniqueness of import and export names (`instantiation.wast` 522-527 shape). Upstream cases
are mirrored in declarator form, not replayed from the `.wast` files.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Validation

open Silmaril.Wasm.Component.Types
open Silmaril.Wasm.Component.Engine (CoreExternType)

variable {X : Type}

/-! ## Naming requirements (`Explainer.md` §External Visibility of Types) -/

namespace NameReq

end NameReq

/-! ## Declarator state and profile hooks -/

namespace DState

end DState

namespace DState

end DState

/-! ## Core module types (validated in an empty core type space) -/

/-! ## Resolving an `externtype` -/

private theorem typeSlotAt?_eq_ok {Γ : Ctx X} {i : Nat} {s : TypeSlot X} :
    Γ.typeSlotAt? i = .ok s ↔ Γ.types[i]? = some s := Ctx.listAt?_eq_ok

private theorem type?_eq_some {Γ : Ctx X} {i : Nat} {d : TypeDef Nat X} :
    Γ.type? i = some d ↔ ∃ s, Γ.types[i]? = some s ∧ s.def_ = d := by
  simp only [Ctx.type?, Option.map_eq_some_iff]

/-! ## Binder hoisting and resource paths -/

namespace DState

end DState

/-! ## Leaf declarators -/

/-! ## Completeness of the leaf declarators -/

theorem conflict?_of_nameFresh {names : List String} {n : String} (h : NameFresh names n) :
    conflict? names n = none := by
  unfold conflict?
  rw [List.find?_eq_none]
  intro p hp
  simpa using h p hp

theorem importDecl?_complete {feat : Features} {st st' : DState X} {n : Syntax.ExternName}
    {d : Syntax.ExternDesc} (h : ValidImportDecl feat st n d st') :
    importDecl? feat st n d = .ok st' := by
  cases h with
  | mk hn hf hd hv =>
    simp only [importDecl?, hn, conflict?_of_nameFresh hf, resolveDesc?_iff.mpr hd, hv,
      ite_true]

theorem exportDecl?_complete {feat : Features} {st st' : DState X} {n : Syntax.ExternName}
    {d : Syntax.ExternDesc} (h : ValidExportDecl feat st n d st') :
    exportDecl? feat st n d = .ok st' := by
  cases h with
  | mk hn hf hd hval hv =>
    simp only [exportDecl?, hn, conflict?_of_nameFresh hf, resolveDesc?_iff.mpr hd, hval, hv,
      ite_true]

theorem aliasDecl?_complete {sc : Scopes X} {st st' : DState X} {a : Syntax.Alias}
    (h : ValidAlias sc st a st') : aliasDecl? sc st a = .ok st' := by
  cases h with
  | export_ hs h hsort =>
    rcases hs with rfl | rfl <;> simp [aliasDecl?, h, hsort]
  | outerType hq hslot hres =>
    have hs : Ctx.typeSlotAt? _ _ = .ok _ := Ctx.listAt?_eq_ok.mpr hslot
    simp only [aliasDecl?, hq, hs]
    cases hc : crossesComponent sc st.ctx _
    · rfl
    · simp [hres hc]
  | outerCoreType hq hslot =>
    have hs : Ctx.coreTypeAt? _ _ = .ok _ := Ctx.listAt?_eq_ok.mpr hslot
    simp only [aliasDecl?, hq, hs]

/-! ## Resource definitions -/

/-! ## Type definitions and declarators (mutually recursive) -/

section Soundness

variable {feat : Features} {hk : DeclHooks X}

end Soundness

section Completeness

variable {feat : Features} {hk : DeclHooks X}

mutual
  /-- Completeness of `checkDefType?`. -/
  theorem checkDefType?_complete {sc : Scopes X} {st st' : DState X} {d : Syntax.DefType} :
      ValidDefType feat hk sc st d st' → checkDefType? feat hk sc st d = .ok st'
    | .val h => by simp only [checkDefType?, checkDefValType?_complete h]
    | .func h => by simp only [checkDefType?, checkFuncType?_complete h]
    | .resource h => by
      simp only [checkDefType?]
      exact resourceDef?_iff.mpr ⟨h, rfl⟩
    | .instance_ h => by simp only [checkDefType?, checkInstanceDecls?_complete h]
    | .component h => by simp only [checkDefType?, checkComponentDecls?_complete h]

  /-- Completeness of `checkInstanceDecl?`. -/
  theorem checkInstanceDecl?_complete {sc : Scopes X} {st st' : DState X}
      {d : Syntax.InstanceDecl} :
      ValidInstanceDecl feat hk sc st d st' → checkInstanceDecl? feat hk sc st d = .ok st'
    | .coreType h => coreTypeDecl?_iff.mpr h
    | .type h => checkDefType?_complete h
    | .alias h => aliasDecl?_complete h
    | .export_ h => exportDecl?_complete h

  /-- Completeness of `checkComponentDecl?`. -/
  theorem checkComponentDecl?_complete {sc : Scopes X} {st st' : DState X}
      {d : Syntax.ComponentDecl} :
      ValidComponentDecl feat hk sc st d st' → checkComponentDecl? feat hk sc st d = .ok st'
    | .import_ h => importDecl?_complete h
    | .decl h => checkInstanceDecl?_complete h

  /-- Completeness of `checkInstanceDecls?`. -/
  theorem checkInstanceDecls?_complete {sc : Scopes X} {st st' : DState X}
      {ds : List Syntax.InstanceDecl} :
      ValidInstanceDecls feat hk sc st ds st' → checkInstanceDecls? feat hk sc st ds = .ok st'
    | .nil => rfl
    | .cons h hs => by
      simp only [checkInstanceDecls?, checkInstanceDecl?_complete h,
        checkInstanceDecls?_complete hs]

  /-- Completeness of `checkComponentDecls?`. -/
  theorem checkComponentDecls?_complete {sc : Scopes X} {st st' : DState X}
      {ds : List Syntax.ComponentDecl} :
      ValidComponentDecls feat hk sc st ds st' →
        checkComponentDecls? feat hk sc st ds = .ok st'
    | .nil => rfl
    | .cons h hs => by
      simp only [checkComponentDecls?, checkComponentDecl?_complete h,
        checkComponentDecls?_complete hs]
end

/-- `checkDefType?` decides `ValidDefType`. -/
theorem checkDefType?_iff {sc : Scopes X} {st st' : DState X} {d : Syntax.DefType} :
    checkDefType? feat hk sc st d = .ok st' ↔ ValidDefType feat hk sc st d st' :=
  ⟨checkDefType?_sound d, checkDefType?_complete⟩

end Completeness

/-! ## Profile hooks -/

/-! ## Tests -/

namespace DefTypesTests

theorem instance_sub_resource_fresh : isFreshInst (lastType? (run instSubResource)) = true := by
  decide +kernel

theorem instance_two_sub_resources_fresh : isTwoFresh (run instTwo) = true := by decide +kernel

/-- Soundness applied: the relational judgement holds for the instance type. -/
theorem instance_sub_resource_valid :
    ∃ st', ValidDefType Features.all lime1Hooks [] st0 instSubResource st' := by
  cases h : run instSubResource with
  | error e =>
    have : isFreshInst (lastType? (run instSubResource)) = true := instance_sub_resource_fresh
    rw [h] at this; cases this
  | ok st' => exact ⟨st', checkDefType?_sound _ h⟩

/-- `resources.wast` 729-733: a resource definition inside a component type is rejected. -/
theorem resource_in_component_type :
    errMsg? (run (.component [.decl (.type (.resource .i32 none))])) =
      some "resources can only be defined within a concrete component" := by decide +kernel

/-- `resources.wast` 735-739: ... and inside an instance type. -/
theorem resource_in_instance_type :
    errMsg? (run (.instance_ [.type (.resource .i32 none)])) =
      some "resources can only be defined within a concrete component" := by decide +kernel

theorem not_valid_resource_in_component_type (st' : DState CoreExternType) :
    ¬ ValidDefType Features.all lime1Hooks [] st0
      (.component [.decl (.type (.resource .i32 none))]) st' := by
  intro h
  cases h with
  | component h =>
    cases h with
    | cons h _ =>
      cases h with
      | decl h =>
        cases h with
        | type h =>
          cases h with
          | resource h => exact absurd h.kindOk (by decide)

/-- A concrete resource definition with a destructor `[i32] -> []` allocates `nextVar`. -/
theorem resource_def_ok :
    (match run (.resource .i32 (some 0)) with
     | .ok st =>
       (st.ctx.localRep? 1 == some .i32) && st.ctx.nextVar == 2 &&
         (match st.ctx.type? 1 with | some (.resource v) => v == 1 | _ => false)
     | .error _ => false) = true := by decide +kernel

/-- `resources.wast` 750-756: a destructor of the wrong type. -/
theorem resource_dtor_wrong :
    errMsg? (run (.resource .i32 (some 1))) = some "wrong signature for a destructor" := by
  decide +kernel

/-- `rep i64` needs 🐘. -/
theorem resource_i64_gate :
    errMsg? (checkDefType? Features.p3 lime1Hooks [] st0 (.resource .i64 none)) =
      some "resource representation `i64` requires the component model memory64 feature" := by
  decide +kernel

theorem component_type_import_resource : isCompType (lastType? (run compType)) = true := by
  decide +kernel

/-- `external-visibility.wast` 394-399: within a component type, an import may not reference a
preceding export's resource. -/
theorem import_refers_to_export :
    errMsg? (run (.component [.decl (.export_ { name := "r" } (.type .subResource)),
      .decl (.type (.val (.own 0))),
      .decl (.type (.func { params := [], result := some (.idx 1) })),
      .import_ { name := "f" } (.func 2)])) =
      some "func not valid to be used as import" := by decide +kernel

/-- `external-visibility.wast` 385-390: exporting `(eq $Rec2)` where `$Rec` has no name. -/
theorem export_unnamed_record :
    errMsg? (run (.component [.decl (.type (.val (.record [("x", .prim .u32)]))),
      .decl (.type (.val (.record [("r", .idx 0)]))),
      .decl (.export_ { name := "t" } (.type (.eq 1)))])) =
      some "type not valid to be used as export" := by decide +kernel

/-- The same inside an instance type is accepted (the check is skipped, lines 322-326). -/
theorem instance_skips_visibility :
    (run (.instance_ [.type (.val (.record [("x", .prim .u32)])),
      .type (.val (.record [("r", .idx 0)])),
      .export_ { name := "t" } (.type (.eq 1))])).toOption.isSome = true := by decide +kernel

/-- `external-visibility.wast` 306-310 (in a component type): importing the inner record first
makes the outer type import valid. -/
theorem import_named_record_ok :
    (run (.component [.decl (.type (.val (.record [("x", .prim .u32)]))),
      .import_ { name := "rec" } (.type (.eq 0)),
      .decl (.type (.val (.record [("r", .idx 1)]))),
      .import_ { name := "t" } (.type (.eq 2))])).toOption.isSome = true := by decide +kernel

/-- `external-visibility.wast` 312-317 (in a component type). -/
theorem import_unnamed_record :
    errMsg? (run (.component [.decl (.type (.val (.record [("x", .prim .u32)]))),
      .decl (.type (.val (.record [("r", .idx 0)]))),
      .import_ { name := "t" } (.type (.eq 1))])) =
      some "type not valid to be used as import" := by decide +kernel

/-- Importing an instance type re-registers its type exports under fresh tokens: a function
over the instance's resource, aliased out, may be exported. -/
theorem import_instance_alias_export_ok :
    (run (.component [
      .decl (.type (.instance_ [.export_ { name := "r" } (.type .subResource)])),
      .import_ { name := "i" } (.instance_ 0),
      .decl (.alias (.export_ 0 "r" .type)),
      .decl (.type (.val (.own 1))),
      .decl (.type (.func { params := [], result := some (.idx 2) })),
      .decl (.export_ { name := "f" } (.func 3))])).toOption.isSome = true := by decide +kernel

/-- `outer-alias.wast` 173-180: `alias export` of a func in a component type. -/
theorem alias_export_func :
    errMsg? (run (.component [
      .decl (.type (.instance_ [.type (.func { params := [], result := none }),
        .export_ { name := "f" } (.func 0)])),
      .import_ { name := "i" } (.instance_ 0),
      .decl (.alias (.export_ 0 "f" .func))])) =
      some "aliases in component and instance types may only refer to types or instances" := by
  decide +kernel

/-- `outer-alias.wast` 196-201: `alias outer` of a component in an instance type. -/
theorem alias_outer_component :
    errMsg? (run (.instance_ [.alias (.outer 1 0 .component)])) =
      some "aliases in component and instance types may only refer to types or instances" := by
  decide +kernel

/-- An outer alias of the enclosing component's resource into a type declarator does not cross
a component boundary and is accepted; through a nested component type into another it is
(`outer-alias.wast` 69-76 shape: the scope stack holds a component). -/
theorem alias_outer_resource_type_ok :
    (run (.instance_ [.alias (.outer 1 0 .type)])).toOption.isSome = true := by decide +kernel

theorem alias_outer_resource_crossing :
    errMsg? (checkDefType? Features.all lime1Hooks [compCtx]
      { ctx := { compCtx with types := [] }, names := [] }
      (.component [.decl (.alias (.outer 2 0 .type))])) =
      some "type index 0 transitively refers to resources" := by decide +kernel

theorem alias_outer_bad_count :
    errMsg? (run (.instance_ [.alias (.outer 3 0 .type)])) =
      some "invalid outer alias count of 3" := by decide +kernel

/-- `core-modules.wast` 36-42: module-type export of an out-of-bounds type index. -/
theorem core_module_type_oob :
    errMsg? (run (.instance_ [.coreType (.module_ [.export_ "a" (.func ⟨0⟩)])])) =
      some "unknown type 0: type index out of bounds" := by decide +kernel

/-- `core-modules.wast` 72-81: duplicate module-type exports inside an instance type. -/
theorem core_module_type_dup_export :
    errMsg? (run (.instance_ [.coreType (.module_ [
      .type (V1.FuncType.toCoreRec ⟨[], []⟩),
      .export_ "" (.func ⟨0⟩), .export_ "" (.func ⟨0⟩)])])) =
      some "export name `` already defined" := by decide +kernel

/-- `core-modules.wast` 110-117: duplicate two-level imports in a module type. -/
theorem core_module_type_dup_import :
    errMsg? (checkCoreModuleType? lime1Hooks [compCtx] [
      .type (V1.FuncType.toCoreRec ⟨[], []⟩),
      .import_ "" "a" (.func ⟨0⟩), .import_ "" "a" (.func ⟨0⟩)]) =
      some "duplicate import name `:a`" := by decide +kernel

-- FLAG(statement-change): the outer core type slot is built by `CoreTypeSlot.ofRec`, which now
-- also records its closed defined type.
/-- A valid module type with a local function type, an outer-aliased one and a memory. -/
theorem core_module_type_ok :
    checkCoreModuleType? lime1Hooks
      [{ compCtx with
        coreTypes := CoreTypeSlot.ofRec [] (V1.FuncType.toCoreRec ⟨[.int .i32], []⟩) }]
      [.type (V1.FuncType.toCoreRec ⟨[], []⟩), .aliasOuter 1 0,
       .import_ "env" "f" (.func ⟨1⟩), .export_ "g" (.func ⟨0⟩)] =
      .ok ⟨[(("env", "f"), .func ⟨[.int .i32], []⟩)], [("g", .func ⟨[], []⟩)]⟩ := by
  decide +kernel

/-- Explainer.md l.549: a module type may not alias another module type. -/
theorem core_module_type_alias_module :
    errMsg? (run (.instance_ [.coreType (.module_ []),
      .coreType (.module_ [.aliasOuter 1 0])])) =
      some "module types cannot define or alias other module types" := by decide +kernel

theorem core_module_type_alias_count_two :
    (checkDefType? Features.all lime1Hooks [] stF
      (.component [.decl (.coreType (.module_ [.aliasOuter 2 0,
        .export_ "f" (.func ⟨0⟩)]))])).toOption.isSome = true := by decide +kernel

theorem core_module_type_alias_count_three :
    errMsg? (checkDefType? Features.all lime1Hooks [] stF
      (.component [.decl (.coreType (.module_ [.aliasOuter 3 0]))])) =
      some "invalid outer alias count of 3" := by decide +kernel

/-- `core-modules.wast` 50-56: a module-type memory import above 65536 pages. -/
theorem core_module_type_memory_too_large :
    errMsg? (checkCoreModuleType? lime1Hooks [compCtx]
      [.import_ "" "" (.memory ⟨.i32, ⟨70000, none⟩⟩)]) =
      some "memory size must be at most 65536 pages (4GiB)" := by decide +kernel

/-- Limits with minimum above maximum. -/
theorem core_module_type_memory_min_gt_max :
    errMsg? (checkCoreModuleType? lime1Hooks [compCtx]
      [.export_ "m" (.memory ⟨.i32, ⟨5, some 2⟩⟩)]) =
      some "size minimum must not be greater than maximum" := by decide +kernel

/-- Lime1 has no exception tags and no 64-bit memories. -/
theorem core_module_type_lime1_tag :
    (checkCoreModuleType? lime1Hooks [compCtx]
      [.type (V1.FuncType.toCoreRec ⟨[], []⟩), .import_ "" "t" (.tag ⟨0⟩)]).toOption.isNone
      = true := by decide +kernel

theorem core_module_type_lime1_memory64 :
    (checkCoreModuleType? lime1Hooks [compCtx]
      [.import_ "" "m" (.memory ⟨.i64, ⟨1, none⟩⟩)]).toOption.isNone = true := by
  decide +kernel

/-- Import names are strongly unique within a component type. -/
theorem import_name_conflict :
    errMsg? (run (.component [.import_ { name := "a-b" } (.type .subResource),
      .import_ { name := "A-B" } (.type .subResource)])) =
      some "import name `A-B` conflicts with previous name `a-b`" := by decide +kernel

/-- `instantiation.wast` 522-527 shape: duplicate export names. -/
theorem export_name_conflict :
    errMsg? (run (.instance_ [.export_ { name := "a" } (.type .subResource),
      .export_ { name := "a" } (.type .subResource)])) =
      some "export name `a` conflicts with previous name `a`" := by decide +kernel

end DefTypesTests

end Silmaril.Wasm.Component.Validation
