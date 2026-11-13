module

import all Batteries.Data.Except
public import Silmaril.Wasm.Component.Reference.Validation.ValTypes.Defs
public import Silmaril.Wasm.Component.Reference.Syntax.Names.Defs
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

/-- A naming requirement over naming tokens. -/
inductive NameReq where
  /-- No requirement. -/
  | tt
  /-- Both requirements. -/
  | and (a b : NameReq)
  /-- A use of the type with token `tok`: satisfied if `tok` is visible, or if the type is
  `transparent` (needs no name of its own) and its `contents` are satisfied. -/
  | use (tok : Nat) (transparent : Bool) (contents : NameReq)
  /-- `r`, with the tokens `extra` additionally visible (the type exports of an instance
  type name its own exported types). -/
  | scoped (extra : List Nat) (r : NameReq)
  deriving Repr, DecidableEq

namespace NameReq

/-- Decide a requirement against the visibility set `S`. -/
def eval : List Nat → NameReq → Bool
  | _, .tt => true
  | S, .and a b => eval S a && eval S b
  | S, .use t tr c => S.contains t || (tr && eval S c)
  | S, .scoped ex r => eval (ex ++ S) r

/-- The conjunction of a list of requirements. -/
def all : List NameReq → NameReq
  | [] => .tt
  | r :: rs => .and r (all rs)

/-- Rename the tokens of a requirement. -/
def rename (g : Nat → Nat) : NameReq → NameReq
  | .tt => .tt
  | .and a b => .and (rename g a) (rename g b)
  | .use t tr c => .use (g t) tr (rename g c)
  | .scoped ex r => .scoped (ex.map g) (rename g r)

end NameReq

/-- The naming information of a token: transparency, the requirement on the types it refers to
one layer down, and (for instance/component types) the inner tokens of its type exports by
path. The default is a nominal type with no contents. -/
structure TokInfo where
  transparent : Bool := false
  contents : NameReq := .tt
  paths : List (List String × Nat) := []
  deriving Repr, DecidableEq

/-- The global naming table, keyed by (globally fresh) naming tokens; the first entry wins. -/
abbrev NameTable := List (Nat × TokInfo)

/-- The information of a token (default: nominal, no contents). -/
def tokInfo (tbl : NameTable) (tok : Nat) : TokInfo := (tbl.lookup tok).getD {}

/-- The requirement of a use of type index `i`. -/
def idxReq (tbl : NameTable) (Γ : Ctx X) (i : Nat) : NameReq :=
  match Γ.typeSlot? i with
  | some s => let inf := tokInfo tbl s.token; .use s.token inf.transparent inf.contents
  | none => .tt

/-- The requirement of a `valtype`. -/
def vtReq (tbl : NameTable) (Γ : Ctx X) : Syntax.VT → NameReq
  | .prim _ => .tt
  | .idx i => idxReq tbl Γ i

/-- The requirement of an optional `valtype`. -/
def optVTReq (tbl : NameTable) (Γ : Ctx X) : Option Syntax.VT → NameReq
  | none => .tt
  | some v => vtReq tbl Γ v

/-- The contents requirement of a `defvaltype` (one layer down). -/
def defValReq (tbl : NameTable) (Γ : Ctx X) : Syntax.DefValType → NameReq
  | .prim _ | .flags _ | .enum _ => .tt
  | .record fs => .all (fs.map fun f => vtReq tbl Γ f.2)
  | .variant cs => .all (cs.map fun c => optVTReq tbl Γ c.2)
  | .list t | .fixedList t _ | .option t => vtReq tbl Γ t
  | .tuple ts => .all (ts.map (vtReq tbl Γ))
  | .result a b => .and (optVTReq tbl Γ a) (optVTReq tbl Γ b)
  | .map k v => .and (vtReq tbl Γ k) (vtReq tbl Γ v)
  | .own r | .borrow r => idxReq tbl Γ r
  | .stream t | .future t => optVTReq tbl Γ t

/-- `record`, `variant`, `enum` and `flags` need a name of their own. -/
def nominalDefVal : Syntax.DefValType → Bool
  | .record _ | .variant _ | .enum _ | .flags _ => true
  | _ => false

/-- The naming information of a `defvaltype`. -/
def valInfo (tbl : NameTable) (Γ : Ctx X) (d : Syntax.DefValType) : TokInfo :=
  { transparent := !nominalDefVal d, contents := defValReq tbl Γ d }

/-- The naming information of a `functype`: parameter and result types. -/
def funcInfo (tbl : NameTable) (Γ : Ctx X) (ft : Syntax.FuncType) : TokInfo :=
  { transparent := true,
    contents := .and (.all (ft.params.map fun p => vtReq tbl Γ p.2)) (optVTReq tbl Γ ft.result) }

/-- The contents requirement of type index `i`. -/
def contentsOf (tbl : NameTable) (Γ : Ctx X) (i : Nat) : NameReq :=
  match Γ.typeSlot? i with
  | some s => (tokInfo tbl s.token).contents
  | none => .tt

/-- The naming requirement checked when an `externtype` is imported or exported. -/
def descReq (tbl : NameTable) (Γ : Ctx X) : Syntax.ExternDesc → NameReq
  | .func i | .type (.eq i) | .instance_ i => contentsOf tbl Γ i
  | .value (.type vt) => vtReq tbl Γ vt
  | _ => .tt

/-- The visibility condition: skipped inside instance types. -/
def visibleOk (k : Kind) (b : Bool) : Bool := k == .instanceType || b

/-! ## Declarator state and profile hooks -/

/-- The declarator state: the validation context, the global naming table, and the naming
data (requirements, type-export paths with tokens) of the exports of the current scope. -/
structure DState (X : Type) where
  ctx : Ctx X
  names : NameTable := []
  expReqs : List NameReq := []
  expPaths : List (List String × Nat) := []

/-- Profile hooks for core types inside component types. -/
structure DeclHooks (X : Type) where
  /-- The core extern type of a module-type import/export, resolved against the module type's
  local core type space (`none`: invalid or outside the profile). -/
  coreExtern? : List (CoreTypeSlot X) → Silmaril.Wasm.ExternType → Option X
  /-- The destructor core function type is `[rep] -> []`. -/
  dtorOk : AddrType → X → Bool
  /-- A recursion group (`core:rectype`) defined after the core types `prev` is admitted by
  the profile. -/
  recOk : List (CoreTypeSlot X) → Silmaril.Wasm.RecType → Bool

/-- The error of a recursion group defined after the core types `prev` (`none`: valid): its
type indices must be in bounds and its supertypes valid (`RecType.StructurallyValid`, the
structural conditions of core type validation; recursive composite matching against the
supertype is not checked), and the profile must admit it (`DeclHooks.recOk`). -/
def recGroupError? (hk : DeclHooks X) (prev : List (CoreTypeSlot X))
    (r : Silmaril.Wasm.RecType) : Option ValidationError :=
  if !r.checkStructure (CoreTypeSlot.subTypes prev) then
    some ⟨"invalid core type: type index out of bounds or invalid supertype"⟩
  else if !hk.recOk prev r then some ⟨"core type is not valid in this profile"⟩
  else none

namespace DState

/-- Replace the context. -/
def withCtx (st : DState X) (Γ : Ctx X) : DState X := { st with ctx := Γ }

/-- Push a type with a fresh token and register its naming information. -/
def pushTypeInfo (st : DState X) (d : TypeDef Nat X) (inf : TokInfo) : DState X :=
  { st with ctx := (st.ctx.pushType d).2, names := (st.ctx.nextToken, inf) :: st.names }

/-- A `resource` definition: fresh variable `nextVar`, `definedRes (v, some rep)`, push. -/
def defineResource (st : DState X) (rep : AddrType) : DState X :=
  let p := st.ctx.freshVar
  (st.withCtx (p.2.addDefinedRes p.1 (some rep))).pushTypeInfo (.resource p.1) {}

/-- The initial state of a nested declarator scope. -/
def child (st : DState X) (Γ : Ctx X) : DState X := { ctx := Γ, names := st.names }

/-- Return from a child scope: counters and naming table come back, all else is the
parent's. -/
def returnTo (st ch : DState X) : DState X :=
  { st with ctx := { st.ctx with nextVar := ch.ctx.nextVar, nextToken := ch.ctx.nextToken },
            names := ch.names }

end DState

/-- The instance type declared by a finished instance-type scope. -/
def instanceTypeOf (Γ : Ctx X) : InstanceType Nat X :=
  ⟨Γ.definedRes.map (·.1), Γ.exports⟩

/-- The component type declared by a finished component-type scope. -/
def componentTypeOf (Γ : Ctx X) : ComponentType Nat X :=
  ⟨Γ.importedRes.map (·.1), Γ.imports, Γ.definedRes.map (·.1), Γ.exports⟩

/-- Naming information of a finished instance-type scope: its exports' requirements with its
own exported tokens visible. -/
def instanceInfo (ch : DState X) : TokInfo :=
  { transparent := true, contents := .scoped (ch.expPaths.map (·.2)) (.all ch.expReqs),
    paths := ch.expPaths }

/-- Naming information of a finished component-type scope (closed: no requirement). -/
def componentInfo (ch : DState X) : TokInfo :=
  { transparent := true, contents := .tt, paths := ch.expPaths }

namespace DState

/-- Close an instance-type scope into the parent. -/
def closeInstance (st ch : DState X) : DState X :=
  (st.returnTo ch).pushTypeInfo (.instance (instanceTypeOf ch.ctx)) (instanceInfo ch)

/-- Close a component-type scope into the parent. -/
def closeComponent (st ch : DState X) : DState X :=
  (st.returnTo ch).pushTypeInfo (.component (componentTypeOf ch.ctx)) (componentInfo ch)

end DState

/-! ## Core module types (validated in an empty core type space) -/

/-- The state of a module-type declarator: the local core type space, imports, exports. -/
structure CMState (X : Type) where
  types : List (CoreTypeSlot X) := []
  imports : List ((String × String) × X) := []
  exports : List (String × X) := []

/-- The error of limits whose minimum exceeds the maximum (wasmparser). -/
def limitsOrderOk (l : Silmaril.Wasm.Limits) : Bool :=
  match l.max with
  | none => true
  | some m => decide (l.min.val ≤ m.val)

/-- The error of an unresolvable core extern type: out-of-bounds type index, limits with
minimum above maximum, a memory above its page bound (wasmparser messages), a table above
its size bound (descriptive), or a descriptive profile message. -/
def coreExternError (types : List (CoreTypeSlot X)) : Silmaril.Wasm.ExternType →
    ValidationError
  | .func i | .tag i =>
    if types.length ≤ i.value.val then ValidationError.outOfBounds "type" "type" i.value.val
    else ⟨"core extern type is not valid in this profile"⟩
  | .memory m =>
    if !limitsOrderOk m.limits then ⟨"size minimum must not be greater than maximum"⟩
    else if !decide m.Valid then
      match m.address with
      | .i32 => ⟨"memory size must be at most 65536 pages (4GiB)"⟩
      | .i64 => ⟨"memory size must be at most 2**48 pages"⟩
    else ⟨"core extern type is not valid in this profile"⟩
  | .table t =>
    if !limitsOrderOk t.limits then ⟨"size minimum must not be greater than maximum"⟩
    else if !t.limits.check (2 ^ t.address.width - 1) then
      ⟨s!"table size must be at most {2 ^ t.address.width - 1} elements"⟩
    else ⟨"core extern type is not valid in this profile"⟩
  | _ => ⟨"core extern type is not valid in this profile"⟩

/-- Explainer.md l.549: a module type may not define or alias another module type. -/
def moduleAliasError : ValidationError :=
  ⟨"module types cannot define or alias other module types"⟩

/-- One module-type declarator (`core:moduledecl`). `outer` is the stack of enclosing
contexts, innermost first: `outer[0]` is the scope containing the `core type` definition
(outer alias count 1), `outer[c]` count `c + 1` (wasmparser `check_alias_count(components,
count - 1)`). Only core *recursion groups* may be aliased (Explainer.md l.549). A `rec` group
of `n` subtypes occupies `n` local type indices (slot `k` is member `k` of the group); the
group must pass `recGroupError?`. -/
def moduleDecl? (hk : DeclHooks X) (outer : List (Ctx X)) (s : CMState X) :
    Syntax.CoreModuleDecl → Except ValidationError (CMState X)
  | .import_ m n ty =>
    match hk.coreExtern? s.types ty with
    | none => .error (coreExternError s.types ty)
    | some x =>
      match s.imports.lookup (m, n) with
      | some _ => .error ⟨s!"duplicate import name `{m}:{n}`"⟩
      | none => .ok { s with imports := s.imports ++ [((m, n), x)] }
  | .type r =>
    match recGroupError? hk s.types r with
    | some e => .error e
    | none => .ok { s with types := s.types ++ CoreTypeSlot.ofRec s.types r }
  | .aliasOuter 0 idx =>
    match s.types[idx]? with
    | some (.rec_ r k d) => .ok { s with types := s.types ++ [.rec_ r k d] }
    | some (.module_ _) => .error moduleAliasError
    | none => .error (ValidationError.outOfBounds "type" "type" idx)
  | .aliasOuter (c + 1) idx =>
    match outer[c]? with
    | none => .error (ValidationError.invalidOuterAliasCount (c + 1))
    | some q =>
      match q.coreTypes[idx]? with
      | some (.rec_ r k d) => .ok { s with types := s.types ++ [.rec_ r k d] }
      | some (.module_ _) => .error moduleAliasError
      | none => .error (ValidationError.outOfBounds "type" "type" idx)
  | .export_ n ty =>
    match hk.coreExtern? s.types ty with
    | none => .error (coreExternError s.types ty)
    | some x =>
      match s.exports.lookup n with
      | some _ => .error ⟨s!"export name `{n}` already defined"⟩
      | none => .ok { s with exports := s.exports ++ [(n, x)] }

/-- The module-type declarators, in order. -/
def moduleDecls? (hk : DeclHooks X) (outer : List (Ctx X)) :
    CMState X → List Syntax.CoreModuleDecl → Except ValidationError (CMState X)
  | s, [] => .ok s
  | s, d :: ds =>
    match moduleDecl? hk outer s d with
    | .ok s' => moduleDecls? hk outer s' ds
    | .error e => .error e

/-- Validate a core module type in an empty core type space; `outer` as in `moduleDecl?`. -/
def checkCoreModuleType? (hk : DeclHooks X) (outer : List (Ctx X))
    (ds : List Syntax.CoreModuleDecl) : Except ValidationError (CoreModuleType X) :=
  match moduleDecls? hk outer {} ds with
  | .ok s => .ok ⟨s.imports, s.exports⟩
  | .error e => .error e

/-- One module-type declarator (relational). -/
inductive ModuleDeclStep (hk : DeclHooks X) (outer : List (Ctx X)) :
    CMState X → Syntax.CoreModuleDecl → CMState X → Prop where
  | import_ {s : CMState X} {m n : String} {ty : Silmaril.Wasm.ExternType} {x : X}
      (hty : hk.coreExtern? s.types ty = some x) (hdup : s.imports.lookup (m, n) = none) :
      ModuleDeclStep hk outer s (.import_ m n ty) { s with imports := s.imports ++ [((m, n), x)] }
  | type {s : CMState X} {r : Silmaril.Wasm.RecType} (h : recGroupError? hk s.types r = none) :
      ModuleDeclStep hk outer s (.type r)
        { s with types := s.types ++ CoreTypeSlot.ofRec s.types r }
  | aliasSelf {s : CMState X} {idx k : Nat} {r : Silmaril.Wasm.RecType}
      {d : Silmaril.Wasm.Validation.DefType} (h : s.types[idx]? = some (.rec_ r k d)) :
      ModuleDeclStep hk outer s (.aliasOuter 0 idx) { s with types := s.types ++ [.rec_ r k d] }
  | aliasOuter {s : CMState X} {c idx k : Nat} {q : Ctx X} {r : Silmaril.Wasm.RecType}
      {d : Silmaril.Wasm.Validation.DefType}
      (hq : outer[c]? = some q) (h : q.coreTypes[idx]? = some (.rec_ r k d)) :
      ModuleDeclStep hk outer s (.aliasOuter (c + 1) idx)
        { s with types := s.types ++ [.rec_ r k d] }
  | export_ {s : CMState X} {n : String} {ty : Silmaril.Wasm.ExternType} {x : X}
      (hty : hk.coreExtern? s.types ty = some x) (hdup : s.exports.lookup n = none) :
      ModuleDeclStep hk outer s (.export_ n ty) { s with exports := s.exports ++ [(n, x)] }

/-- The module-type declarators (relational). -/
inductive ModuleDeclSteps (hk : DeclHooks X) (outer : List (Ctx X)) :
    CMState X → List Syntax.CoreModuleDecl → CMState X → Prop where
  | nil (s : CMState X) : ModuleDeclSteps hk outer s [] s
  | cons {s s' s'' : CMState X} {d ds} (h : ModuleDeclStep hk outer s d s')
      (hs : ModuleDeclSteps hk outer s' ds s'') : ModuleDeclSteps hk outer s (d :: ds) s''

/-- A valid core module type declaration (empty initial core type space). -/
def ValidCoreModuleType (hk : DeclHooks X) (outer : List (Ctx X))
    (ds : List Syntax.CoreModuleDecl) (mt : CoreModuleType X) : Prop :=
  ∃ s, ModuleDeclSteps hk outer {} ds s ∧ mt = ⟨s.imports, s.exports⟩

/-! ## Resolving an `externtype` -/

/-- 🪙 gate error (descriptive). -/
def valuesGateError : ValidationError :=
  ⟨"value imports and exports require the component model values feature"⟩

/-- Resolve an `externtype` to an entity type. `(sub resource)` resolves to the next fresh
variable `nextVar` (allocated by the push). -/
def resolveDesc? (feat : Features) (Γ : Ctx X) :
    Syntax.ExternDesc → Except ValidationError (Entity Nat X)
  | .coreModule c =>
    match Γ.coreTypeAt? c with
    | .error e => .error e
    | .ok (.module_ t) => .ok (.module t)
    | .ok (.rec_ _ _ _) => .error ⟨s!"core type index {c} is not a module type"⟩
  | .func i =>
    match Γ.typeSlotAt? i with
    | .error e => .error e
    | .ok s =>
      match s.def_ with
      | .func t => .ok (.func t)
      | _ => .error ⟨s!"type index {i} is not a function type"⟩
  | .value b =>
    if feat.values then
      match b with
      | .eq j =>
        match Γ.valueAt? j with
        | .ok p => .ok (.value p.1)
        | .error e => .error e
      | .type vt =>
        match resolveVT? Γ vt with
        | .ok t => .ok (.value t)
        | .error e => .error e
    else .error valuesGateError
  | .type (.eq i) =>
    match Γ.typeSlotAt? i with
    | .ok s => .ok (.type s.def_)
    | .error e => .error e
  | .type .subResource => .ok (.type (.resource Γ.nextVar))
  | .component i =>
    match Γ.typeSlotAt? i with
    | .error e => .error e
    | .ok s =>
      match s.def_ with
      | .component t => .ok (.component t)
      | _ => .error ⟨s!"type index {i} is not a component type"⟩
  | .instance_ i =>
    match Γ.typeSlotAt? i with
    | .error e => .error e
    | .ok s =>
      match s.def_ with
      | .instance t => .ok (.instance t)
      | _ => .error ⟨s!"type index {i} is not an instance type"⟩

/-- Resolution of an `externtype` (relational). -/
inductive ResolveDesc (feat : Features) (Γ : Ctx X) : Syntax.ExternDesc → Entity Nat X → Prop
  | coreModule {c : Nat} {t : CoreModuleType X} (h : Γ.coreType? c = some (.module_ t)) :
      ResolveDesc feat Γ (.coreModule c) (.module t)
  | func {i : Nat} {t : Types.FuncType Nat} (h : Γ.type? i = some (.func t)) :
      ResolveDesc feat Γ (.func i) (.func t)
  | valueEq {j : Nat} {t : Types.ValType Nat} {b : Bool} (hf : feat.values = true)
      (h : Γ.value? j = some (t, b)) : ResolveDesc feat Γ (.value (.eq j)) (.value t)
  | valueType {vt : Syntax.VT} {t : Types.ValType Nat} (hf : feat.values = true)
      (h : ResolveVT Γ vt t) : ResolveDesc feat Γ (.value (.type vt)) (.value t)
  | typeEq {i : Nat} {d : TypeDef Nat X} (h : Γ.type? i = some d) :
      ResolveDesc feat Γ (.type (.eq i)) (.type d)
  | subResource : ResolveDesc feat Γ (.type .subResource) (.type (.resource Γ.nextVar))
  | component {i : Nat} {t : ComponentType Nat X} (h : Γ.type? i = some (.component t)) :
      ResolveDesc feat Γ (.component i) (.component t)
  | instance_ {i : Nat} {t : InstanceType Nat X} (h : Γ.type? i = some (.instance t)) :
      ResolveDesc feat Γ (.instance_ i) (.instance t)

/-! ## Binder hoisting and resource paths -/

mutual
  /-- The export path (positions) of `.type (.resource v)` inside an entity type. -/
  def Entity.resPath? (v : Nat) : Entity Nat X → Option (List Nat)
    | .type (.resource r) => if r = v then some [] else none
    | .instance t => InstanceType.resPath? v t
    | _ => none

  /-- `Entity.resPath?` through an instance type's exports. -/
  def InstanceType.resPath? (v : Nat) : InstanceType Nat X → Option (List Nat)
    | ⟨_, es⟩ => Entity.resPathList? v 0 es

  /-- `Entity.resPath?` through an export list, `k` being the position of the head. -/
  def Entity.resPathList? (v : Nat) (k : Nat) : List (String × Entity Nat X) → Option (List Nat)
    | [] => none
    | (_, e) :: es =>
      match Entity.resPath? v e with
      | some p => some (k :: p)
      | none => Entity.resPathList? v (k + 1) es
end

/-- Rename the binders `ds` to `base, base + 1, ...`; other variables are unchanged. -/
def freshenMap (ds : List Nat) (base : Nat) (r : Nat) : Nat :=
  match ds.idxOf? r with
  | some k => base + k
  | none => r

/-- Allocate the variables bound by an imported/exported entity: the `(sub resource)` variable,
or the ∃-binders of an instance type, renamed to fresh variables and hoisted out of the
instance type (which is pushed with `defined = []`). Returns the entity to push, the allocated
variables and the context with the counter advanced. -/
def bindEntity (Γ : Ctx X) (d : Syntax.ExternDesc) (e : Entity Nat X) :
    Entity Nat X × List Nat × Ctx X :=
  match d, e with
  | .type .subResource, _ => (.type (.resource Γ.nextVar), [Γ.nextVar], Γ.freshVar.2)
  | _, .instance t =>
    (.instance ⟨[], Entity.mapList (freshenMap t.defined Γ.nextVar) t.exports⟩,
     List.range' Γ.nextVar t.defined.length,
     { Γ with nextVar := Γ.nextVar + t.defined.length })
  | _, e => (e, [], Γ)

/-- Map an inner token (of an instance type's type exports) to the fresh token allocated at
the same path by the push. -/
def renameTok (inner outer : List (List String × Nat)) (t : Nat) : Nat :=
  match inner.find? (·.2 == t) with
  | some (p, _) => (outer.lookup p).getD t
  | none => t

/-- Register the naming information of the tokens allocated by pushing the entity of `d` at
index `j` (`Γ` before, `Γ'` after the push). -/
def registerNames (tbl : NameTable) (Γ Γ' : Ctx X) (d : Syntax.ExternDesc) (j : Nat) :
    NameTable :=
  match d with
  | .type .subResource =>
    match Γ'.typeSlot? j with
    | some s => (s.token, {}) :: tbl
    | none => tbl
  | .type (.eq i) =>
    match Γ'.typeSlot? j, Γ.typeSlot? i with
    | some s, some s0 => (s.token, tokInfo tbl s0.token) :: tbl
    | _, _ => tbl
  | .instance_ i =>
    match Γ'.instanceSlot? j, Γ.typeSlot? i with
    | some s, some s0 =>
      let inner := (tokInfo tbl s0.token).paths
      let g := renameTok inner s.tokens
      (s.tokens.filterMap fun q => (inner.lookup q.1).map fun it =>
        let inf := tokInfo tbl it
        (q.2, { inf with contents := inf.contents.rename g })) ++ tbl
    | _, _ => tbl
  | _ => tbl

/-- The type-export paths (with tokens) contributed by an export `n` pushed at index `j`. -/
def newPaths (Γ : Ctx X) (n : String) (e : Entity Nat X) (j : Nat) :
    List (List String × Nat) :=
  match e with
  | .type _ => ((Γ.typeSlot? j).map fun s => ([n], s.token)).toList
  | .instance _ => ((Γ.instanceSlot? j).map fun s => s.tokens.map fun q => (n :: q.1, q.2)).getD []
  | _ => []

namespace DState

/-- Declare an import `n : e` (resolved from `d`): bind variables, push with visible tokens,
record the import and the imported resources with their paths, register tokens. -/
def declImport (st : DState X) (n : String) (d : Syntax.ExternDesc) (e : Entity Nat X) :
    DState X :=
  let k := st.ctx.imports.length
  let b := bindEntity st.ctx d e
  let p := b.2.2.pushImportEntity b.1
  let Γ3 := b.2.1.foldl (fun g v => g.addImportedRes v (k :: (Entity.resPath? v b.1).getD []))
    (p.2.addImport n b.1)
  { st with ctx := Γ3, names := registerNames st.names st.ctx Γ3 d p.1 }

/-- Declare an export `n : e` (resolved from `d`) with requirement `req`: bind variables,
push with visible tokens, record the export and the exported (∃) resources, register tokens,
and record the export's naming data for the enclosing type. -/
def declExport (st : DState X) (n : String) (d : Syntax.ExternDesc) (e : Entity Nat X)
    (req : NameReq) : DState X :=
  let k := st.ctx.exports.length
  let b := bindEntity st.ctx d e
  let p := b.2.2.pushExportEntity b.1
  let Γ3 := b.2.1.foldl
    (fun g v => (g.addDefinedRes v none).addExplicitRes v (k :: (Entity.resPath? v b.1).getD []))
    (p.2.addExport n b.1)
  { ctx := Γ3, names := registerNames st.names st.ctx Γ3 d p.1,
    expReqs := st.expReqs ++ [req], expPaths := st.expPaths ++ newPaths Γ3 n b.1 p.1 }

end DState

/-! ## Leaf declarators -/

/-- The first earlier name that strongly conflicts with `n` (Explainer §Name Uniqueness). -/
def conflict? (names : List String) (n : String) : Option String :=
  names.find? fun p => Syntax.strongCanonChars p.toList == Syntax.strongCanonChars n.toList

/-- `n` is strongly unique with respect to the earlier names. -/
def NameFresh (names : List String) (n : String) : Prop :=
  ∀ p ∈ names, Syntax.strongCanonChars p.toList ≠ Syntax.strongCanonChars n.toList

/-- The word of an entity sort in wasmparser messages. -/
def sortWord : Entity Nat X → String
  | .module _ => "module" | .func _ => "func" | .value _ => "value" | .type _ => "type"
  | .instance _ => "instance" | .component _ => "component"

/-- An exported value type must not contain `borrow` (🪙). -/
def exportValueOk : Entity Nat X → Bool
  | .value t => !ABI.containsBorrow t
  | _ => true

/-- An `importdecl` (component types). -/
def importDecl? (feat : Features) (st : DState X) (n : Syntax.ExternName)
    (d : Syntax.ExternDesc) : Except ValidationError (DState X) :=
  if n.valid then
    match conflict? (st.ctx.imports.map (·.1)) n.name with
    | some p => .error ⟨s!"import name `{n.name}` conflicts with previous name `{p}`"⟩
    | none =>
      match resolveDesc? feat st.ctx d with
      | .error err => .error err
      | .ok e =>
        if visibleOk st.ctx.kind ((descReq st.names st.ctx d).eval st.ctx.importedTokens) then
          .ok (st.declImport n.name d e)
        else .error ⟨s!"{sortWord e} not valid to be used as import"⟩
  else .error ⟨s!"`{n.name}` is not a valid extern name"⟩

/-- An `exportdecl` (component and instance types). -/
def exportDecl? (feat : Features) (st : DState X) (n : Syntax.ExternName)
    (d : Syntax.ExternDesc) : Except ValidationError (DState X) :=
  if n.valid then
    match conflict? (st.ctx.exports.map (·.1)) n.name with
    | some p => .error ⟨s!"export name `{n.name}` conflicts with previous name `{p}`"⟩
    | none =>
      match resolveDesc? feat st.ctx d with
      | .error err => .error err
      | .ok e =>
        if exportValueOk e then
          let req := descReq st.names st.ctx d
          if visibleOk st.ctx.kind
              (req.eval (st.ctx.importedTokens ++ st.ctx.exportedTokens)) then
            .ok (st.declExport n.name d e req)
          else .error ⟨s!"{sortWord e} not valid to be used as export"⟩
        else .error ⟨"value exports cannot contain a `borrow` type"⟩
  else .error ⟨s!"`{n.name}` is not a valid extern name"⟩

/-- An `importdecl` (relational). -/
inductive ValidImportDecl (feat : Features) (st : DState X) (n : Syntax.ExternName)
    (d : Syntax.ExternDesc) : DState X → Prop
  | mk {e : Entity Nat X} (hname : n.valid = true)
      (hfresh : NameFresh (st.ctx.imports.map (·.1)) n.name)
      (hdesc : ResolveDesc feat st.ctx d e)
      (hvis : visibleOk st.ctx.kind
        ((descReq st.names st.ctx d).eval st.ctx.importedTokens) = true) :
      ValidImportDecl feat st n d (st.declImport n.name d e)

/-- An `exportdecl` (relational). -/
inductive ValidExportDecl (feat : Features) (st : DState X) (n : Syntax.ExternName)
    (d : Syntax.ExternDesc) : DState X → Prop
  | mk {e : Entity Nat X} (hname : n.valid = true)
      (hfresh : NameFresh (st.ctx.exports.map (·.1)) n.name)
      (hdesc : ResolveDesc feat st.ctx d e)
      (hval : exportValueOk e = true)
      (hvis : visibleOk st.ctx.kind
        ((descReq st.names st.ctx d).eval
          (st.ctx.importedTokens ++ st.ctx.exportedTokens)) = true) :
      ValidExportDecl feat st n d (st.declExport n.name d e (descReq st.names st.ctx d))

/-- Alias sort error (wasmparser substring "may only refer to types or instances"). -/
def aliasSortError : ValidationError :=
  ⟨"aliases in component and instance types may only refer to types or instances"⟩

/-- An entity has the syntactic sort `s`. -/
def sortMatches (s : Syntax.Sort_) : Entity Nat X → Bool
  | .module _ => s == .core .module_
  | .func _ => s == .func
  | .value _ => s == .value
  | .type _ => s == .type
  | .instance _ => s == .instance_
  | .component _ => s == .component

/-- Export `n` of instance `i` exists with sort `s`. -/
def exportSortOk (Γ : Ctx X) (i : Nat) (n : String) (s : Syntax.Sort_) : Bool :=
  match (Γ.instance? i).bind (·.exports.lookup n) with
  | some e => sortMatches s e
  | none => false

/-- An outer alias of count `ct` crosses a `component` boundary. -/
def crossesComponent (sc : Scopes X) (Γ : Ctx X) (ct : Nat) : Bool :=
  ((Γ :: sc).take ct).any (·.kind == .component)

/-- An alias declarator: `alias export` of instances/types, `alias outer` of core types/types.
-/
def aliasDecl? (sc : Scopes X) (st : DState X) : Syntax.Alias →
    Except ValidationError (DState X)
  | .export_ i n s =>
    if s == .instance_ || s == .type then
      match st.ctx.aliasInstanceExport? i n with
      | .error e => .error e
      | .ok p =>
        if exportSortOk st.ctx i n s then .ok (st.withCtx p.2)
        else .error ⟨s!"export `{n}` of instance {i} has a different sort"⟩
    else .error aliasSortError
  | .outer ct idx .type =>
    match Scopes.outer? sc st.ctx ct with
    | .error e => .error e
    | .ok q =>
      match q.typeSlotAt? idx with
      | .error e => .error e
      | .ok slot =>
        if crossesComponent sc st.ctx ct && !slot.def_.fv.isEmpty then
          .error ⟨s!"type index {idx} transitively refers to resources"⟩
        else .ok (st.withCtx (st.ctx.pushTypeSlot slot).2)
  | .outer ct idx (.core .type) =>
    match Scopes.outer? sc st.ctx ct with
    | .error e => .error e
    | .ok q =>
      match q.coreTypeAt? idx with
      | .error e => .error e
      | .ok slot => .ok (st.withCtx (st.ctx.pushCoreType slot).2)
  | .outer _ _ _ => .error aliasSortError
  | .coreExport _ _ _ => .error aliasSortError

/-- An alias declarator (relational). -/
inductive ValidAlias (sc : Scopes X) (st : DState X) : Syntax.Alias → DState X → Prop
  | export_ {i : Nat} {n : String} {s : Syntax.Sort_} {p : Nat × Ctx X}
      (hs : s = .instance_ ∨ s = .type) (h : st.ctx.aliasInstanceExport? i n = .ok p)
      (hsort : exportSortOk st.ctx i n s = true) :
      ValidAlias sc st (.export_ i n s) (st.withCtx p.2)
  | outerType {ct idx : Nat} {q : Ctx X} {slot : TypeSlot X}
      (hq : Scopes.outer? sc st.ctx ct = .ok q) (hslot : q.typeSlot? idx = some slot)
      (hres : crossesComponent sc st.ctx ct = true → slot.def_.fv = []) :
      ValidAlias sc st (.outer ct idx .type) (st.withCtx (st.ctx.pushTypeSlot slot).2)
  | outerCoreType {ct idx : Nat} {q : Ctx X} {slot : CoreTypeSlot X}
      (hq : Scopes.outer? sc st.ctx ct = .ok q) (hslot : q.coreType? idx = some slot) :
      ValidAlias sc st (.outer ct idx (.core .type)) (st.withCtx (st.ctx.pushCoreType slot).2)

/-- A `core type` declarator; a module type sees the enclosing contexts `st.ctx :: sc`. -/
def coreTypeDecl? (hk : DeclHooks X) (sc : Scopes X) (st : DState X) :
    Syntax.CoreTypeDef → Except ValidationError (DState X)
  | .rec_ r =>
    match recGroupError? hk st.ctx.coreTypes r with
    | some e => .error e
    | none => .ok (st.withCtx (st.ctx.pushCoreRec r))
  | .module_ ds =>
    match checkCoreModuleType? hk (st.ctx :: sc) ds with
    | .ok mt => .ok (st.withCtx (st.ctx.pushCoreType (.module_ mt)).2)
    | .error e => .error e

/-- A `core type` declarator (relational). -/
inductive ValidCoreTypeDecl (hk : DeclHooks X) (sc : Scopes X) (st : DState X) :
    Syntax.CoreTypeDef → DState X → Prop
  | rec_ {r : Silmaril.Wasm.RecType} (h : recGroupError? hk st.ctx.coreTypes r = none) :
      ValidCoreTypeDecl hk sc st (.rec_ r) (st.withCtx (st.ctx.pushCoreRec r))
  | module_ {ds : List Syntax.CoreModuleDecl} {mt : CoreModuleType X}
      (h : ValidCoreModuleType hk (st.ctx :: sc) ds mt) :
      ValidCoreTypeDecl hk sc st (.module_ ds)
        (st.withCtx (st.ctx.pushCoreType (.module_ mt)).2)

/-! ## Completeness of the leaf declarators -/

/-! ## Resource definitions -/

/-- wasmparser: "resources can only be defined within a concrete component". -/
def resourceKindError : ValidationError :=
  ⟨"resources can only be defined within a concrete component"⟩

/-- The 🐘 gate on `rep i64` (descriptive). -/
def resourceRepError : ValidationError :=
  ⟨"resource representation `i64` requires the component model memory64 feature"⟩

/-- wasmparser: "wrong signature for a destructor". -/
def dtorError : ValidationError := ⟨"wrong signature for a destructor"⟩

/-- A `resource rep dtor` definition. -/
def resourceDef? (feat : Features) (hk : DeclHooks X) (st : DState X) (rep : AddrType)
    (dtor : Option Nat) : Except ValidationError (DState X) :=
  if st.ctx.kind = .component then
    if rep = .i32 ∨ feat.memory64 = true then
      match dtor with
      | none => .ok (st.defineResource rep)
      | some f =>
        match st.ctx.coreFuncAt? f with
        | .error e => .error e
        | .ok x => if hk.dtorOk rep x then .ok (st.defineResource rep) else .error dtorError
    else .error resourceRepError
  else .error resourceKindError

/-- The destructor condition: none, or a core function of type `[rep] -> []` (hook). -/
def DtorOk (hk : DeclHooks X) (Γ : Ctx X) (rep : AddrType) : Option Nat → Prop
  | none => True
  | some f => ∃ x, Γ.coreFunc? f = some x ∧ hk.dtorOk rep x = true

/-- A valid `resource` definition (relational): only in a concrete component; `rep` is `i32`
or (🐘) `i64`; the destructor has type `[rep] -> []`. -/
structure ValidResourceDef (feat : Features) (hk : DeclHooks X) (st : DState X)
    (rep : AddrType) (dtor : Option Nat) : Prop where
  kindOk : st.ctx.kind = .component
  repOk : rep = .i32 ∨ feat.memory64 = true
  dtorOk : DtorOk hk st.ctx rep dtor

/-! ## Type definitions and declarators (mutually recursive) -/

mutual
  /-- Validate a type definition and push it (`checkDefType?_sound`). -/
  def checkDefType? (feat : Features) (hk : DeclHooks X) (sc : Scopes X) (st : DState X) :
      Syntax.DefType → Except ValidationError (DState X)
    | .val d =>
      match checkDefValType? feat st.ctx d with
      | .ok t => .ok (st.pushTypeInfo (.val t) (valInfo st.names st.ctx d))
      | .error e => .error e
    | .func ft =>
      match checkFuncType? feat st.ctx ft with
      | .ok t => .ok (st.pushTypeInfo (.func t) (funcInfo st.names st.ctx ft))
      | .error e => .error e
    | .resource rep dtor => resourceDef? feat hk st rep dtor
    | .instance_ ds =>
      match checkInstanceDecls? feat hk (Scopes.enter sc st.ctx .instanceType).1
          (st.child (Scopes.enter sc st.ctx .instanceType).2) ds with
      | .ok ch => .ok (st.closeInstance ch)
      | .error e => .error e
    | .component ds =>
      match checkComponentDecls? feat hk (Scopes.enter sc st.ctx .componentType).1
          (st.child (Scopes.enter sc st.ctx .componentType).2) ds with
      | .ok ch => .ok (st.closeComponent ch)
      | .error e => .error e
    termination_by structural d => d

  /-- Validate one `instancedecl`. -/
  def checkInstanceDecl? (feat : Features) (hk : DeclHooks X) (sc : Scopes X) (st : DState X) :
      Syntax.InstanceDecl → Except ValidationError (DState X)
    | .coreType t => coreTypeDecl? hk sc st t
    | .type t => checkDefType? feat hk sc st t
    | .alias a => aliasDecl? sc st a
    | .export_ n d => exportDecl? feat st n d
    termination_by structural d => d

  /-- Validate one `componentdecl`. -/
  def checkComponentDecl? (feat : Features) (hk : DeclHooks X) (sc : Scopes X)
      (st : DState X) : Syntax.ComponentDecl → Except ValidationError (DState X)
    | .import_ n d => importDecl? feat st n d
    | .decl d => checkInstanceDecl? feat hk sc st d
    termination_by structural d => d

  /-- Validate `instancedecl`s in order. -/
  def checkInstanceDecls? (feat : Features) (hk : DeclHooks X) (sc : Scopes X)
      (st : DState X) : List Syntax.InstanceDecl → Except ValidationError (DState X)
    | [] => .ok st
    | d :: ds =>
      match checkInstanceDecl? feat hk sc st d with
      | .ok st' => checkInstanceDecls? feat hk sc st' ds
      | .error e => .error e
    termination_by structural ds => ds

  /-- Validate `componentdecl`s in order. -/
  def checkComponentDecls? (feat : Features) (hk : DeclHooks X) (sc : Scopes X)
      (st : DState X) : List Syntax.ComponentDecl → Except ValidationError (DState X)
    | [] => .ok st
    | d :: ds =>
      match checkComponentDecl? feat hk sc st d with
      | .ok st' => checkComponentDecls? feat hk sc st' ds
      | .error e => .error e
    termination_by structural ds => ds
end

mutual
  /-- A valid type definition (relational). -/
  inductive ValidDefType (feat : Features) (hk : DeclHooks X) :
      Scopes X → DState X → Syntax.DefType → DState X → Prop
    | val {sc : Scopes X} {st : DState X} {d : Syntax.DefValType} {t : Types.ValType Nat}
        (h : ValidDefValType feat st.ctx d t) :
        ValidDefType feat hk sc st (.val d) (st.pushTypeInfo (.val t) (valInfo st.names st.ctx d))
    | func {sc : Scopes X} {st : DState X} {ft : Syntax.FuncType} {t : Types.FuncType Nat}
        (h : ValidFuncType feat st.ctx ft t) :
        ValidDefType feat hk sc st (.func ft)
          (st.pushTypeInfo (.func t) (funcInfo st.names st.ctx ft))
    | resource {sc : Scopes X} {st : DState X} {rep : AddrType} {dtor : Option Nat}
        (h : ValidResourceDef feat hk st rep dtor) :
        ValidDefType feat hk sc st (.resource rep dtor) (st.defineResource rep)
    | instance_ {sc : Scopes X} {st ch : DState X} {ds : List Syntax.InstanceDecl}
        (h : ValidInstanceDecls feat hk (Scopes.enter sc st.ctx .instanceType).1
          (st.child (Scopes.enter sc st.ctx .instanceType).2) ds ch) :
        ValidDefType feat hk sc st (.instance_ ds) (st.closeInstance ch)
    | component {sc : Scopes X} {st ch : DState X} {ds : List Syntax.ComponentDecl}
        (h : ValidComponentDecls feat hk (Scopes.enter sc st.ctx .componentType).1
          (st.child (Scopes.enter sc st.ctx .componentType).2) ds ch) :
        ValidDefType feat hk sc st (.component ds) (st.closeComponent ch)

  /-- A valid `instancedecl` (relational). -/
  inductive ValidInstanceDecl (feat : Features) (hk : DeclHooks X) :
      Scopes X → DState X → Syntax.InstanceDecl → DState X → Prop
    | coreType {sc : Scopes X} {st st' : DState X} {t : Syntax.CoreTypeDef}
        (h : ValidCoreTypeDecl hk sc st t st') :
        ValidInstanceDecl feat hk sc st (.coreType t) st'
    | type {sc : Scopes X} {st st' : DState X} {t : Syntax.DefType}
        (h : ValidDefType feat hk sc st t st') : ValidInstanceDecl feat hk sc st (.type t) st'
    | alias {sc : Scopes X} {st st' : DState X} {a : Syntax.Alias}
        (h : ValidAlias sc st a st') : ValidInstanceDecl feat hk sc st (.alias a) st'
    | export_ {sc : Scopes X} {st st' : DState X} {n : Syntax.ExternName}
        {d : Syntax.ExternDesc} (h : ValidExportDecl feat st n d st') :
        ValidInstanceDecl feat hk sc st (.export_ n d) st'

  /-- A valid `componentdecl` (relational). -/
  inductive ValidComponentDecl (feat : Features) (hk : DeclHooks X) :
      Scopes X → DState X → Syntax.ComponentDecl → DState X → Prop
    | import_ {sc : Scopes X} {st st' : DState X} {n : Syntax.ExternName}
        {d : Syntax.ExternDesc} (h : ValidImportDecl feat st n d st') :
        ValidComponentDecl feat hk sc st (.import_ n d) st'
    | decl {sc : Scopes X} {st st' : DState X} {d : Syntax.InstanceDecl}
        (h : ValidInstanceDecl feat hk sc st d st') :
        ValidComponentDecl feat hk sc st (.decl d) st'

  /-- Valid `instancedecl`s in order (relational). -/
  inductive ValidInstanceDecls (feat : Features) (hk : DeclHooks X) :
      Scopes X → DState X → List Syntax.InstanceDecl → DState X → Prop
    | nil {sc : Scopes X} {st : DState X} : ValidInstanceDecls feat hk sc st [] st
    | cons {sc : Scopes X} {st st' st'' : DState X} {d : Syntax.InstanceDecl}
        {ds : List Syntax.InstanceDecl} (h : ValidInstanceDecl feat hk sc st d st')
        (hs : ValidInstanceDecls feat hk sc st' ds st'') :
        ValidInstanceDecls feat hk sc st (d :: ds) st''

  /-- Valid `componentdecl`s in order (relational). -/
  inductive ValidComponentDecls (feat : Features) (hk : DeclHooks X) :
      Scopes X → DState X → List Syntax.ComponentDecl → DState X → Prop
    | nil {sc : Scopes X} {st : DState X} : ValidComponentDecls feat hk sc st [] st
    | cons {sc : Scopes X} {st st' st'' : DState X} {d : Syntax.ComponentDecl}
        {ds : List Syntax.ComponentDecl} (h : ValidComponentDecl feat hk sc st d st')
        (hs : ValidComponentDecls feat hk sc st' ds st'') :
        ValidComponentDecls feat hk sc st (d :: ds) st''
end

section Soundness

variable {feat : Features} {hk : DeclHooks X}

end Soundness

section Completeness

variable {feat : Features} {hk : DeclHooks X}

end Completeness

/-! ## Profile hooks -/

/-- The Lime1/V1 core extern type of a module-type import/export (`Engine.CoreExternType`):
function types must be a final, parent-free one-type recursion group of numeric types
(`V1.FuncType.ofCoreRec?`); tables must hold `funcref`, have address type `i32` and limits
within `2^32 - 1`; memories must have address type `i32` and limits within 65536 pages
(`MemoryType.Valid`); globals hold numeric values. Tags are rejected (Lime1 and V1 have no
exception handling), as are 64-bit memories and tables (no memory64). -/
def lime1CoreExtern? (ts : List (CoreTypeSlot CoreExternType)) :
    Silmaril.Wasm.ExternType → Option CoreExternType
  | .func i =>
    match ts[i.value.val]? with
    | some (.rec_ r 0 _) => (V1.FuncType.ofCoreRec? r).map .func
    | _ => none
  | .tag _ => none
  | .global g =>
    match g.value with
    | .num t => some (.global t (decide (g.mutability = .var)))
    | _ => none
  | .memory m =>
    if m.address = .i32 ∧ m.Valid then
      some (.memory m.address m.limits.min.val (m.limits.max.map Fin.val))
    else none
  | .table t =>
    if t.element = ⟨true, .abstract .func⟩ ∧ t.address = .i32 ∧ t.Valid ts.length then
      some (.table t.address t.limits.min.val (t.limits.max.map Fin.val))
    else none

/-- Hooks of the Lime1/V1 profiles: destructors have exactly the type `[rep] -> []`; a
recursion group must be a final, parent-free one-type group of a numeric function type
(`V1.FuncType.ofCoreRec?`, the only core types of WebAssembly 1.0 and Lime1). -/
def lime1Hooks : DeclHooks CoreExternType where
  coreExtern? := lime1CoreExtern?
  dtorOk rep x := decide (x = .func ⟨[.int rep.intType], []⟩)
  recOk _ r := (V1.FuncType.ofCoreRec? r).isSome

/-! ## Tests -/

namespace DefTypesTests

/-- The error message of a checker result, if any. -/
def errMsg? {α : Type} : Except ValidationError α → Option String
  | .error e => some e.message
  | .ok _ => none

/-- A component context with a resource `resource 0` at type index 0 and `nextVar = 1`,
`nextToken = 1`, and a core function `[i32] -> []` at core function index 0. -/
def compCtx : Ctx CoreExternType :=
  { kind := .component, types := [⟨.resource 0, 0⟩], definedRes := [(0, some .i32)],
    coreFuncs := [.func ⟨[.int .i32], []⟩, .func ⟨[], []⟩], nextVar := 1, nextToken := 1 }

def st0 : DState CoreExternType := { ctx := compCtx, names := [(0, {})] }

/-- Run `checkDefType?` at component level. -/
def run (d : Syntax.DefType) : Except ValidationError (DState CoreExternType) :=
  checkDefType? Features.all lime1Hooks [] st0 d

/-- The type pushed last, if its binders/exports have the given shape (Boolean inspection). -/
def lastType? (r : Except ValidationError (DState CoreExternType)) :
    Option (TypeDef Nat CoreExternType) :=
  match r with
  | .ok st => st.ctx.type? (st.ctx.types.length - 1)
  | .error _ => none

/-- `(type (instance (export "r" (type (sub resource)))))`: the ∃-binder is the fresh variable
`nextVar = 1` (distinct from the existing resource `0`). -/
def instSubResource : Syntax.DefType :=
  .instance_ [.export_ { name := "r" } (.type .subResource)]

def isFreshInst : Option (TypeDef Nat CoreExternType) → Bool
  | some (.instance ⟨[v], [("r", .type (.resource w))]⟩) => v == 1 && w == 1
  | _ => false

/-- Two `(sub resource)` exports get two distinct fresh variables, and the parent's counter
advances past them. -/
def instTwo : Syntax.DefType :=
  .instance_ [.export_ { name := "a" } (.type .subResource),
    .export_ { name := "b" } (.type .subResource)]

def isTwoFresh : Except ValidationError (DState CoreExternType) → Bool
  | .ok st =>
    match st.ctx.type? 1 with
    | some (.instance ⟨[v, w], [("a", .type (.resource v')), ("b", .type (.resource w'))]⟩) =>
      v == 1 && w == 2 && v' == 1 && w' == 2 && st.ctx.nextVar == 3
    | _ => false
  | .error _ => false

/-- A component type importing a `(sub resource)` and exporting a function over it:
`(component (import "r" (type (sub resource))) (type (func (result (own 0))))
(export "f" (func 1)))`: the ∀-binder is the fresh variable `1`, with path `[0]`. -/
def compType : Syntax.DefType :=
  .component [.import_ { name := "r" } (.type .subResource),
    .decl (.type (.val (.own 0))),
    .decl (.type (.func { params := [], result := some (.idx 1) })),
    .decl (.export_ { name := "f" } (.func 2))]

def isCompType : Option (TypeDef Nat CoreExternType) → Bool
  | some (.component ⟨[v], [("r", .type (.resource v'))], [],
      [("f", .func ⟨[], some (.own w), false⟩)]⟩) => v == 1 && v' == 1 && w == 1
  | _ => false

-- FLAG(statement-change): the outer core type slot is built by `CoreTypeSlot.ofRec`, which now
-- also records its closed defined type.
/-- An outer alias of count 2 from a module type nested in a component type reaches the
enclosing component's core types (wasmparser `check_alias_count(components, count - 1)`). -/
def stF : DState CoreExternType :=
  { ctx := { compCtx with coreTypes := CoreTypeSlot.ofRec [] (V1.FuncType.toCoreRec ⟨[], []⟩) },
    names := [(0, {})] }

end DefTypesTests

end Silmaril.Wasm.Component.Validation
