module

public import Silmaril.Wasm.Component.Reference.Features.Defs
public import Silmaril.Wasm.Component.Reference.Syntax.Basic.Defs
public import Silmaril.Wasm.Component.Reference.Types.Basic.Defs
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

/-- A validation error. `message` mirrors the wasmparser message, so `assert_invalid` substrings of
the upstream corpus can be matched. -/
structure ValidationError where
  message : String
  deriving Repr, DecidableEq, BEq, Inhabited

namespace ValidationError

/-- wasmparser's out-of-bounds message: `unknown {what} {i}: {space} index out of bounds`. -/
def outOfBounds (what space : String) (i : Nat) : ValidationError :=
  ⟨s!"unknown {what} {i}: {space} index out of bounds"⟩

/-- wasmparser: `invalid outer alias count of {ct}`. -/
def invalidOuterAliasCount (ct : Nat) : ValidationError :=
  ⟨s!"invalid outer alias count of {ct}"⟩

/-- wasmparser: ``instance {i} has no export named `{n}` ``. -/
def noExportNamed (i : Nat) (n : String) : ValidationError :=
  ⟨s!"instance {i} has no export named `{n}`"⟩

/-- A 🪙 value consumed twice (descriptive text, not verified against wasmparser). -/
def valueConsumed (i : Nat) : ValidationError :=
  ⟨s!"value {i} cannot be used more than once"⟩

/-- context.get/set used at a second core value type (descriptive text, not wasmparser's). -/
def contextTypeMismatch : ValidationError :=
  ⟨"canonical `context.get` and `context.set` must use the same type within a component"⟩

end ValidationError

/-- `Except.error e` unless `b`. -/
def ensure (b : Bool) (e : ValidationError) : Except ValidationError Unit :=
  if b then .ok () else .error e

/-! ## Context -/

/-- The kind of state being validated (wasmparser `ComponentKind`): a concrete component, or
the declarators of an instance type or of a component type. -/
inductive Kind where
  | component | instanceType | componentType
  deriving Repr, DecidableEq, BEq, Inhabited

/-- An entry of the core type index space. -/
inductive CoreTypeSlot (X : Type) where
  /-- Member `k` of the Core 3.0 recursion group `t` (`core:rectype`), with its closed defined
  type `d` (`CoreTypeSlot.ofRec`). -/
  | rec_ (t : Silmaril.Wasm.RecType) (k : Nat) (d : Silmaril.Wasm.Validation.DefType)
  /-- A validated core module type (`core:moduletype`). -/
  | module_ (t : CoreModuleType X)
  deriving Repr, DecidableEq

namespace CoreTypeSlot

variable {X : Type}

open Silmaril.Wasm.Validation (DefType rolldt liftRec Ty)

/-- The closed defined type of a slot. A core module type is not a defined type; it stands for
the placeholder `default` (member 0 of the empty recursion group), which is never valid
(`TyOk` fails), so nothing that refers to it validates. -/
def defType : CoreTypeSlot X → DefType
  | .rec_ _ _ d => d
  | .module_ _ => default

/-- The closed defined types of a core type space, one per index. -/
def defTypes (ts : List (CoreTypeSlot X)) : List DefType := ts.map defType

/-- The closed defined types of the recursion group `r` defined after the closed types `dts`:
`$rolldt(|dts|, r)` closed against `dts` (one step of `$alloctypes`, `Execution.Core.allocTypes`;
`Context.rollGroup` of `Type_ok`, Wasm 3.0 spec §2.4 "Types"). -/
def closeRec (dts : List DefType) (r : Silmaril.Wasm.RecType) : List DefType :=
  (rolldt dts.length (liftRec r)).map (·.substAll (dts.map .dt))

/-- The slots of recursion group `r` defined after the slots `prev`: one per member, in order,
each with its closed defined type (`closeRec` against `defTypes prev`). -/
def ofRec (prev : List (CoreTypeSlot X)) (r : Silmaril.Wasm.RecType) : List (CoreTypeSlot X) :=
  (List.range r.types.length).map fun k => .rec_ r k ((closeRec (defTypes prev) r).getD k default)

-- FLAG(statement-change): `ofRec` takes the preceding slots `prev` (to close the group).
@[simp] theorem length_ofRec (prev : List (CoreTypeSlot X)) (r : Silmaril.Wasm.RecType) :
    (ofRec prev r).length = r.types.length := by
  simp [ofRec]

@[simp] theorem defTypes_append (ts us : List (CoreTypeSlot X)) :
    defTypes (ts ++ us) = defTypes ts ++ defTypes us := List.map_append ..

/-- The subtype a slot names (`none` for a core module type). -/
def subType? : CoreTypeSlot X → Option Silmaril.Wasm.SubType
  | .rec_ r k _ => r.types[k]?
  | .module_ _ => none

/-- The function type of a slot naming a function subtype. -/
def funcType? (s : CoreTypeSlot X) : Option Silmaril.Wasm.FuncType :=
  match s.subType? with
  | some ⟨_, _, .func ft⟩ => some ft
  | _ => none

/-- The subtypes of a core type space, for structural checks of a later recursion group. A
core module type stands for a final placeholder subtype, so it can never be a supertype. -/
def subTypes (ts : List (CoreTypeSlot X)) : List Silmaril.Wasm.SubType :=
  ts.map fun s => (s.subType?).getD ⟨true, [], .func ⟨[], []⟩⟩

end CoreTypeSlot

/-- An entry of the component type index space: the semantic type and its naming identity
(`Explainer.md` §External Visibility of Types; wasmparser `ComponentAnyTypeId` with
`created`/`referenced`). No derived instances: `TypeDef` derives none. -/
structure TypeSlot (X : Type) where
  def_ : TypeDef Nat X
  token : Nat

mutual
  /-- The type-export paths of an entity type: `[[]]` for a type, the paths of its exports for
  an instance type, none otherwise (components and modules are closed). -/
  def entityTypePaths {X : Type} : Entity Nat X → List (List String)
    | .type _ => [[]]
    | .instance ⟨_, es⟩ => exportsTypePaths es
    | _ => []

  /-- The type-export paths of an export list, each prefixed by its export name. -/
  def exportsTypePaths {X : Type} : List (String × Entity Nat X) → List (List String)
    | [] => []
    | (n, e) :: es => (entityTypePaths e).map (n :: ·) ++ exportsTypePaths es
end

/-- An entry of the component instance index space: the instance type and the naming token of
each (nested) type export, keyed by export path (an imported or exported instance adds all of
its exported types, recursively; `Explainer.md` §External Visibility of Types). No derived
instances:
`InstanceType` derives none. -/
structure InstanceSlot (X : Type) where
  ty : InstanceType Nat X
  tokens : List (List String × Nat) := []

namespace InstanceSlot

variable {X : Type}

/-- The token recorded for a type-export path. -/
def tokenAt? (s : InstanceSlot X) (path : List String) : Option Nat := s.tokens.lookup path

/-- All recorded tokens. -/
def allTokens (s : InstanceSlot X) : List Nat := s.tokens.map (·.2)

/-- The slot of nested instance export `n` of type `t`: the tokens under prefix `n`. -/
def sub (s : InstanceSlot X) (n : String) (t : InstanceType Nat X) : InstanceSlot X :=
  ⟨t, s.tokens.filterMap fun
    | (m :: rest, k) => if m = n then some (rest, k) else none
    | ([], _) => none⟩

end InstanceSlot

/-- The validation context (wasmparser `ComponentState`). -/
structure Ctx (X : Type) where
  kind : Kind
  -- core index spaces
  coreTypes : List (CoreTypeSlot X) := []
  coreFuncs : List X := []
  coreTables : List X := []
  coreMems : List X := []
  coreGlobals : List X := []
  coreTags : List X := []
  coreModules : List (CoreModuleType X) := []
  coreInstances : List (List (String × X)) := []
  -- component index spaces
  types : List (TypeSlot X) := []
  funcs : List (Types.FuncType Nat) := []
  /-- Values (🪙) with their `consumed` flag. -/
  values : List (Types.ValType Nat × Bool) := []
  /-- Instances with the tokens of their (nested) type exports. -/
  instances : List (InstanceSlot X) := []
  components : List (ComponentType Nat X) := []
  -- import/export maps, in definition order
  imports : List (String × Entity Nat X) := []
  exports : List (String × Entity Nat X) := []
  /-- ∀-bound resources with their import path (indices into imports, then nested exports). -/
  importedRes : List (Nat × List Nat) := []
  /-- ∃-bound resources: `some rep` defined here, `none` defined in a child instance or
  declared as an export in a type. -/
  definedRes : List (Nat × Option AddrType) := []
  /-- Explicitly exported resources with their export path. -/
  explicitRes : List (Nat × List Nat) := []
  /-- Visibility sets (wasmparser `imported_types` / `exported_types`), as tokens. -/
  importedTokens : List Nat := []
  exportedTokens : List Nat := []
  /-- Top-level imported/exported resource names (wasmparser
  `toplevel_{imported,exported}_resources`), for `[method]`/`[constructor]` checks. -/
  importResNames : List (String × Nat) := []
  exportResNames : List (String × Nat) := []
  /-- The core value type fixed by the first `context.get`/`context.set`. -/
  contextType : Option AddrType := none
  hasStart : Bool := false
  /-- Fresh resource-variable and naming-token counters. -/
  nextVar : Nat := 0
  nextToken : Nat := 0

/-- The stack of enclosing contexts, innermost first. -/
abbrev Scopes (X : Type) := List (Ctx X)

namespace Ctx

variable {X : Type}

/-- The empty context of a kind, with the given counters. -/
def empty (k : Kind) (nextVar nextToken : Nat := 0) : Ctx X :=
  { kind := k, nextVar := nextVar, nextToken := nextToken }

/-- Append to an index space, returning the new index. -/
def pushList {α : Type} (l : List α) (a : α) : Nat × List α := (l.length, l ++ [a])

theorem pushList_get {α : Type} (l : List α) (a : α) :
    (pushList l a).2[(pushList l a).1]? = some a := by
  simp [pushList]

/-- Look up an index space, with wasmparser's out-of-bounds message. -/
def listAt? {α : Type} (what space : String) (l : List α) (i : Nat) :
    Except ValidationError α :=
  match l[i]? with
  | some a => .ok a
  | none => .error (ValidationError.outOfBounds what space i)

/-! ### Fresh variables and tokens -/

/-- Allocate a fresh resource variable. -/
def freshVar (Γ : Ctx X) : Nat × Ctx X := (Γ.nextVar, { Γ with nextVar := Γ.nextVar + 1 })

/-- Allocate a fresh naming token. -/
def freshToken (Γ : Ctx X) : Nat × Ctx X :=
  (Γ.nextToken, { Γ with nextToken := Γ.nextToken + 1 })

/-- Allocate one fresh token per path. -/
def freshTokens (Γ : Ctx X) (paths : List (List String)) : List (List String × Nat) × Ctx X :=
  (paths.zip (List.range' Γ.nextToken paths.length),
   { Γ with nextToken := Γ.nextToken + paths.length })

/-! ### Pushes (each returns the new index) -/

def pushCoreType (Γ : Ctx X) (t : CoreTypeSlot X) : Nat × Ctx X :=
  let p := pushList Γ.coreTypes t; (p.1, { Γ with coreTypes := p.2 })
/-- Push the members of a recursion group, one core type index each. -/
def pushCoreRec (Γ : Ctx X) (r : Silmaril.Wasm.RecType) : Ctx X :=
  { Γ with coreTypes := Γ.coreTypes ++ CoreTypeSlot.ofRec Γ.coreTypes r }
def pushCoreFunc (Γ : Ctx X) (t : X) : Nat × Ctx X :=
  let p := pushList Γ.coreFuncs t; (p.1, { Γ with coreFuncs := p.2 })
def pushCoreTable (Γ : Ctx X) (t : X) : Nat × Ctx X :=
  let p := pushList Γ.coreTables t; (p.1, { Γ with coreTables := p.2 })
def pushCoreMem (Γ : Ctx X) (t : X) : Nat × Ctx X :=
  let p := pushList Γ.coreMems t; (p.1, { Γ with coreMems := p.2 })
def pushCoreGlobal (Γ : Ctx X) (t : X) : Nat × Ctx X :=
  let p := pushList Γ.coreGlobals t; (p.1, { Γ with coreGlobals := p.2 })
def pushCoreTag (Γ : Ctx X) (t : X) : Nat × Ctx X :=
  let p := pushList Γ.coreTags t; (p.1, { Γ with coreTags := p.2 })
def pushCoreModule (Γ : Ctx X) (t : CoreModuleType X) : Nat × Ctx X :=
  let p := pushList Γ.coreModules t; (p.1, { Γ with coreModules := p.2 })
def pushCoreInstance (Γ : Ctx X) (t : List (String × X)) : Nat × Ctx X :=
  let p := pushList Γ.coreInstances t; (p.1, { Γ with coreInstances := p.2 })
/-- Push a type slot, keeping its token (outer aliases and `aliasInstanceExport?`). -/
def pushTypeSlot (Γ : Ctx X) (s : TypeSlot X) : Nat × Ctx X :=
  let p := pushList Γ.types s; (p.1, { Γ with types := p.2 })
/-- Push a type with a fresh naming token (a new type identity, wasmparser `with_unique`). -/
def pushType (Γ : Ctx X) (t : TypeDef Nat X) : Nat × Ctx X :=
  let (tok, Γ') := Γ.freshToken
  Γ'.pushTypeSlot ⟨t, tok⟩
def pushFunc (Γ : Ctx X) (t : Types.FuncType Nat) : Nat × Ctx X :=
  let p := pushList Γ.funcs t; (p.1, { Γ with funcs := p.2 })
/-- Push an unconsumed value (🪙). -/
def pushValue (Γ : Ctx X) (t : Types.ValType Nat) : Nat × Ctx X :=
  let p := pushList Γ.values (t, false); (p.1, { Γ with values := p.2 })
/-- Push an instance slot, keeping its tokens (alias of an instance export; an inline-export
instance `(instance (export ...))`, whose judgement records the tokens of the referenced type
slots). -/
def pushInstanceSlot (Γ : Ctx X) (s : InstanceSlot X) : Nat × Ctx X :=
  let p := pushList Γ.instances s; (p.1, { Γ with instances := p.2 })
/-- Push an instance with fresh tokens for all its (nested) type exports (`instantiate`, or
the new index of an import/export). -/
def pushInstance (Γ : Ctx X) (t : InstanceType Nat X) : Nat × Ctx X :=
  let (toks, Γ') := Γ.freshTokens (exportsTypePaths t.exports)
  Γ'.pushInstanceSlot ⟨t, toks⟩
def pushComponent (Γ : Ctx X) (t : ComponentType Nat X) : Nat × Ctx X :=
  let p := pushList Γ.components t; (p.1, { Γ with components := p.2 })

/-- Push an entity type into the index space of its sort with *fresh* identities (a `type`
entity gets a fresh token, an `instance` fresh tokens for its type exports) that are not
registered as visible. Not for aliases, which keep identities (`aliasInstanceExport?`,
`pushTypeSlot`, `pushInstanceSlot`); imports/exports use `pushImportEntity`/`pushExportEntity`.
-/
def pushEntity (Γ : Ctx X) : Entity Nat X → Nat × Ctx X
  | .module t => Γ.pushCoreModule t
  | .func t => Γ.pushFunc t
  | .value t => Γ.pushValue t
  | .type t => Γ.pushType t
  | .instance t => Γ.pushInstance t
  | .component t => Γ.pushComponent t

/-! ### Lookups -/

def coreType? (Γ : Ctx X) (i : Nat) : Option (CoreTypeSlot X) := Γ.coreTypes[i]?
def coreFunc? (Γ : Ctx X) (i : Nat) : Option X := Γ.coreFuncs[i]?
def coreTable? (Γ : Ctx X) (i : Nat) : Option X := Γ.coreTables[i]?
def coreMem? (Γ : Ctx X) (i : Nat) : Option X := Γ.coreMems[i]?
def coreGlobal? (Γ : Ctx X) (i : Nat) : Option X := Γ.coreGlobals[i]?
def coreTag? (Γ : Ctx X) (i : Nat) : Option X := Γ.coreTags[i]?
def coreModule? (Γ : Ctx X) (i : Nat) : Option (CoreModuleType X) := Γ.coreModules[i]?
def coreInstance? (Γ : Ctx X) (i : Nat) : Option (List (String × X)) := Γ.coreInstances[i]?
def typeSlot? (Γ : Ctx X) (i : Nat) : Option (TypeSlot X) := Γ.types[i]?
def type? (Γ : Ctx X) (i : Nat) : Option (TypeDef Nat X) := (Γ.types[i]?).map (·.def_)
def func? (Γ : Ctx X) (i : Nat) : Option (Types.FuncType Nat) := Γ.funcs[i]?
def value? (Γ : Ctx X) (i : Nat) : Option (Types.ValType Nat × Bool) := Γ.values[i]?
def instanceSlot? (Γ : Ctx X) (i : Nat) : Option (InstanceSlot X) := Γ.instances[i]?
def instance? (Γ : Ctx X) (i : Nat) : Option (InstanceType Nat X) :=
  (Γ.instances[i]?).map (·.ty)
def component? (Γ : Ctx X) (i : Nat) : Option (ComponentType Nat X) := Γ.components[i]?

/-! ### Lookups with wasmparser errors -/

def coreTypeAt? (Γ : Ctx X) (i : Nat) := listAt? "type" "type" Γ.coreTypes i
def coreFuncAt? (Γ : Ctx X) (i : Nat) := listAt? "core function" "function" Γ.coreFuncs i
def coreTableAt? (Γ : Ctx X) (i : Nat) := listAt? "table" "table" Γ.coreTables i
def coreMemAt? (Γ : Ctx X) (i : Nat) := listAt? "memory" "memory" Γ.coreMems i
def coreGlobalAt? (Γ : Ctx X) (i : Nat) := listAt? "global" "global" Γ.coreGlobals i
def coreTagAt? (Γ : Ctx X) (i : Nat) := listAt? "tag" "tag" Γ.coreTags i
def coreModuleAt? (Γ : Ctx X) (i : Nat) := listAt? "module" "module" Γ.coreModules i
def coreInstanceAt? (Γ : Ctx X) (i : Nat) :=
  listAt? "core instance" "instance" Γ.coreInstances i
def typeSlotAt? (Γ : Ctx X) (i : Nat) := listAt? "type" "type" Γ.types i
def funcAt? (Γ : Ctx X) (i : Nat) := listAt? "function" "function" Γ.funcs i
def valueAt? (Γ : Ctx X) (i : Nat) := listAt? "value" "value" Γ.values i
def instanceSlotAt? (Γ : Ctx X) (i : Nat) := listAt? "instance" "instance" Γ.instances i
def instanceAt? (Γ : Ctx X) (i : Nat) := (Γ.instanceSlotAt? i).map (·.ty)
def componentAt? (Γ : Ctx X) (i : Nat) := listAt? "component" "component" Γ.components i

/-- The number of entries of the index space of a sort (so `i < Γ.count s` is "index in
range"). -/
def count (Γ : Ctx X) : Syntax.Sort_ → Nat
  | .core .func => Γ.coreFuncs.length
  | .core .table => Γ.coreTables.length
  | .core .memory => Γ.coreMems.length
  | .core .global => Γ.coreGlobals.length
  | .core .tag => Γ.coreTags.length
  | .core .type => Γ.coreTypes.length
  | .core .module_ => Γ.coreModules.length
  | .core .instance_ => Γ.coreInstances.length
  | .func => Γ.funcs.length
  | .value => Γ.values.length
  | .type => Γ.types.length
  | .component => Γ.components.length
  | .instance_ => Γ.instances.length

/-! ### Values (🪙 linearity) -/

/-- Mark value `i` consumed, returning its type; errors if out of bounds or already
consumed. -/
def consumeValue? (Γ : Ctx X) (i : Nat) : Except ValidationError (Types.ValType Nat × Ctx X) :=
  match Γ.values[i]? with
  | none => .error (ValidationError.outOfBounds "value" "value" i)
  | some (_, true) => .error (ValidationError.valueConsumed i)
  | some (t, false) => .ok (t, { Γ with values := Γ.values.set i (t, true) })

/-- Every value has been consumed (checked at the end of a component). -/
def allValuesConsumed (Γ : Ctx X) : Bool := Γ.values.all (·.2)

/-! ### Imports, exports, resources, visibility -/

def addImport (Γ : Ctx X) (n : String) (e : Entity Nat X) : Ctx X :=
  { Γ with imports := Γ.imports ++ [(n, e)] }
def addExport (Γ : Ctx X) (n : String) (e : Entity Nat X) : Ctx X :=
  { Γ with exports := Γ.exports ++ [(n, e)] }
def import? (Γ : Ctx X) (n : String) : Option (Entity Nat X) := Γ.imports.lookup n
def export? (Γ : Ctx X) (n : String) : Option (Entity Nat X) := Γ.exports.lookup n

def addImportedRes (Γ : Ctx X) (r : Nat) (path : List Nat) : Ctx X :=
  { Γ with importedRes := Γ.importedRes ++ [(r, path)] }
def addDefinedRes (Γ : Ctx X) (r : Nat) (rep : Option AddrType) : Ctx X :=
  { Γ with definedRes := Γ.definedRes ++ [(r, rep)] }
def addExplicitRes (Γ : Ctx X) (r : Nat) (path : List Nat) : Ctx X :=
  { Γ with explicitRes := Γ.explicitRes ++ [(r, path)] }
def importedRes? (Γ : Ctx X) (r : Nat) : Option (List Nat) := Γ.importedRes.lookup r
def definedRes? (Γ : Ctx X) (r : Nat) : Option (Option AddrType) := Γ.definedRes.lookup r
def explicitRes? (Γ : Ctx X) (r : Nat) : Option (List Nat) := Γ.explicitRes.lookup r

/-- `r` is defined by a `resource` definition of this component (so `resource.new`/`rep` are
allowed on it); returns its representation. -/
def localRep? (Γ : Ctx X) (r : Nat) : Option AddrType := (Γ.definedRes? r).bind id

def addImportedToken (Γ : Ctx X) (t : Nat) : Ctx X :=
  { Γ with importedTokens := Γ.importedTokens ++ [t] }
def addExportedToken (Γ : Ctx X) (t : Nat) : Ctx X :=
  { Γ with exportedTokens := Γ.exportedTokens ++ [t] }
def addImportedTokens (Γ : Ctx X) (ts : List Nat) : Ctx X :=
  { Γ with importedTokens := Γ.importedTokens ++ ts }
def addExportedTokens (Γ : Ctx X) (ts : List Nat) : Ctx X :=
  { Γ with exportedTokens := Γ.exportedTokens ++ ts }

/-- The tokens an entity pushed at index `i` of its sort would contribute to a visibility
set: the type's token, or all tokens of the instance slot. -/
def entityTokens (Γ : Ctx X) (e : Entity Nat X) (i : Nat) : List Nat :=
  match e with
  | .type _ => ((Γ.typeSlot? i).map (·.token)).toList
  | .instance _ => ((Γ.instanceSlot? i).map (·.allTokens)).getD []
  | _ => []

/-- Push the new index of an import `(import n e)` with fresh identities and register them
in `importedTokens` (wasmparser: an imported type, or all types of an imported instance,
recursively, become `imported_types`). The import map itself is `addImport`. -/
def pushImportEntity (Γ : Ctx X) (e : Entity Nat X) : Nat × Ctx X :=
  let (i, Γ') := Γ.pushEntity e
  (i, Γ'.addImportedTokens (Γ'.entityTokens e i))

/-- Push the new index of an export with fresh identities (`with_unique`) and register them in
`exportedTokens`. The export map itself is `addExport`. -/
def pushExportEntity (Γ : Ctx X) (e : Entity Nat X) : Nat × Ctx X :=
  let (i, Γ') := Γ.pushEntity e
  (i, Γ'.addExportedTokens (Γ'.entityTokens e i))

/-- `alias export i "n"` of a component instance: push export `n` of instance `i` into the
space of its sort, *keeping* the identities recorded in the instance slot (a type gets its
recorded token; a nested instance the tokens under prefix `n`). Other sorts are pushed by
`pushEntity`. Errors: wasmparser "unknown instance ... index out of bounds" and
"instance {i} has no export named `{n}`". Sort checking against the alias's declared sort
is the judgement's. -/
def aliasInstanceExport? (Γ : Ctx X) (i : Nat) (n : String) :
    Except ValidationError (Nat × Ctx X) := do
  let s ← Γ.instanceSlotAt? i
  match s.ty.exports.lookup n with
  | none => .error (ValidationError.noExportNamed i n)
  | some (.type t) =>
    match s.tokenAt? [n] with
    | some tok => .ok (Γ.pushTypeSlot ⟨t, tok⟩)
    | none => .ok (Γ.pushType t)
  | some (.instance t) => .ok (Γ.pushInstanceSlot (s.sub n t))
  | some e => .ok (Γ.pushEntity e)

/-- A type with token `t` may be referenced by an import (imported types only). -/
def importVisible (Γ : Ctx X) (t : Nat) : Bool := Γ.importedTokens.contains t
/-- A type with token `t` may be referenced by an export (imported or exported types). -/
def exportVisible (Γ : Ctx X) (t : Nat) : Bool :=
  Γ.importedTokens.contains t || Γ.exportedTokens.contains t

def addImportResName (Γ : Ctx X) (n : String) (r : Nat) : Ctx X :=
  { Γ with importResNames := Γ.importResNames ++ [(n, r)] }
def addExportResName (Γ : Ctx X) (n : String) (r : Nat) : Ctx X :=
  { Γ with exportResNames := Γ.exportResNames ++ [(n, r)] }
def importResName? (Γ : Ctx X) (n : String) : Option Nat := Γ.importResNames.lookup n
def exportResName? (Γ : Ctx X) (n : String) : Option Nat := Γ.exportResNames.lookup n

/-- Fix the `context.get`/`context.set` core type, or check it against the fixed one. -/
def setContextType? (Γ : Ctx X) (t : AddrType) : Except ValidationError (Ctx X) :=
  match Γ.contextType with
  | none => .ok { Γ with contextType := some t }
  | some t' => if t = t' then .ok Γ else .error ValidationError.contextTypeMismatch

/-! ### Push/lookup lemmas -/

section Lemmas

variable (Γ : Ctx X)

@[simp] theorem pushCoreType_lookup (t : CoreTypeSlot X) :
    (Γ.pushCoreType t).2.coreType? (Γ.pushCoreType t).1 = some t := pushList_get _ _
@[simp] theorem pushCoreFunc_lookup (t : X) :
    (Γ.pushCoreFunc t).2.coreFunc? (Γ.pushCoreFunc t).1 = some t := pushList_get _ _
@[simp] theorem pushCoreTable_lookup (t : X) :
    (Γ.pushCoreTable t).2.coreTable? (Γ.pushCoreTable t).1 = some t := pushList_get _ _
@[simp] theorem pushCoreMem_lookup (t : X) :
    (Γ.pushCoreMem t).2.coreMem? (Γ.pushCoreMem t).1 = some t := pushList_get _ _
@[simp] theorem pushCoreGlobal_lookup (t : X) :
    (Γ.pushCoreGlobal t).2.coreGlobal? (Γ.pushCoreGlobal t).1 = some t := pushList_get _ _
@[simp] theorem pushCoreTag_lookup (t : X) :
    (Γ.pushCoreTag t).2.coreTag? (Γ.pushCoreTag t).1 = some t := pushList_get _ _
@[simp] theorem pushCoreModule_lookup (t : CoreModuleType X) :
    (Γ.pushCoreModule t).2.coreModule? (Γ.pushCoreModule t).1 = some t := pushList_get _ _
@[simp] theorem pushCoreInstance_lookup (t : List (String × X)) :
    (Γ.pushCoreInstance t).2.coreInstance? (Γ.pushCoreInstance t).1 = some t :=
  pushList_get _ _
@[simp] theorem pushTypeSlot_lookup (s : TypeSlot X) :
    (Γ.pushTypeSlot s).2.typeSlot? (Γ.pushTypeSlot s).1 = some s := pushList_get _ _
@[simp] theorem pushFunc_lookup (t : Types.FuncType Nat) :
    (Γ.pushFunc t).2.func? (Γ.pushFunc t).1 = some t := pushList_get _ _
@[simp] theorem pushValue_lookup (t : Types.ValType Nat) :
    (Γ.pushValue t).2.value? (Γ.pushValue t).1 = some (t, false) := pushList_get _ _
@[simp] theorem pushInstanceSlot_lookup (s : InstanceSlot X) :
    (Γ.pushInstanceSlot s).2.instanceSlot? (Γ.pushInstanceSlot s).1 = some s :=
  pushList_get _ _
@[simp] theorem pushInstance_lookup (t : InstanceType Nat X) :
    (Γ.pushInstance t).2.instance? (Γ.pushInstance t).1 = some t := by
  simp [pushInstance, freshTokens, instance?, pushInstanceSlot, pushList]
@[simp] theorem pushComponent_lookup (t : ComponentType Nat X) :
    (Γ.pushComponent t).2.component? (Γ.pushComponent t).1 = some t := pushList_get _ _

/-- `pushType` stores the type under the token that was fresh before the push. -/
@[simp] theorem pushType_lookup (t : TypeDef Nat X) :
    (Γ.pushType t).2.typeSlot? (Γ.pushType t).1 = some ⟨t, Γ.nextToken⟩ := by
  simp [pushType, freshToken]

@[simp] theorem pushType_type? (t : TypeDef Nat X) :
    (Γ.pushType t).2.type? (Γ.pushType t).1 = some t := by
  simp [pushType, freshToken, type?, pushTypeSlot, pushList]

end Lemmas

end Ctx

/-! ## Scope stack (outer aliases) -/

namespace Scopes

variable {X : Type}

/-- Enter a nested scope of kind `k` (a nested component definition or a type declarator):
the current context becomes the innermost enclosing one; counters carry over. -/
def enter (sc : Scopes X) (Γ : Ctx X) (k : Kind) : Scopes X × Ctx X :=
  (Γ :: sc, Ctx.empty k Γ.nextVar Γ.nextToken)

/-- Leave the innermost scope: restore the parent, carrying back the child's counters so that
variables and tokens stay globally fresh. `none` at the outermost scope. -/
def exit? (sc : Scopes X) (child : Ctx X) : Option (Scopes X × Ctx X) :=
  match sc with
  | [] => none
  | p :: rest => some (rest, { p with nextVar := child.nextVar, nextToken := child.nextToken })

/-- The context addressed by the count `ct` of `alias outer ct i`: `0` is the current
context `Γ`, `ct + 1` the `ct`-th enclosing one. wasmparser: "invalid outer alias count". -/
def outer? (sc : Scopes X) (Γ : Ctx X) (ct : Nat) : Except ValidationError (Ctx X) :=
  match ct with
  | 0 => .ok Γ
  | n + 1 =>
    match sc[n]? with
    | some p => .ok p
    | none => .error (ValidationError.invalidOuterAliasCount (n + 1))

end Scopes

/-! ## Tests: push/lookup round trips -/

section Tests

namespace Tests

def ctxTest0 : Ctx Unit := Ctx.empty .component

def u32Test : Types.ValType Nat := .prim .u32
def funcTypeTest : Types.FuncType Nat := { params := [("x", .own 0)], result := some (.own 0) }

/-- The error of an `Except`, if any. -/
def errOf? {α : Type} : Except ValidationError α → Option ValidationError
  | .error e => some e
  | .ok _ => none

/-! External visibility through instance slots (`external-visibility.wast` lines 408-454):
aliasing a type out of an exported instance yields a token in `exportedTokens`; aliasing out of
the unexported inline-export instance, or out of an instantiated instance, does not. -/

def bagTy : InstanceType Nat Unit := ⟨[], [("t", .type (.val u32Test))]⟩

/-- The token of type index `j` and whether it may be used by an export. -/
def typeVis (g : Ctx Unit) (j : Nat) : Option (Nat × Bool) :=
  (g.typeSlot? j).map fun s => (s.token, g.exportVisible s.token)

end Tests

end Tests

end Silmaril.Wasm.Component.Validation
