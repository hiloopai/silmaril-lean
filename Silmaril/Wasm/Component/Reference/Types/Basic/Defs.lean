module

public import Silmaril.Wasm.Component.Reference.ABI.Layout.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Flatten.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Calling.Defs

/-!
# Semantic (index-free) component types

The Component Model's type ASTs contain no type indices after decoding
(Explainer §Type Checking, "type ASTs do *not* contain any type indices"; the
reference `definitions.py` likewise has index-free `ExternDecl` (lines 65-68),
`ComponentType` (lines 70-73), `InstanceType` (lines 75-77) and `FuncType`
(lines 79-83), at
https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py
).
Design sources: `Explainer.md` §Type Definitions, §Declarators and §Type Checking (index-free
types, abstract types and generativity, subtyping and instantiation), and wasmparser's
`crates/wasmparser/src/validator/component.rs` and `component_types.rs` (import pushing, export
inference).

The only non-structural atoms are **resource type variables**, so every former
here is parametric in a variable type `R` (validation: fresh numbers; runtime:
resource ids). Following the wasmparser style (`component_types.rs`), binders are explicit lists of
variables drawn from a global supply:

* `InstanceType.defined` are ∃-binders (abstract resources exported by an
  instance type; empty for concrete instances);
* `ComponentType.imported` are ∀-binders scoping over the imports and exports:
  all `(sub resource)` type imports *and* the abstract resources exported by
  imported instance/component types (wasmparser `prepare_instance_import`), whose nested
  `defined` lists are then empty; `ComponentType.defined` are ∃-binders scoping
  over the exports only. `InstanceType.defined` is thus non-empty only for
  existentials (instance types in export position or standalone).

Every former is also parametric in the core extern type `X`, so that the V1/Lime1
profiles can use `Engine.CoreExternType` and the abstract Core 3.0 profile can
use `Silmaril.Wasm.ExternType` (this file imports neither).

Provided:

* `WIT.ValType.mapResource` / `WIT.FuncType.mapResource` (resource renaming),
  `WIT.ValType.fv`, `WIT.ValType.mapResourceFields_map_snd`, with
  `map_id`/`map_comp`-style lemmas, `fv_mapResource`, and
  the invariance lemmas `ABI.layout_mapResource`, `ABI.flatten_mapResource`,
  `ABI.flattenFunc_mapResource` (layout and flattening ignore resource
  identity);
* `CoreModuleType X`, the mutual family `TypeDef`, `Entity`, `InstanceType`,
  `ComponentType`;
* `map` (renaming/substitution of resource variables, applied uniformly to
  binders and occurrences) and `mapX` (change of core extern type) with
  `map_id`, `map_comp`, `mapX_id`, `mapX_comp` and `map_mapX` (the two maps
  commute);
* free variables `fv` (binders removed), `WellScoped ctx` (decidable),
  `Entity.sort`, `ComponentType.lookupImport` / `lookupExport`,
  `InstanceType.lookupExport`.

NOT modelled here: subtyping, type equality up to α-renaming of binders,
resource paths of binders, validation of core extern types, the WIT-level
well-formedness of the value types (see `WIT.ValType.WellFormed`), and the
freshness side conditions of `map` (a non-injective `map` may capture: `map`
is plain substitution, and capture-avoidance is the caller's obligation).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.WIT

universe u v w x

section MapResource

variable {Ref : Type u} {R : Type v} {S : Type w} {T : Type x}

mutual
  /-- Rename (substitute) resource identities in a value type. Names (`ref`) are
  untouched. -/
  def ValType.mapResource (f : R → S) : ValType Ref R → ValType Ref S
    | .prim t => .prim t
    | .ref n => .ref n
    | .list t => .list (t.mapResource f)
    | .fixedList t n => .fixedList (t.mapResource f) n
    | .record fs => .record (ValType.mapResourceFields f fs)
    | .tuple ts => .tuple (ValType.mapResourceList f ts)
    | .variant cs => .variant (ValType.mapResourceCases f cs)
    | .enum cs => .enum cs
    | .flags ls => .flags ls
    | .option t => .option (t.mapResource f)
    | .result ok err => .result (ValType.mapResourceOption f ok) (ValType.mapResourceOption f err)
    | .map k t => .map k (t.mapResource f)
    | .own r => .own (f r)
    | .borrow r => .borrow (f r)
    | .future e => .future (ValType.mapResourceOption f e)
    | .stream e => .stream (ValType.mapResourceOption f e)
    | .errorContext => .errorContext

  def ValType.mapResourceFields (f : R → S) :
      List (String × ValType Ref R) → List (String × ValType Ref S)
    | [] => []
    | (n, t) :: fs => (n, t.mapResource f) :: ValType.mapResourceFields f fs

  def ValType.mapResourceList (f : R → S) : List (ValType Ref R) → List (ValType Ref S)
    | [] => []
    | t :: ts => t.mapResource f :: ValType.mapResourceList f ts

  def ValType.mapResourceCases (f : R → S) :
      List (String × Option (ValType Ref R)) → List (String × Option (ValType Ref S))
    | [] => []
    | (n, t) :: cs => (n, ValType.mapResourceOption f t) :: ValType.mapResourceCases f cs

  def ValType.mapResourceOption (f : R → S) : Option (ValType Ref R) → Option (ValType Ref S)
    | none => none
    | some t => some (t.mapResource f)
end

mutual
  /-- Resource variables occurring in a value type (with repetitions, in order). -/
  def ValType.fv : ValType Ref R → List R
    | .prim _ | .ref _ | .enum _ | .flags _ | .errorContext => []
    | .list t | .fixedList t _ | .option t | .map _ t => t.fv
    | .record fs => ValType.fvFields fs
    | .tuple ts => ValType.fvList ts
    | .variant cs => ValType.fvCases cs
    | .result ok err => ValType.fvOption ok ++ ValType.fvOption err
    | .own r | .borrow r => [r]
    | .future e | .stream e => ValType.fvOption e

  def ValType.fvFields : List (String × ValType Ref R) → List R
    | [] => []
    | (_, t) :: fs => t.fv ++ ValType.fvFields fs

  def ValType.fvList : List (ValType Ref R) → List R
    | [] => []
    | t :: ts => t.fv ++ ValType.fvList ts

  def ValType.fvCases : List (String × Option (ValType Ref R)) → List R
    | [] => []
    | (_, t) :: cs => ValType.fvOption t ++ ValType.fvCases cs

  def ValType.fvOption : Option (ValType Ref R) → List R
    | none => []
    | some t => t.fv
end

mutual
  @[simp] theorem ValType.mapResource_id : ∀ t : ValType Ref R, t.mapResource id = t
    | .prim _ | .ref _ | .enum _ | .flags _ | .errorContext | .own _ | .borrow _ => rfl
    | .list t | .fixedList t _ | .option t | .map _ t => by
      simp only [ValType.mapResource, ValType.mapResource_id t]
    | .record fs => by simp only [ValType.mapResource, ValType.mapResourceFields_id fs]
    | .tuple ts => by simp only [ValType.mapResource, ValType.mapResourceList_id ts]
    | .variant cs => by simp only [ValType.mapResource, ValType.mapResourceCases_id cs]
    | .result ok err => by
      simp only [ValType.mapResource, ValType.mapResourceOption_id ok,
        ValType.mapResourceOption_id err]
    | .future e | .stream e => by
      simp only [ValType.mapResource, ValType.mapResourceOption_id e]

  @[simp] theorem ValType.mapResourceFields_id :
      ∀ fs : List (String × ValType Ref R), ValType.mapResourceFields id fs = fs
    | [] => rfl
    | (_, t) :: fs => by
      simp only [ValType.mapResourceFields, ValType.mapResource_id t,
        ValType.mapResourceFields_id fs]

  @[simp] theorem ValType.mapResourceList_id :
      ∀ ts : List (ValType Ref R), ValType.mapResourceList id ts = ts
    | [] => rfl
    | t :: ts => by
      simp only [ValType.mapResourceList, ValType.mapResource_id t,
        ValType.mapResourceList_id ts]

  @[simp] theorem ValType.mapResourceCases_id :
      ∀ cs : List (String × Option (ValType Ref R)), ValType.mapResourceCases id cs = cs
    | [] => rfl
    | (_, t) :: cs => by
      simp only [ValType.mapResourceCases, ValType.mapResourceOption_id t,
        ValType.mapResourceCases_id cs]

  @[simp] theorem ValType.mapResourceOption_id :
      ∀ t : Option (ValType Ref R), ValType.mapResourceOption id t = t
    | none => rfl
    | some t => by simp only [ValType.mapResourceOption, ValType.mapResource_id t]
end

/-- Parameters are renamed pointwise; names and the `async` flag are kept. -/
def FuncType.mapResource (f : R → S) (ft : FuncType Ref R) : FuncType Ref S where
  params := ValType.mapResourceFields f ft.params
  result := ValType.mapResourceOption f ft.result
  async_ := ft.async_

def FuncType.fv (ft : FuncType Ref R) : List R :=
  ValType.fvFields ft.params ++ ValType.fvOption ft.result

@[simp] theorem FuncType.mapResource_id (ft : FuncType Ref R) : ft.mapResource id = ft := by
  cases ft
  simp only [FuncType.mapResource, ValType.mapResourceFields_id, ValType.mapResourceOption_id]

/-- Renaming commutes with projecting the types out of named fields. -/
theorem ValType.mapResourceFields_map_snd (f : R → S) :
    ∀ fs : List (String × ValType Ref R),
      (ValType.mapResourceFields f fs).map Prod.snd =
        ValType.mapResourceList f (fs.map Prod.snd)
  | [] => rfl
  | (_, t) :: fs => by
    simp only [ValType.mapResourceFields, List.map_cons,
      ValType.mapResourceList, ValType.mapResourceFields_map_snd f fs]

end MapResource

end Silmaril.Wasm.Component.WIT

namespace Silmaril.Wasm.Component.ABI

universe u v

variable {R : Type u} {S : Type v}

mutual
  /-- Canonical ABI layout ignores resource identity. -/
  @[simp] theorem layout_mapResource (p : AddrType) (f : R → S) :
      ∀ t : WIT.ClosedType R, layout p (t.mapResource f) = layout p t
    | .prim _ | .enum _ | .flags _ | .errorContext | .own _ | .borrow _
    | .list _ | .map _ _ | .future _ | .stream _ => by
      simp only [WIT.ValType.mapResource, layout]
    | .ref n => nomatch n
    | .fixedList t _ | .option t => by
      simp only [WIT.ValType.mapResource, layout, layout_mapResource p f t]
    | .record fs => by
      simp only [WIT.ValType.mapResource, layout, layoutFields_mapResource p f fs]
    | .tuple ts => by
      simp only [WIT.ValType.mapResource, layout, layoutTypes_mapResource p f ts]
    | .variant cs => by
      simp only [WIT.ValType.mapResource, layout, layoutCases_mapResource p f cs]
    | .result ok err => by
      simp only [WIT.ValType.mapResource, layout, layoutOption_mapResource p f ok,
        layoutOption_mapResource p f err]

  theorem layoutFields_mapResource (p : AddrType) (f : R → S) :
      ∀ fs : List (String × WIT.ClosedType R),
        layoutFields p (WIT.ValType.mapResourceFields f fs) = layoutFields p fs
    | [] => by simp only [WIT.ValType.mapResourceFields, layoutFields]
    | (_, t) :: fs => by
      simp only [WIT.ValType.mapResourceFields, layoutFields, layout_mapResource p f t,
        layoutFields_mapResource p f fs]

  theorem layoutTypes_mapResource (p : AddrType) (f : R → S) :
      ∀ ts : List (WIT.ClosedType R),
        layoutTypes p (WIT.ValType.mapResourceList f ts) = layoutTypes p ts
    | [] => by simp only [WIT.ValType.mapResourceList, layoutTypes]
    | t :: ts => by
      simp only [WIT.ValType.mapResourceList, layoutTypes, layout_mapResource p f t,
        layoutTypes_mapResource p f ts]

  theorem layoutCases_mapResource (p : AddrType) (f : R → S) :
      ∀ cs : List (String × Option (WIT.ClosedType R)),
        layoutCases p (WIT.ValType.mapResourceCases f cs) = layoutCases p cs
    | [] => by simp only [WIT.ValType.mapResourceCases, layoutCases]
    | (_, t) :: cs => by
      simp only [WIT.ValType.mapResourceCases, layoutCases, layoutOption_mapResource p f t,
        layoutCases_mapResource p f cs]

  theorem layoutOption_mapResource (p : AddrType) (f : R → S) :
      ∀ t : Option (WIT.ClosedType R),
        layoutOption p (WIT.ValType.mapResourceOption f t) = layoutOption p t
    | none => by simp only [WIT.ValType.mapResourceOption, layoutOption]
    | some t => by
      simp only [WIT.ValType.mapResourceOption, layoutOption, layout_mapResource p f t]
end

mutual
  /-- Canonical ABI flattening ignores resource identity. -/
  @[simp] theorem flatten_mapResource (p : AddrType) (f : R → S) :
      ∀ t : WIT.ClosedType R, flatten p (t.mapResource f) = flatten p t
    | .prim _ | .enum _ | .flags _ | .errorContext | .own _ | .borrow _
    | .list _ | .map _ _ | .future _ | .stream _ => by
      simp only [WIT.ValType.mapResource, flatten]
    | .ref n => nomatch n
    | .fixedList t _ | .option t => by
      simp only [WIT.ValType.mapResource, flatten, flatten_mapResource p f t]
    | .record fs => by
      simp only [WIT.ValType.mapResource, flatten, flattenFields_mapResource p f fs]
    | .tuple ts => by
      simp only [WIT.ValType.mapResource, flatten, flattenTypes_mapResource p f ts]
    | .variant cs => by
      simp only [WIT.ValType.mapResource, flatten, flattenCases_mapResource p f cs]
    | .result ok err => by
      simp only [WIT.ValType.mapResource, flatten, flattenOption_mapResource p f ok,
        flattenOption_mapResource p f err]

  theorem flattenFields_mapResource (p : AddrType) (f : R → S) :
      ∀ fs : List (String × WIT.ClosedType R),
        flattenFields p (WIT.ValType.mapResourceFields f fs) = flattenFields p fs
    | [] => by simp only [WIT.ValType.mapResourceFields, flattenFields]
    | (_, t) :: fs => by
      simp only [WIT.ValType.mapResourceFields, flattenFields, flatten_mapResource p f t,
        flattenFields_mapResource p f fs]

  theorem flattenTypes_mapResource (p : AddrType) (f : R → S) :
      ∀ ts : List (WIT.ClosedType R),
        flattenTypes p (WIT.ValType.mapResourceList f ts) = flattenTypes p ts
    | [] => by simp only [WIT.ValType.mapResourceList, flattenTypes]
    | t :: ts => by
      simp only [WIT.ValType.mapResourceList, flattenTypes, flatten_mapResource p f t,
        flattenTypes_mapResource p f ts]

  theorem flattenCases_mapResource (p : AddrType) (f : R → S) :
      ∀ cs : List (String × Option (WIT.ClosedType R)),
        flattenCases p (WIT.ValType.mapResourceCases f cs) = flattenCases p cs
    | [] => by simp only [WIT.ValType.mapResourceCases, flattenCases]
    | (_, t) :: cs => by
      simp only [WIT.ValType.mapResourceCases, flattenCases, flattenOption_mapResource p f t,
        flattenCases_mapResource p f cs]

  theorem flattenOption_mapResource (p : AddrType) (f : R → S) :
      ∀ t : Option (WIT.ClosedType R),
        flattenOption p (WIT.ValType.mapResourceOption f t) = flattenOption p t
    | none => by simp only [WIT.ValType.mapResourceOption, flattenOption]
    | some t => by
      simp only [WIT.ValType.mapResourceOption, flattenOption, flatten_mapResource p f t]
end

/-- The flat core signature of a function type ignores resource identity. -/
@[simp] theorem flattenFunc_mapResource (opts : Options) (d : Direction) (f : R → S)
    (ft : WIT.FuncType Empty R) :
    flattenFunc opts d (FuncType.ofWIT (ft.mapResource f)) =
      flattenFunc opts d (FuncType.ofWIT ft) := by
  obtain ⟨params, result, _⟩ := ft
  have hp : flattenTypes opts.memory ((WIT.ValType.mapResourceFields f params).map Prod.snd) =
      flattenTypes opts.memory (params.map Prod.snd) := by
    rw [WIT.ValType.mapResourceFields_map_snd, flattenTypes_mapResource]
  have hr : flattenTypes opts.memory (WIT.ValType.mapResourceOption f result).toList =
      flattenTypes opts.memory result.toList := by
    cases result <;>
      simp only [WIT.ValType.mapResourceOption, Option.toList, flattenTypes,
        flatten_mapResource]
  simp only [flattenFunc, FuncType.ofWIT, WIT.FuncType.mapResource, hp, hr]
  cases d <;> rfl

end Silmaril.Wasm.Component.ABI

namespace Silmaril.Wasm.Component.Types

universe u v w x y z

/-- Semantic value types: closed WIT value types over resource variables `R`. -/
abbrev ValType (R : Type u) := WIT.ClosedType R

/-- Semantic function types: named parameters, at most one result, `async_` flag. -/
abbrev FuncType (R : Type u) := WIT.FuncType Empty R

/-- Index-free core module type over the core extern type `X`: imports keyed by
`(module, name)`, exports keyed by name. -/
structure CoreModuleType (X : Type v) where
  imports : List ((String × String) × X)
  exports : List (String × X)
  deriving Repr, DecidableEq, BEq

/-- The sort of a component entity type (`Entity.sort`): the six Explainer
`externdesc` sorts `core module`, `func`, `value`, `type`, `instance`,
`component`; `module` stands for `core module`. -/
inductive EntitySort where
  | module | func | value | type | «instance» | component
  deriving Repr, DecidableEq

mutual
  /-- What a component `type` index denotes (index-free). -/
  inductive TypeDef (R : Type u) (X : Type v) where
    | val (t : ValType R)
    | resource (r : R)
    | func (t : FuncType R)
    | «instance» (t : InstanceType R X)
    | component (t : ComponentType R X)

  /-- Component entity types (wasmparser `ComponentEntityType`, REF `ExternDecl`
  payloads). -/
  inductive Entity (R : Type u) (X : Type v) where
    | module (t : CoreModuleType X)
    | func (t : FuncType R)
    | value (t : ValType R)
    | type (t : TypeDef R X)
    | «instance» (t : InstanceType R X)
    | component (t : ComponentType R X)

  /-- Instance types; `defined` are ∃-binders over `exports`. `defined` is non-empty
  only for existentials (an instance type in export position or standalone); an
  instance type in import position has `defined = []`, its abstract resources
  being ∀-bound by the enclosing `ComponentType.imported` (see there). -/
  structure InstanceType (R : Type u) (X : Type v) where
    defined : List R
    exports : List (String × Entity R X)

  /-- Component types; `imported` are ∀-binders over imports and exports,
  `defined` are ∃-binders over the exports.

  Binder convention (wasmparser `prepare_instance_import`): `imported` lists
  *every* ∀-bound resource, i.e. the `(sub resource)` type imports **and** the
  abstract resources exported by imported instance/component types; those
  imported types then carry `defined = []`. Placing such a resource only in the
  nested `InstanceType.defined` would make it free in the exports, and placing it
  in both would bind it twice. -/
  structure ComponentType (R : Type u) (X : Type v) where
    imported : List R
    imports : List (String × Entity R X)
    defined : List R
    exports : List (String × Entity R X)
end

variable {R : Type u} {S : Type w} {T : Type x} {X : Type v} {Y : Type y} {Z : Type z}

/-! ## Core module types -/

def CoreModuleType.mapX (g : X → Y) (m : CoreModuleType X) : CoreModuleType Y where
  imports := m.imports.map fun i => (i.1, g i.2)
  exports := m.exports.map fun e => (e.1, g e.2)

@[simp] theorem CoreModuleType.mapX_id (m : CoreModuleType X) : m.mapX id = m := by
  cases m; simp only [CoreModuleType.mapX, id, List.map_id']

/-! ## Entity sorts -/

def Entity.sort : Entity R X → EntitySort
  | .module _ => .module
  | .func _ => .func
  | .value _ => .value
  | .type _ => .type
  | .instance _ => .instance
  | .component _ => .component

/-! ## Renaming of resource variables -/

mutual
  /-- Substitute resource variables (binders and occurrences alike). -/
  def TypeDef.map (f : R → S) : TypeDef R X → TypeDef S X
    | .val t => .val (t.mapResource f)
    | .resource r => .resource (f r)
    | .func t => .func (t.mapResource f)
    | .instance t => .instance (t.map f)
    | .component t => .component (t.map f)

  def Entity.map (f : R → S) : Entity R X → Entity S X
    | .module t => .module t
    | .func t => .func (t.mapResource f)
    | .value t => .value (t.mapResource f)
    | .type t => .type (t.map f)
    | .instance t => .instance (t.map f)
    | .component t => .component (t.map f)

  def InstanceType.map (f : R → S) : InstanceType R X → InstanceType S X
    | ⟨d, es⟩ => ⟨d.map f, Entity.mapList f es⟩

  def ComponentType.map (f : R → S) : ComponentType R X → ComponentType S X
    | ⟨i, is, d, es⟩ => ⟨i.map f, Entity.mapList f is, d.map f, Entity.mapList f es⟩

  def Entity.mapList (f : R → S) : List (String × Entity R X) → List (String × Entity S X)
    | [] => []
    | (n, e) :: es => (n, e.map f) :: Entity.mapList f es
end

mutual
  /-- Change the core extern type. -/
  def TypeDef.mapX (g : X → Y) : TypeDef R X → TypeDef R Y
    | .val t => .val t
    | .resource r => .resource r
    | .func t => .func t
    | .instance t => .instance (t.mapX g)
    | .component t => .component (t.mapX g)

  def Entity.mapX (g : X → Y) : Entity R X → Entity R Y
    | .module t => .module (t.mapX g)
    | .func t => .func t
    | .value t => .value t
    | .type t => .type (t.mapX g)
    | .instance t => .instance (t.mapX g)
    | .component t => .component (t.mapX g)

  def InstanceType.mapX (g : X → Y) : InstanceType R X → InstanceType R Y
    | ⟨d, es⟩ => ⟨d, Entity.mapXList g es⟩

  def ComponentType.mapX (g : X → Y) : ComponentType R X → ComponentType R Y
    | ⟨i, is, d, es⟩ => ⟨i, Entity.mapXList g is, d, Entity.mapXList g es⟩

  def Entity.mapXList (g : X → Y) : List (String × Entity R X) → List (String × Entity R Y)
    | [] => []
    | (n, e) :: es => (n, e.mapX g) :: Entity.mapXList g es
end

mutual
  @[simp] theorem TypeDef.map_id : ∀ t : TypeDef R X, t.map id = t
    | .val t => by simp only [TypeDef.map, WIT.ValType.mapResource_id]
    | .resource _ => rfl
    | .func t => by simp only [TypeDef.map, WIT.FuncType.mapResource_id]
    | .instance t => by simp only [TypeDef.map, InstanceType.map_id t]
    | .component t => by simp only [TypeDef.map, ComponentType.map_id t]

  @[simp] theorem Entity.map_id : ∀ e : Entity R X, e.map id = e
    | .module _ => rfl
    | .func t => by simp only [Entity.map, WIT.FuncType.mapResource_id]
    | .value t => by simp only [Entity.map, WIT.ValType.mapResource_id]
    | .type t => by simp only [Entity.map, TypeDef.map_id t]
    | .instance t => by simp only [Entity.map, InstanceType.map_id t]
    | .component t => by simp only [Entity.map, ComponentType.map_id t]

  @[simp] theorem InstanceType.map_id : ∀ t : InstanceType R X, t.map id = t
    | ⟨d, es⟩ => by simp only [InstanceType.map, List.map_id, Entity.mapList_id es]

  @[simp] theorem ComponentType.map_id : ∀ t : ComponentType R X, t.map id = t
    | ⟨i, is, d, es⟩ => by
      simp only [ComponentType.map, List.map_id, Entity.mapList_id is, Entity.mapList_id es]

  @[simp] theorem Entity.mapList_id :
      ∀ es : List (String × Entity R X), Entity.mapList id es = es
    | [] => rfl
    | (_, e) :: es => by simp only [Entity.mapList, Entity.map_id e, Entity.mapList_id es]
end

mutual
  @[simp] theorem TypeDef.mapX_id : ∀ t : TypeDef R X, t.mapX id = t
    | .val _ | .resource _ | .func _ => rfl
    | .instance t => by simp only [TypeDef.mapX, InstanceType.mapX_id t]
    | .component t => by simp only [TypeDef.mapX, ComponentType.mapX_id t]

  @[simp] theorem Entity.mapX_id : ∀ e : Entity R X, e.mapX id = e
    | .func _ | .value _ => rfl
    | .module t => by simp only [Entity.mapX, CoreModuleType.mapX_id]
    | .type t => by simp only [Entity.mapX, TypeDef.mapX_id t]
    | .instance t => by simp only [Entity.mapX, InstanceType.mapX_id t]
    | .component t => by simp only [Entity.mapX, ComponentType.mapX_id t]

  @[simp] theorem InstanceType.mapX_id : ∀ t : InstanceType R X, t.mapX id = t
    | ⟨d, es⟩ => by simp only [InstanceType.mapX, Entity.mapXList_id es]

  @[simp] theorem ComponentType.mapX_id : ∀ t : ComponentType R X, t.mapX id = t
    | ⟨i, is, d, es⟩ => by
      simp only [ComponentType.mapX, Entity.mapXList_id is, Entity.mapXList_id es]

  @[simp] theorem Entity.mapXList_id :
      ∀ es : List (String × Entity R X), Entity.mapXList id es = es
    | [] => rfl
    | (_, e) :: es => by simp only [Entity.mapXList, Entity.mapX_id e, Entity.mapXList_id es]
end

/-! ## Free variables and well-scopedness -/

section FreeVars

variable [DecidableEq R]

/-- Remove the variables bound by `binders`. -/
def unbind (binders : List R) (vs : List R) : List R := vs.filter fun r => decide (r ∉ binders)

mutual
  /-- Free resource variables (with repetitions), binders removed. -/
  def TypeDef.fv : TypeDef R X → List R
    | .val t => t.fv
    | .resource r => [r]
    | .func t => t.fv
    | .instance t => t.fv
    | .component t => t.fv

  def Entity.fv : Entity R X → List R
    | .module _ => []
    | .func t => t.fv
    | .value t => t.fv
    | .type t => t.fv
    | .instance t => t.fv
    | .component t => t.fv

  /-- `defined` binds in `exports`. -/
  def InstanceType.fv : InstanceType R X → List R
    | ⟨d, es⟩ => unbind d (Entity.fvList es)

  /-- `imported` binds in imports and exports; `defined` binds in exports. -/
  def ComponentType.fv : ComponentType R X → List R
    | ⟨i, is, d, es⟩ => unbind i (Entity.fvList is ++ unbind d (Entity.fvList es))

  def Entity.fvList : List (String × Entity R X) → List R
    | [] => []
    | (_, e) :: es => e.fv ++ Entity.fvList es
end

/-- All free variables are in the ambient context `ctx`. -/
def TypeDef.WellScoped (ctx : List R) (t : TypeDef R X) : Prop := ∀ r ∈ t.fv, r ∈ ctx
def Entity.WellScoped (ctx : List R) (e : Entity R X) : Prop := ∀ r ∈ e.fv, r ∈ ctx
def InstanceType.WellScoped (ctx : List R) (t : InstanceType R X) : Prop :=
  ∀ r ∈ t.fv, r ∈ ctx
def ComponentType.WellScoped (ctx : List R) (t : ComponentType R X) : Prop :=
  ∀ r ∈ t.fv, r ∈ ctx

instance (ctx : List R) (t : TypeDef R X) : Decidable (t.WellScoped ctx) :=
  inferInstanceAs (Decidable (∀ r ∈ t.fv, r ∈ ctx))
instance (ctx : List R) (e : Entity R X) : Decidable (e.WellScoped ctx) :=
  inferInstanceAs (Decidable (∀ r ∈ e.fv, r ∈ ctx))
instance (ctx : List R) (t : InstanceType R X) : Decidable (t.WellScoped ctx) :=
  inferInstanceAs (Decidable (∀ r ∈ t.fv, r ∈ ctx))
instance (ctx : List R) (t : ComponentType R X) : Decidable (t.WellScoped ctx) :=
  inferInstanceAs (Decidable (∀ r ∈ t.fv, r ∈ ctx))

end FreeVars

/-! ## Lookup -/

def InstanceType.lookupExport (t : InstanceType R X) (name : String) : Option (Entity R X) :=
  t.exports.lookup name

def ComponentType.lookupImport (t : ComponentType R X) (name : String) :
    Option (Entity R X) :=
  t.imports.lookup name

def ComponentType.lookupExport (t : ComponentType R X) (name : String) :
    Option (Entity R X) :=
  t.exports.lookup name

/-! ## Tests -/

/-- `func (param "x" (own r0)) (param "y" (borrow r0)) (result (own r0))` (a valid
function type: `borrow` occurs only in parameter position). -/
def exampleFunc : FuncType Nat :=
  { params := [("x", .own 0), ("y", .borrow 0)], result := some (.own 0) }

/-- A component importing resource `0` (∀-bound), defining resource `2`
(∃-bound) and mentioning an outer resource `1`. -/
def exampleComponent : ComponentType Nat Unit where
  imported := [0]
  imports := [("r", .type (.resource 0)),
    ("m", .module { imports := [(("a", "b"), ())], exports := [] })]
  defined := [2]
  exports := [("f", .func exampleFunc),
    ("g", .func { params := [("y", .borrow 1)], result := some (.own 2) }),
    ("t", .type (.resource 2))]

/-- Binder convention for instance imports: the resource `r` exported by the
imported instance `i` is ∀-bound in `imported` (the imported instance type has
`defined = []`), so an export mentioning `own 0` has no free variables. -/
def exampleInstanceImport : ComponentType Nat Unit where
  imported := [0]
  imports := [("i", .instance { defined := [], exports := [("r", .type (.resource 0))] })]
  defined := []
  exports := [("f", .func { params := [], result := some (.own 0) })]

end Silmaril.Wasm.Component.Types

namespace Silmaril.Wasm.Component.Types

universe u v w x y z
variable {R : Type u} {S : Type w} {T : Type x} {X : Type v} {Y : Type y} {Z : Type z}

section FreeVars

variable [DecidableEq R]

theorem mem_unbind {binders vs : List R} {r : R} :
    r ∈ unbind binders vs ↔ r ∈ vs ∧ r ∉ binders := by
  simp only [unbind, List.mem_filter, decide_eq_true_eq]

end FreeVars

end Silmaril.Wasm.Component.Types
