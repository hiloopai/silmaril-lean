module

public import Silmaril.Wasm.Component.Reference.Types.Basic.Defs

public import Silmaril.Raw.Wasm.Component.ABI.Layout
public import Silmaril.Raw.Wasm.Component.ABI.Flatten
public import Silmaril.Raw.Wasm.Component.ABI.Calling

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
  theorem ValType.mapResource_comp (f : R → S) (g : S → T) :
      ∀ t : ValType Ref R, (t.mapResource f).mapResource g = t.mapResource (g ∘ f)
    | .prim _ | .ref _ | .enum _ | .flags _ | .errorContext | .own _ | .borrow _ => rfl
    | .list t | .fixedList t _ | .option t | .map _ t => by
      simp only [ValType.mapResource, ValType.mapResource_comp f g t]
    | .record fs => by
      simp only [ValType.mapResource, ValType.mapResourceFields_comp f g fs]
    | .tuple ts => by simp only [ValType.mapResource, ValType.mapResourceList_comp f g ts]
    | .variant cs => by
      simp only [ValType.mapResource, ValType.mapResourceCases_comp f g cs]
    | .result ok err => by
      simp only [ValType.mapResource, ValType.mapResourceOption_comp f g ok,
        ValType.mapResourceOption_comp f g err]
    | .future e | .stream e => by
      simp only [ValType.mapResource, ValType.mapResourceOption_comp f g e]

  theorem ValType.mapResourceFields_comp (f : R → S) (g : S → T) :
      ∀ fs : List (String × ValType Ref R),
        ValType.mapResourceFields g (ValType.mapResourceFields f fs) =
          ValType.mapResourceFields (g ∘ f) fs
    | [] => rfl
    | (_, t) :: fs => by
      simp only [ValType.mapResourceFields, ValType.mapResource_comp f g t,
        ValType.mapResourceFields_comp f g fs]

  theorem ValType.mapResourceList_comp (f : R → S) (g : S → T) :
      ∀ ts : List (ValType Ref R),
        ValType.mapResourceList g (ValType.mapResourceList f ts) =
          ValType.mapResourceList (g ∘ f) ts
    | [] => rfl
    | t :: ts => by
      simp only [ValType.mapResourceList, ValType.mapResource_comp f g t,
        ValType.mapResourceList_comp f g ts]

  theorem ValType.mapResourceCases_comp (f : R → S) (g : S → T) :
      ∀ cs : List (String × Option (ValType Ref R)),
        ValType.mapResourceCases g (ValType.mapResourceCases f cs) =
          ValType.mapResourceCases (g ∘ f) cs
    | [] => rfl
    | (_, t) :: cs => by
      simp only [ValType.mapResourceCases, ValType.mapResourceOption_comp f g t,
        ValType.mapResourceCases_comp f g cs]

  theorem ValType.mapResourceOption_comp (f : R → S) (g : S → T) :
      ∀ t : Option (ValType Ref R),
        ValType.mapResourceOption g (ValType.mapResourceOption f t) =
          ValType.mapResourceOption (g ∘ f) t
    | none => rfl
    | some t => by simp only [ValType.mapResourceOption, ValType.mapResource_comp f g t]
end

mutual
  /-- Renaming acts on free resource variables pointwise. -/
  theorem ValType.fv_mapResource (f : R → S) :
      ∀ t : ValType Ref R, (t.mapResource f).fv = t.fv.map f
    | .prim _ | .ref _ | .enum _ | .flags _ | .errorContext | .own _ | .borrow _ => rfl
    | .list t | .fixedList t _ | .option t | .map _ t => by
      simp only [ValType.mapResource, ValType.fv, ValType.fv_mapResource f t]
    | .record fs => by
      simp only [ValType.mapResource, ValType.fv, ValType.fvFields_mapResource f fs]
    | .tuple ts => by
      simp only [ValType.mapResource, ValType.fv, ValType.fvList_mapResource f ts]
    | .variant cs => by
      simp only [ValType.mapResource, ValType.fv, ValType.fvCases_mapResource f cs]
    | .result ok err => by
      simp only [ValType.mapResource, ValType.fv, ValType.fvOption_mapResource f ok,
        ValType.fvOption_mapResource f err, List.map_append]
    | .future e | .stream e => by
      simp only [ValType.mapResource, ValType.fv, ValType.fvOption_mapResource f e]

  theorem ValType.fvFields_mapResource (f : R → S) :
      ∀ fs : List (String × ValType Ref R),
        ValType.fvFields (ValType.mapResourceFields f fs) = (ValType.fvFields fs).map f
    | [] => rfl
    | (_, t) :: fs => by
      simp only [ValType.mapResourceFields, ValType.fvFields, ValType.fv_mapResource f t,
        ValType.fvFields_mapResource f fs, List.map_append]

  theorem ValType.fvList_mapResource (f : R → S) :
      ∀ ts : List (ValType Ref R),
        ValType.fvList (ValType.mapResourceList f ts) = (ValType.fvList ts).map f
    | [] => rfl
    | t :: ts => by
      simp only [ValType.mapResourceList, ValType.fvList, ValType.fv_mapResource f t,
        ValType.fvList_mapResource f ts, List.map_append]

  theorem ValType.fvCases_mapResource (f : R → S) :
      ∀ cs : List (String × Option (ValType Ref R)),
        ValType.fvCases (ValType.mapResourceCases f cs) = (ValType.fvCases cs).map f
    | [] => rfl
    | (_, t) :: cs => by
      simp only [ValType.mapResourceCases, ValType.fvCases, ValType.fvOption_mapResource f t,
        ValType.fvCases_mapResource f cs, List.map_append]

  theorem ValType.fvOption_mapResource (f : R → S) :
      ∀ t : Option (ValType Ref R),
        ValType.fvOption (ValType.mapResourceOption f t) = (ValType.fvOption t).map f
    | none => rfl
    | some t => by
      simp only [ValType.mapResourceOption, ValType.fvOption, ValType.fv_mapResource f t]
end

theorem FuncType.mapResource_comp (f : R → S) (g : S → T) (ft : FuncType Ref R) :
    (ft.mapResource f).mapResource g = ft.mapResource (g ∘ f) := by
  simp only [FuncType.mapResource, ValType.mapResourceFields_comp,
    ValType.mapResourceOption_comp]

theorem FuncType.fv_mapResource (f : R → S) (ft : FuncType Ref R) :
    (ft.mapResource f).fv = ft.fv.map f := by
  simp only [FuncType.fv, FuncType.mapResource, ValType.fvFields_mapResource,
    ValType.fvOption_mapResource, List.map_append]

end MapResource

end Silmaril.Wasm.Component.WIT

namespace Silmaril.Wasm.Component.ABI

universe u v

variable {R : Type u} {S : Type v}

end Silmaril.Wasm.Component.ABI

namespace Silmaril.Wasm.Component.Types

universe u v w x y z

variable {R : Type u} {S : Type w} {T : Type x} {X : Type v} {Y : Type y} {Z : Type z}

/-! ## Core module types -/

theorem CoreModuleType.mapX_comp (g : X → Y) (h : Y → Z) (m : CoreModuleType X) :
    (m.mapX g).mapX h = m.mapX (h ∘ g) := by
  simp only [CoreModuleType.mapX, List.map_map, Function.comp_def]

/-! ## Entity sorts -/

/-! ## Renaming of resource variables -/

mutual
  theorem TypeDef.map_comp (f : R → S) (g : S → T) :
      ∀ t : TypeDef R X, (t.map f).map g = t.map (g ∘ f)
    | .val t => by simp only [TypeDef.map, WIT.ValType.mapResource_comp]
    | .resource _ => rfl
    | .func t => by simp only [TypeDef.map, WIT.FuncType.mapResource_comp]
    | .instance t => by simp only [TypeDef.map, InstanceType.map_comp f g t]
    | .component t => by simp only [TypeDef.map, ComponentType.map_comp f g t]

  theorem Entity.map_comp (f : R → S) (g : S → T) :
      ∀ e : Entity R X, (e.map f).map g = e.map (g ∘ f)
    | .module _ => rfl
    | .func t => by simp only [Entity.map, WIT.FuncType.mapResource_comp]
    | .value t => by simp only [Entity.map, WIT.ValType.mapResource_comp]
    | .type t => by simp only [Entity.map, TypeDef.map_comp f g t]
    | .instance t => by simp only [Entity.map, InstanceType.map_comp f g t]
    | .component t => by simp only [Entity.map, ComponentType.map_comp f g t]

  theorem InstanceType.map_comp (f : R → S) (g : S → T) :
      ∀ t : InstanceType R X, (t.map f).map g = t.map (g ∘ f)
    | ⟨d, es⟩ => by simp only [InstanceType.map, List.map_map, Entity.mapList_comp f g es]

  theorem ComponentType.map_comp (f : R → S) (g : S → T) :
      ∀ t : ComponentType R X, (t.map f).map g = t.map (g ∘ f)
    | ⟨i, is, d, es⟩ => by
      simp only [ComponentType.map, List.map_map, Entity.mapList_comp f g is,
        Entity.mapList_comp f g es]

  theorem Entity.mapList_comp (f : R → S) (g : S → T) :
      ∀ es : List (String × Entity R X),
        Entity.mapList g (Entity.mapList f es) = Entity.mapList (g ∘ f) es
    | [] => rfl
    | (_, e) :: es => by
      simp only [Entity.mapList, Entity.map_comp f g e, Entity.mapList_comp f g es]
end

mutual
  theorem TypeDef.mapX_comp (g : X → Y) (h : Y → Z) :
      ∀ t : TypeDef R X, (t.mapX g).mapX h = t.mapX (h ∘ g)
    | .val _ | .resource _ | .func _ => rfl
    | .instance t => by simp only [TypeDef.mapX, InstanceType.mapX_comp g h t]
    | .component t => by simp only [TypeDef.mapX, ComponentType.mapX_comp g h t]

  theorem Entity.mapX_comp (g : X → Y) (h : Y → Z) :
      ∀ e : Entity R X, (e.mapX g).mapX h = e.mapX (h ∘ g)
    | .func _ | .value _ => rfl
    | .module t => by simp only [Entity.mapX, CoreModuleType.mapX_comp]
    | .type t => by simp only [Entity.mapX, TypeDef.mapX_comp g h t]
    | .instance t => by simp only [Entity.mapX, InstanceType.mapX_comp g h t]
    | .component t => by simp only [Entity.mapX, ComponentType.mapX_comp g h t]

  theorem InstanceType.mapX_comp (g : X → Y) (h : Y → Z) :
      ∀ t : InstanceType R X, (t.mapX g).mapX h = t.mapX (h ∘ g)
    | ⟨d, es⟩ => by simp only [InstanceType.mapX, Entity.mapXList_comp g h es]

  theorem ComponentType.mapX_comp (g : X → Y) (h : Y → Z) :
      ∀ t : ComponentType R X, (t.mapX g).mapX h = t.mapX (h ∘ g)
    | ⟨i, is, d, es⟩ => by
      simp only [ComponentType.mapX, Entity.mapXList_comp g h is, Entity.mapXList_comp g h es]

  theorem Entity.mapXList_comp (g : X → Y) (h : Y → Z) :
      ∀ es : List (String × Entity R X),
        Entity.mapXList h (Entity.mapXList g es) = Entity.mapXList (h ∘ g) es
    | [] => rfl
    | (_, e) :: es => by
      simp only [Entity.mapXList, Entity.mapX_comp g h e, Entity.mapXList_comp g h es]
end

mutual
  /-- Renaming resource variables commutes with changing the core extern type. -/
  theorem TypeDef.map_mapX (f : R → S) (g : X → Y) :
      ∀ t : TypeDef R X, (t.mapX g).map f = (t.map f).mapX g
    | .val _ | .resource _ | .func _ => rfl
    | .instance t => by simp only [TypeDef.mapX, TypeDef.map, InstanceType.map_mapX f g t]
    | .component t => by simp only [TypeDef.mapX, TypeDef.map, ComponentType.map_mapX f g t]

  theorem Entity.map_mapX (f : R → S) (g : X → Y) :
      ∀ e : Entity R X, (e.mapX g).map f = (e.map f).mapX g
    | .func _ | .value _ | .module _ => rfl
    | .type t => by simp only [Entity.mapX, Entity.map, TypeDef.map_mapX f g t]
    | .instance t => by simp only [Entity.mapX, Entity.map, InstanceType.map_mapX f g t]
    | .component t => by simp only [Entity.mapX, Entity.map, ComponentType.map_mapX f g t]

  theorem InstanceType.map_mapX (f : R → S) (g : X → Y) :
      ∀ t : InstanceType R X, (t.mapX g).map f = (t.map f).mapX g
    | ⟨d, es⟩ => by
      simp only [InstanceType.mapX, InstanceType.map, Entity.mapList_mapXList f g es]

  theorem ComponentType.map_mapX (f : R → S) (g : X → Y) :
      ∀ t : ComponentType R X, (t.mapX g).map f = (t.map f).mapX g
    | ⟨i, is, d, es⟩ => by
      simp only [ComponentType.mapX, ComponentType.map, Entity.mapList_mapXList f g is,
        Entity.mapList_mapXList f g es]

  theorem Entity.mapList_mapXList (f : R → S) (g : X → Y) :
      ∀ es : List (String × Entity R X),
        Entity.mapList f (Entity.mapXList g es) = Entity.mapXList g (Entity.mapList f es)
    | [] => rfl
    | (_, e) :: es => by
      simp only [Entity.mapXList, Entity.mapList, Entity.map_mapX f g e,
        Entity.mapList_mapXList f g es]
end

/-! ## Free variables and well-scopedness -/

section FreeVars

variable [DecidableEq R]

theorem ComponentType.WellScoped.mono {ctx ctx' : List R} {t : ComponentType R X}
    (h : t.WellScoped ctx) (sub : ∀ r ∈ ctx, r ∈ ctx') : t.WellScoped ctx' :=
  fun r hr => sub r (h r hr)

end FreeVars

/-! ## Lookup -/

/-! ## Tests -/

theorem exampleFunc_map :
    exampleFunc.mapResource (· + 7) =
      { params := [("x", .own 7), ("y", .borrow 7)], result := some (.own 7) } := rfl

theorem exampleFunc_fv : exampleFunc.fv = [0, 0, 0] := by decide +kernel

theorem exampleFunc_entity_map :
    (Entity.func exampleFunc : Entity Nat Unit).map (fun _ => 3) =
      .func { params := [("x", .own 3), ("y", .borrow 3)], result := some (.own 3) } :=
  rfl

theorem exampleComponent_fv : exampleComponent.fv = [1] := by decide +kernel

theorem exampleComponent_wellScoped : exampleComponent.WellScoped [1] := by decide +kernel

theorem exampleComponent_not_closed : ¬ exampleComponent.WellScoped [] := by decide +kernel

theorem exampleComponent_lookup :
    (exampleComponent.lookupImport "r").map Entity.sort = some .type ∧
      (exampleComponent.lookupExport "g").map Entity.sort = some .func ∧
      exampleComponent.lookupExport "r" = none := by
  refine ⟨rfl, rfl, rfl⟩

theorem exampleComponent_map_fv :
    (exampleComponent.map (· + 10)).fv = [11] := by decide +kernel

theorem exampleInstanceImport_fv : exampleInstanceImport.fv = [] := by decide +kernel

theorem exampleInstanceImport_wellScoped : exampleInstanceImport.WellScoped [] := by
  decide +kernel

end Silmaril.Wasm.Component.Types
