module

public import Silmaril.Wasm.Component.Reference.Types.Subtype.Thms
public import Silmaril.Wasm.Component.Reference.Types.Subtype.Defs

public import Silmaril.Raw.Wasm.Component.Types.Basic

/-!
# Subtyping of semantic component types (relational)

The relational subtyping `Entity.Sub XSub a b` ("`a` may be used where `b` is expected") on
the index-free types of `Types/Basic.lean`, following the Explainer §Type Checking rule
"subtyping is only relaxed for `module`, `instance` and `component` types" (a subtype may
import less and export more; only names matter) and wasmparser's `SubtypeCx`
(`crates/wasmparser/src/validator/component_types.rs`, the checker wasmtime uses):

* **sorts** must agree (`Entity.Sub.sort_eq`);
* **function types**: exact equality, including parameter names and the `async_` flag
  (wasmparser is intentionally conservative here);
* **value types**: exact structural equality (`own r`/`borrow r` compare resource variables);
* **resources** (`TypeDef.resource`): equal variables;
* **instance types**: width subtyping — every export of the supertype is present, by name, in
  the subtype with a subtype entity (`Entity.ListSub`); the ∃-binders `defined` are ignored,
  as in wasmparser's `instance_type` (abstract resources are global identities there);
* **core module types**: contravariant imports and covariant exports, pointwise through the
  supplied core extern subtyping `XSub : X → X → Prop` (wasmparser `module_type`,
  `entity_type`; the V1/Lime1 profiles instantiate it with the core-engine extern subtyping);
* **component types** (`ComponentType.Sub`), wasmparser's three steps with explicit renaming
  functions: a renaming `f` that moves only `A`'s ∀-variables (`A.imported`; identity
  elsewhere) such that `B.imports` satisfy `A.imports` after `f`
  (`open_instance_type(B.imports ⊢ A, Import)`), and a renaming `g` that moves only `B`'s
  ∃-variables (`B.defined`) such that `A.exports` (renamed by `f`) satisfy `B.exports` after `g`
  (`open_instance_type(A.exports' ⊢ B, Export)`). `Remapping R := List (R × R)` is
  wasmparser's `Remapping` (first entry wins), with `Remapping.apply` restricting it to a
  binder list.

  **Range constraint.** Each variable moved by `f` or `g` stays put or lands on a
  `ComponentType.RenameTarget a b`: a variable occurring in `a` or `b` (`vars`) that is not a
  binder nested in either (`ComponentType.inner`). This is the relational counterpart of
  wasmparser sending each binder to the resource found at the same *path* on the other side
  (resource paths themselves are not modelled; the renamings are existentially quantified).
  A variant of the relation without this constraint is not known to be
  transitive beyond middle types without nested component types, because a renaming could
  send an irrelevant variable onto a binder nested in a third type.

  **Deviation (incompleteness w.r.t. wasmparser).** The relation is complete with
  respect to wasmparser only on **hoisted** component types: every instance type in import or
  export position of a component type has `defined = []`, its abstract resources being bound in
  the enclosing `imported` (imports) or `defined` (exports). This is the form wasmparser itself
  produces (`prepare_instance_import` / `prepare_instance_export` in
  `crates/wasmparser/src/validator/component.rs` move such resources into the enclosing
  component and empty the instance's `defined_resources`) and the form `WIT/Encode.lean`
  emits. On a non-hoisted type an export-position instance still binds its own resources, and a
  renaming that must reach them targets a nested binder, which the range constraint forbids.
  Example (`exNestedA`/`exNestedB` in `Subtype/Trans.lean`): `A` exports
  `i : instance ∃5. {t : resource 5}` and `B` is `∃7. {i : instance {t : resource 7}}`; they are
  the same type for wasmparser (after hoisting `A`), and `A <: B` holds without the range constraint
  (`g 7 = 5`), but it does not hold here. Its hoisted form (`exNestedAh`) is accepted.
  Types/Basic.lean's wording that `InstanceType.defined` is non-empty for instance types "in export
  position" should be read as "standalone instance types" (type definitions) for this relation.

Theorems: `Entity.Sub.refl` (for reflexive `XSub`) and `Entity.Sub.map` (closed under
injective renaming of resource variables), for every sort including component types.

Transitivity:
* unconditionally (given a transitive `XSub`) through every middle type that contains no
  component type (`compDepth = 0`): `Entity.Sub.trans_of_compDepth_eq_zero` and its
  `TypeDef`/`InstanceType`/`ListSub` forms;
* for every sort, `Entity.Sub.trans_of_componentTrans` and its `TypeDef`/`InstanceType`/
  `ListSub` forms, for triples satisfying the Barendregt convention `Entity.FreshTriple Γ a b c`
  (all three well scoped in `Γ`; all binder occurrences pairwise distinct and outside `Γ`),
  **given** `ComponentTrans R XSub`, transitivity of component-type subtyping for such
  triples. `ComponentTrans` is proved in `Types/Subtype/Trans.lean` (`componentTrans`),
  which also states the unconditional `Entity.Sub.trans` and its forms. The
  depth-bounded form `Entity.Sub.trans_below` only needs `ComponentTransBelow R XSub N`
  (component middles of `compDepth < N`).

The freshness premise is necessary: without it component-type subtyping is not transitive
(`componentTrans_unscoped_false` in `Subtype/Check.lean`, where `A` mentions a variable free
that the middle type `B` binds).
Lists: `Entity.ListSub` is characterised pointwise by `Entity.ListSub.iff`.

NOT modelled or claimed here: resource *paths* of binders (the renaming is existentially
quantified instead; the executable checker infers it by matching `type (resource _)` entries by
name, see `Subtype/Check.lean`); freshness of binders inside the relation itself (the
variables are drawn from a global supply, `map` is plain substitution, and freshness appears
only as the `FreshTriple` premise of transitivity); the value-type `typeidx`-naming-a-primitive
rule (index-free types have no indices).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Types

universe u v w

variable {R : Type u} {S : Type w} {X : Type v}

/-! ## Remappings -/

/-! ## Core module types -/

theorem CoreModuleType.Sub.refl {XSub : X → X → Prop} (hX : ∀ x, XSub x x)
    (a : CoreModuleType X) : CoreModuleType.Sub XSub a a :=
  ⟨fun _ x h => ⟨x, h, hX x⟩, fun _ y h => ⟨y, h, hX y⟩⟩

/-! ## Binders, variables and renaming targets

`binders` lists every binder occurrence at any depth; `vars` lists every variable occurrence
(binders included, free or bound); `ComponentType.inner` are the binders *nested* in the
imports and exports of a component type (its own top-level `imported`/`defined` excluded).
`ComponentType.RenameTarget a b v` is the range constraint of the renamings of
`ComponentType.Sub a b`: `v` occurs in `a` or `b` and is not a nested binder of either. -/

theorem ComponentType.binders_eq (t : ComponentType R X) :
    t.binders = t.imported ++ t.defined ++ t.inner := by
  cases t; rfl

theorem ComponentType.vars_eq (t : ComponentType R X) :
    t.vars = t.imported ++ t.defined ++ (Entity.varsList t.imports ++ Entity.varsList t.exports) :=
  by cases t; rfl

theorem InstanceType.binders_eq (t : InstanceType R X) :
    t.binders = t.defined ++ Entity.bindersList t.exports := by
  cases t; rfl

theorem InstanceType.vars_eq (t : InstanceType R X) :
    t.vars = t.defined ++ Entity.varsList t.exports := by
  cases t; rfl

mutual
  theorem TypeDef.binders_map (f : R → S) :
      ∀ t : TypeDef R X, (t.map f).binders = t.binders.map f
    | .val _ | .resource _ | .func _ => rfl
    | .instance t => by simp only [TypeDef.map, TypeDef.binders, InstanceType.binders_map f t]
    | .component t => by
      simp only [TypeDef.map, TypeDef.binders, ComponentType.binders_map f t]

  theorem Entity.binders_map (f : R → S) :
      ∀ e : Entity R X, (e.map f).binders = e.binders.map f
    | .module _ | .func _ | .value _ => rfl
    | .type t => by simp only [Entity.map, Entity.binders, TypeDef.binders_map f t]
    | .instance t => by simp only [Entity.map, Entity.binders, InstanceType.binders_map f t]
    | .component t => by
      simp only [Entity.map, Entity.binders, ComponentType.binders_map f t]

  theorem InstanceType.binders_map (f : R → S) :
      ∀ t : InstanceType R X, (t.map f).binders = t.binders.map f
    | ⟨_, es⟩ => by
      simp only [InstanceType.map, InstanceType.binders, Entity.bindersList_map f es,
        List.map_append]

  theorem ComponentType.binders_map (f : R → S) :
      ∀ t : ComponentType R X, (t.map f).binders = t.binders.map f
    | ⟨_, is, _, es⟩ => by
      simp only [ComponentType.map, ComponentType.binders, Entity.bindersList_map f is,
        Entity.bindersList_map f es, List.map_append]

  theorem Entity.bindersList_map (f : R → S) :
      ∀ es : List (String × Entity R X),
        Entity.bindersList (Entity.mapList f es) = (Entity.bindersList es).map f
    | [] => rfl
    | (_, e) :: es => by
      simp only [Entity.mapList, Entity.bindersList, Entity.binders_map f e,
        Entity.bindersList_map f es, List.map_append]
end

mutual
  theorem TypeDef.vars_map (f : R → S) :
      ∀ t : TypeDef R X, (t.map f).vars = t.vars.map f
    | .val t => by simp only [TypeDef.map, TypeDef.vars, WIT.ValType.fv_mapResource]
    | .resource _ => rfl
    | .func t => by simp only [TypeDef.map, TypeDef.vars, WIT.FuncType.fv_mapResource]
    | .instance t => by simp only [TypeDef.map, TypeDef.vars, InstanceType.vars_map f t]
    | .component t => by simp only [TypeDef.map, TypeDef.vars, ComponentType.vars_map f t]

  theorem Entity.vars_map (f : R → S) :
      ∀ e : Entity R X, (e.map f).vars = e.vars.map f
    | .module _ => rfl
    | .func t => by simp only [Entity.map, Entity.vars, WIT.FuncType.fv_mapResource]
    | .value t => by simp only [Entity.map, Entity.vars, WIT.ValType.fv_mapResource]
    | .type t => by simp only [Entity.map, Entity.vars, TypeDef.vars_map f t]
    | .instance t => by simp only [Entity.map, Entity.vars, InstanceType.vars_map f t]
    | .component t => by simp only [Entity.map, Entity.vars, ComponentType.vars_map f t]

  theorem InstanceType.vars_map (f : R → S) :
      ∀ t : InstanceType R X, (t.map f).vars = t.vars.map f
    | ⟨_, es⟩ => by
      simp only [InstanceType.map, InstanceType.vars, Entity.varsList_map f es,
        List.map_append]

  theorem ComponentType.vars_map (f : R → S) :
      ∀ t : ComponentType R X, (t.map f).vars = t.vars.map f
    | ⟨_, is, _, es⟩ => by
      simp only [ComponentType.map, ComponentType.vars, Entity.varsList_map f is,
        Entity.varsList_map f es, List.map_append]

  theorem Entity.varsList_map (f : R → S) :
      ∀ es : List (String × Entity R X),
        Entity.varsList (Entity.mapList f es) = (Entity.varsList es).map f
    | [] => rfl
    | (_, e) :: es => by
      simp only [Entity.mapList, Entity.varsList, Entity.vars_map f e,
        Entity.varsList_map f es, List.map_append]
end

theorem ComponentType.inner_map (f : R → S) (t : ComponentType R X) :
    (t.map f).inner = t.inner.map f := by
  obtain ⟨_, is, _, es⟩ := t
  simp only [ComponentType.inner, ComponentType.map, Entity.bindersList_map, List.map_append]

/-! ## The subtyping relation -/

variable {XSub : X → X → Prop}

theorem Entity.Sub.sort_eq {a b : Entity R X} (h : Entity.Sub XSub a b) : a.sort = b.sort := by
  cases h <;> rfl

/-! ## Pointwise characterisation of `ListSub` -/

theorem Entity.ListSub.get {as bs : List (String × Entity R X)} :
    Entity.ListSub XSub as bs → ∀ {n b}, (n, b) ∈ bs → ∃ a, (n, a) ∈ as ∧ Entity.Sub XSub a b
  | .nil, _, _, h => nomatch h
  | .cons (a := a) ha hs rest, n, b, h => by
    rcases List.mem_cons.1 h with h | h
    · cases h; exact ⟨a, ha, hs⟩
    · exact rest.get h

theorem Entity.ListSub.iff {as bs : List (String × Entity R X)} :
    Entity.ListSub XSub as bs ↔ ∀ n b, (n, b) ∈ bs → ∃ a, (n, a) ∈ as ∧ Entity.Sub XSub a b :=
  ⟨fun h _ _ hm => h.get hm, Entity.ListSub.of_forall⟩

theorem Entity.ListSub.mono {as as' bs : List (String × Entity R X)}
    (h : Entity.ListSub XSub as bs) (hsub : ∀ p ∈ as, p ∈ as') : Entity.ListSub XSub as' bs :=
  Entity.ListSub.of_forall fun _ _ hm =>
    let ⟨a, ha, hs⟩ := h.get hm
    ⟨a, hsub _ ha, hs⟩

/-! ## Reflexivity -/

theorem InstanceType.exports_mk (d : List R) (es : List (String × Entity R X)) :
    (InstanceType.mk d es).exports = es := rfl

mutual
  theorem Entity.Sub.refl (hX : ∀ x, XSub x x) : ∀ e : Entity R X, Entity.Sub XSub e e
    | .module t => .module (CoreModuleType.Sub.refl hX t)
    | .func _ => .func
    | .value _ => .value
    | .type t => .type (TypeDef.Sub.refl hX t)
    | .instance t => .instance (InstanceType.Sub.refl hX t)
    | .component t => .component (ComponentType.Sub.refl hX t)

  theorem TypeDef.Sub.refl (hX : ∀ x, XSub x x) : ∀ t : TypeDef R X, TypeDef.Sub XSub t t
    | .val _ => .val
    | .resource _ => .resource
    | .func _ => .func
    | .instance t => .instance (InstanceType.Sub.refl hX t)
    | .component t => .component (ComponentType.Sub.refl hX t)

  theorem InstanceType.Sub.refl (hX : ∀ x, XSub x x) :
      ∀ t : InstanceType R X, InstanceType.Sub XSub t t
    | ⟨_, es⟩ => .mk (Entity.ListSub.refl hX es)

  theorem ComponentType.Sub.refl (hX : ∀ x, XSub x x) :
      ∀ t : ComponentType R X, ComponentType.Sub XSub t t
    | ⟨_, is, _, es⟩ => by
      refine .mk id id (fun _ _ => rfl) (fun _ _ => Or.inl rfl) ?_ (fun _ _ => rfl)
        (fun _ _ => Or.inl rfl) ?_
      · simp only [Entity.mapList_id]; exact Entity.ListSub.refl hX is
      · simp only [Entity.mapList_id]; exact Entity.ListSub.refl hX es

  theorem Entity.ListSub.refl (hX : ∀ x, XSub x x) :
      ∀ es : List (String × Entity R X), Entity.ListSub XSub es es
    | [] => .nil
    | (_, e) :: es =>
      .cons List.mem_cons_self (Entity.Sub.refl hX e)
        ((Entity.ListSub.refl hX es).mono fun _ hp => List.mem_cons_of_mem _ hp)
end

/-! ## Closure under injective renaming -/

theorem conjRenaming_comp {h : R → S} (hinj : Function.Injective h) (f : R → R) :
    conjRenaming h f ∘ h = h ∘ f := by
  funext r
  have hs : ∃ r', h r' = h r := ⟨r, rfl⟩
  simp only [Function.comp_apply, conjRenaming, hs, ↓reduceDIte]
  rw [hinj hs.choose_spec]

theorem conjRenaming_of_not_mem {h : R → S} (hinj : Function.Injective h) {f : R → R}
    {l : List R} (hf : ∀ r, r ∉ l → f r = r) : ∀ s, s ∉ l.map h → conjRenaming h f s = s := by
  intro s hs
  by_cases hr : ∃ r, h r = s
  · obtain ⟨r, rfl⟩ := hr
    have hr' : r ∉ l := fun hm => hs (List.mem_map_of_mem hm)
    have := congrFun (conjRenaming_comp hinj f) r
    simp only [Function.comp_apply] at this
    rw [this, hf r hr']
  · simp only [conjRenaming, hr, ↓reduceDIte]

theorem Entity.mem_mapList (f : R → S) {es : List (String × Entity R X)} {n : String}
    {e : Entity R X} (h : (n, e) ∈ es) : (n, e.map f) ∈ Entity.mapList f es := by
  induction es with
  | nil => exact nomatch h
  | cons p es ih =>
    obtain ⟨n', e'⟩ := p
    rcases List.mem_cons.1 h with h | h
    · cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem InstanceType.map_exports (f : R → S) (t : InstanceType R X) :
    (t.map f).exports = Entity.mapList f t.exports := by
  cases t; rfl

theorem ComponentType.map_imported (f : R → S) (t : ComponentType R X) :
    (t.map f).imported = t.imported.map f := by
  cases t; rfl

theorem ComponentType.map_imports (f : R → S) (t : ComponentType R X) :
    (t.map f).imports = Entity.mapList f t.imports := by
  cases t; rfl

theorem ComponentType.map_defined (f : R → S) (t : ComponentType R X) :
    (t.map f).defined = t.defined.map f := by
  cases t; rfl

theorem ComponentType.map_exports (f : R → S) (t : ComponentType R X) :
    (t.map f).exports = Entity.mapList f t.exports := by
  cases t; rfl

/-- Conjugating a renaming commutes with `mapList` along an injective `h`. -/
theorem Entity.mapList_conjRenaming {h : R → S} (hinj : Function.Injective h) (f : R → R)
    (es : List (String × Entity R X)) :
    Entity.mapList (conjRenaming h f) (Entity.mapList h es) =
      Entity.mapList h (Entity.mapList f es) := by
  rw [Entity.mapList_comp, Entity.mapList_comp, conjRenaming_comp hinj]

/-- The range constraint is transported along an injective renaming. -/
theorem RenameTarget.conj {h : R → S} (hinj : Function.Injective h) {f : R → R}
    {a b : ComponentType R X} {l : List R}
    (hfr : ∀ r ∈ l, f r = r ∨ ComponentType.RenameTarget a b (f r)) :
    ∀ s ∈ l.map h, conjRenaming h f s = s ∨
      ComponentType.RenameTarget (a.map h) (b.map h) (conjRenaming h f s) := by
  intro s hs
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hs
  have hc : conjRenaming h f (h r) = h (f r) := congrFun (conjRenaming_comp hinj f) r
  rw [hc]
  rcases hfr r hr with he | ⟨hv, hi⟩
  · exact Or.inl (by rw [he])
  · refine Or.inr ⟨?_, ?_⟩
    · rw [ComponentType.vars_map, ComponentType.vars_map, ← List.map_append]
      exact List.mem_map_of_mem hv
    · rw [ComponentType.inner_map, ComponentType.inner_map, ← List.map_append]
      intro hm
      obtain ⟨x, hx, hxe⟩ := List.mem_map.1 hm
      exact hi (hinj hxe ▸ hx)

mutual
  /-- Subtyping is closed under injective renaming of resource variables. -/
  theorem Entity.Sub.map {h : R → S} (hinj : Function.Injective h) {a b : Entity R X} :
      Entity.Sub XSub a b → Entity.Sub XSub (a.map h) (b.map h)
    | .module hm => .module hm
    | .func => .func
    | .value => .value
    | .type d => .type (TypeDef.Sub.map hinj d)
    | .instance d => .instance (InstanceType.Sub.map hinj d)
    | .component d => .component (ComponentType.Sub.map hinj d)

  theorem TypeDef.Sub.map {h : R → S} (hinj : Function.Injective h) {a b : TypeDef R X} :
      TypeDef.Sub XSub a b → TypeDef.Sub XSub (a.map h) (b.map h)
    | .val => .val
    | .resource => .resource
    | .func => .func
    | .instance d => .instance (InstanceType.Sub.map hinj d)
    | .component d => .component (ComponentType.Sub.map hinj d)

  theorem InstanceType.Sub.map {h : R → S} (hinj : Function.Injective h)
      {a b : InstanceType R X} :
      InstanceType.Sub XSub a b → InstanceType.Sub XSub (a.map h) (b.map h)
    | .mk l => .mk (by
        rw [InstanceType.map_exports, InstanceType.map_exports]
        exact Entity.ListSub.map hinj l)

  theorem ComponentType.Sub.map {h : R → S} (hinj : Function.Injective h)
      {a b : ComponentType R X} :
      ComponentType.Sub XSub a b → ComponentType.Sub XSub (a.map h) (b.map h)
    | .mk f g hf hfr li hg hgr le => by
      refine .mk (conjRenaming h f) (conjRenaming h g) ?_ ?_ ?_ ?_ ?_ ?_
      · rw [ComponentType.map_imported]; exact conjRenaming_of_not_mem hinj hf
      · rw [ComponentType.map_imported]
        exact RenameTarget.conj hinj hfr
      · rw [ComponentType.map_imports, ComponentType.map_imports,
          Entity.mapList_conjRenaming hinj]
        exact Entity.ListSub.map hinj li
      · rw [ComponentType.map_defined]; exact conjRenaming_of_not_mem hinj hg
      · rw [ComponentType.map_defined]
        exact RenameTarget.conj hinj hgr
      · rw [ComponentType.map_exports, ComponentType.map_exports,
          Entity.mapList_conjRenaming hinj, Entity.mapList_conjRenaming hinj]
        exact Entity.ListSub.map hinj le

  theorem Entity.ListSub.map {h : R → S} (hinj : Function.Injective h)
      {as bs : List (String × Entity R X)} :
      Entity.ListSub XSub as bs →
        Entity.ListSub XSub (Entity.mapList h as) (Entity.mapList h bs)
    | .nil => .nil
    | .cons ha hs rest =>
      .cons (Entity.mem_mapList h ha) (Entity.Sub.map hinj hs) (Entity.ListSub.map hinj rest)
end

/-! ## Nesting depth

`depth` counts nested `type`/`instance`/`component` entity layers. It is invariant under
renaming (`Entity.depth_map`) and bounds the recursion of the executable checker. -/

theorem Entity.depth_le_depthList {es : List (String × Entity R X)} {n : String}
    {e : Entity R X} (h : (n, e) ∈ es) : e.depth ≤ Entity.depthList es := by
  induction es with
  | nil => exact nomatch h
  | cons p es ih =>
    obtain ⟨n', e'⟩ := p
    simp only [Entity.depthList]
    rcases List.mem_cons.1 h with h | h
    · cases h; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-! ## Component nesting depth

`compDepth` counts only nested `component` layers (`type`/`instance` layers are transparent). A
middle type with `compDepth = 0` contains no component type at all, so transitivity through it
needs no hypothesis (`Entity.Sub.trans_of_compDepth_eq_zero`); `ComponentTransBelow R XSub N`
speaks about component middles of `compDepth < N`, the measure of the induction in
`Types/Subtype/Trans.lean`. -/

/-! ## Binders and the freshness (Barendregt) condition

Transitivity of `ComponentType.Sub` fails without a freshness condition, because `map` is plain
substitution and `ComponentType.Sub.mk` lets the subtype mention, free, a variable that the
middle type binds (the counterexample is `componentTrans_unscoped_false` in
`Subtype/Check.lean`: `A` mentions a free `own 1`, `B` ∀-binds `1`, and `B <: C` instantiates
it). `Entity.FreshTriple Γ a b c` is the Barendregt convention for the three types of a
transitivity step: all three are well scoped in the ambient context `Γ`, and every binder
occurrence (`imported`/`defined` at any depth, `Entity.binders`) in the three types is
distinct from every other one and from `Γ`. It is inherited by same-named entries of
instance types (`Entity.FreshTriple.instance`), which is what threads it through
`Entity.Sub.trans_below`. -/

section Fresh

variable [DecidableEq R]

end Fresh

/-! ## Transitivity (modulo component types) -/

/-- `ListSub` is transitive given transitivity at every same-named triple of entries. -/
theorem Entity.ListSub.trans_of {as bs cs : List (String × Entity R X)}
    (ht : ∀ n a b c, (n, a) ∈ as → (n, b) ∈ bs → (n, c) ∈ cs →
      Entity.Sub XSub a b → Entity.Sub XSub b c → Entity.Sub XSub a c)
    (h₁ : Entity.ListSub XSub as bs) (h₂ : Entity.ListSub XSub bs cs) :
    Entity.ListSub XSub as cs :=
  Entity.ListSub.of_forall fun n c hc =>
    let ⟨b, hb, hbc⟩ := h₂.get hc
    let ⟨a, ha, hab⟩ := h₁.get hb
    ⟨a, ha, ht n a b c ha hb hc hab hbc⟩

section NoComponent

/-! Middles without component types (`compDepth = 0`): transitivity needs only a transitive
`XSub`, and no freshness condition. -/

mutual
  theorem Entity.Sub.trans_flat (hX : ∀ x y z, XSub x y → XSub y z → XSub x z) :
      ∀ (b : Entity R X), b.compDepth ≤ 0 → ∀ (a c : Entity R X),
        Entity.Sub XSub a b → Entity.Sub XSub b c → Entity.Sub XSub a c
    | .module _, _, _, _, h₁, h₂ => by
      cases h₁ with | module h₁ => cases h₂ with | module h₂ =>
        exact .module (CoreModuleType.Sub.trans hX h₁ h₂)
    | .func _, _, _, _, h₁, h₂ => by cases h₁; cases h₂; exact .func
    | .value _, _, _, _, h₁, h₂ => by cases h₁; cases h₂; exact .value
    | .type t, hd, _, _, h₁, h₂ => by
      cases h₁ with | type h₁ => cases h₂ with | type h₂ =>
        exact .type (TypeDef.Sub.trans_flat hX t hd _ _ h₁ h₂)
    | .instance t, hd, _, _, h₁, h₂ => by
      cases h₁ with | «instance» h₁ => cases h₂ with | «instance» h₂ =>
        exact .instance (InstanceType.Sub.trans_flat hX t hd _ _ h₁ h₂)
    | .component _, hd, _, _, _, _ => absurd hd (Nat.not_succ_le_zero _)

  theorem TypeDef.Sub.trans_flat (hX : ∀ x y z, XSub x y → XSub y z → XSub x z) :
      ∀ (b : TypeDef R X), b.compDepth ≤ 0 → ∀ (a c : TypeDef R X),
        TypeDef.Sub XSub a b → TypeDef.Sub XSub b c → TypeDef.Sub XSub a c
    | .val _, _, _, _, h₁, h₂ => by cases h₁; cases h₂; exact .val
    | .resource _, _, _, _, h₁, h₂ => by cases h₁; cases h₂; exact .resource
    | .func _, _, _, _, h₁, h₂ => by cases h₁; cases h₂; exact .func
    | .instance t, hd, _, _, h₁, h₂ => by
      cases h₁ with | «instance» h₁ => cases h₂ with | «instance» h₂ =>
        exact .instance (InstanceType.Sub.trans_flat hX t hd _ _ h₁ h₂)
    | .component _, hd, _, _, _, _ => absurd hd (Nat.not_succ_le_zero _)

  theorem InstanceType.Sub.trans_flat (hX : ∀ x y z, XSub x y → XSub y z → XSub x z) :
      ∀ (b : InstanceType R X), b.compDepth ≤ 0 → ∀ (a c : InstanceType R X),
        InstanceType.Sub XSub a b → InstanceType.Sub XSub b c → InstanceType.Sub XSub a c
    | ⟨_, es⟩, hd, _, _, .mk h₁, .mk h₂ =>
      .mk (Entity.ListSub.trans_of
        (fun n a b c _ hb _ => Entity.Sub.trans_flat_list hX es hd n b hb a c) h₁ h₂)

  theorem Entity.Sub.trans_flat_list (hX : ∀ x y z, XSub x y → XSub y z → XSub x z) :
      ∀ (es : List (String × Entity R X)), Entity.compDepthList es ≤ 0 →
        ∀ (n : String) (b : Entity R X), (n, b) ∈ es → ∀ a c,
          Entity.Sub XSub a b → Entity.Sub XSub b c → Entity.Sub XSub a c
    | [], _, _, _, h => nomatch h
    | (_, e) :: es, hd, n, b, h => by
      simp only [Entity.compDepthList, Nat.max_le] at hd
      rcases List.mem_cons.1 h with h | h
      · cases h; exact Entity.Sub.trans_flat hX e hd.1
      · exact Entity.Sub.trans_flat_list hX es hd.2 n b h
end

/-- Unconditional transitivity through a middle type containing no component type. -/
theorem Entity.Sub.trans_of_compDepth_eq_zero (hX : ∀ x y z, XSub x y → XSub y z → XSub x z)
    {a b c : Entity R X} (hb : b.compDepth = 0) (h₁ : Entity.Sub XSub a b)
    (h₂ : Entity.Sub XSub b c) : Entity.Sub XSub a c :=
  Entity.Sub.trans_flat hX b (Nat.le_of_eq hb) a c h₁ h₂

theorem TypeDef.Sub.trans_of_compDepth_eq_zero (hX : ∀ x y z, XSub x y → XSub y z → XSub x z)
    {a b c : TypeDef R X} (hb : b.compDepth = 0) (h₁ : TypeDef.Sub XSub a b)
    (h₂ : TypeDef.Sub XSub b c) : TypeDef.Sub XSub a c :=
  TypeDef.Sub.trans_flat hX b (Nat.le_of_eq hb) a c h₁ h₂

theorem InstanceType.Sub.trans_of_compDepth_eq_zero
    (hX : ∀ x y z, XSub x y → XSub y z → XSub x z) {a b c : InstanceType R X}
    (hb : b.compDepth = 0) (h₁ : InstanceType.Sub XSub a b) (h₂ : InstanceType.Sub XSub b c) :
    InstanceType.Sub XSub a c :=
  InstanceType.Sub.trans_flat hX b (Nat.le_of_eq hb) a c h₁ h₂

theorem Entity.ListSub.trans_of_compDepth_eq_zero
    (hX : ∀ x y z, XSub x y → XSub y z → XSub x z) {as bs cs : List (String × Entity R X)}
    (hb : Entity.compDepthList bs = 0) (h₁ : Entity.ListSub XSub as bs)
    (h₂ : Entity.ListSub XSub bs cs) : Entity.ListSub XSub as cs :=
  Entity.ListSub.trans_of
    (fun n _ b _ _ hbm _ => Entity.Sub.trans_flat_list hX bs (Nat.le_of_eq hb) n b hbm _ _)
    h₁ h₂

end NoComponent

section Trans

variable [DecidableEq R]

theorem ComponentTrans.below {XSub : X → X → Prop} (hc : ComponentTrans R XSub) (N : Nat) :
    ComponentTransBelow R XSub N :=
  fun Γ a b c _ hw h₁ h₂ => hc Γ a b c hw h₁ h₂

/-- `ComponentTransBelow 0` holds vacuously. -/
theorem componentTransBelow_zero {XSub : X → X → Prop} : ComponentTransBelow R XSub 0 :=
  fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)

mutual
  /-- Depth-bounded transitivity, by structural recursion on the middle entity: only
  component-type middles (of `compDepth < N`) use the hypothesis `hc`, and the Barendregt
  condition is threaded to them. -/
  theorem Entity.Sub.trans_below (hX : ∀ x y z, XSub x y → XSub y z → XSub x z) {N : Nat}
      (hc : ComponentTransBelow R XSub N) :
      ∀ (b : Entity R X), b.compDepth ≤ N → ∀ (Γ : List R) (a c : Entity R X),
        Entity.FreshTriple Γ a b c →
        Entity.Sub XSub a b → Entity.Sub XSub b c → Entity.Sub XSub a c
    | .module _, _, _, _, _, _, h₁, h₂ => by
      cases h₁ with | module h₁ => cases h₂ with | module h₂ =>
        exact .module (CoreModuleType.Sub.trans hX h₁ h₂)
    | .func _, _, _, _, _, _, h₁, h₂ => by cases h₁; cases h₂; exact .func
    | .value _, _, _, _, _, _, h₁, h₂ => by cases h₁; cases h₂; exact .value
    | .type t, hd, Γ, _, _, hw, h₁, h₂ => by
      cases h₁ with | type h₁ => cases h₂ with | type h₂ =>
        exact .type (TypeDef.Sub.trans_below hX hc t hd Γ _ _ hw h₁ h₂)
    | .instance t, hd, Γ, _, _, hw, h₁, h₂ => by
      cases h₁ with | «instance» h₁ => cases h₂ with | «instance» h₂ =>
        exact .instance (InstanceType.Sub.trans_below hX hc t hd Γ _ _ hw h₁ h₂)
    | .component t, hd, Γ, _, _, hw, h₁, h₂ => by
      cases h₁ with | component h₁ => cases h₂ with | component h₂ =>
        exact .component (hc Γ _ t _ hd hw h₁ h₂)

  theorem TypeDef.Sub.trans_below (hX : ∀ x y z, XSub x y → XSub y z → XSub x z) {N : Nat}
      (hc : ComponentTransBelow R XSub N) :
      ∀ (b : TypeDef R X), b.compDepth ≤ N → ∀ (Γ : List R) (a c : TypeDef R X),
        Entity.FreshTriple Γ (.type a) (.type b) (.type c) →
        TypeDef.Sub XSub a b → TypeDef.Sub XSub b c → TypeDef.Sub XSub a c
    | .val _, _, _, _, _, _, h₁, h₂ => by cases h₁; cases h₂; exact .val
    | .resource _, _, _, _, _, _, h₁, h₂ => by cases h₁; cases h₂; exact .resource
    | .func _, _, _, _, _, _, h₁, h₂ => by cases h₁; cases h₂; exact .func
    | .instance t, hd, Γ, _, _, hw, h₁, h₂ => by
      cases h₁ with | «instance» h₁ => cases h₂ with | «instance» h₂ =>
        exact .instance (InstanceType.Sub.trans_below hX hc t hd Γ _ _ hw h₁ h₂)
    | .component t, hd, Γ, _, _, hw, h₁, h₂ => by
      cases h₁ with | component h₁ => cases h₂ with | component h₂ =>
        exact .component (hc Γ _ t _ hd hw h₁ h₂)

  theorem InstanceType.Sub.trans_below (hX : ∀ x y z, XSub x y → XSub y z → XSub x z)
      {N : Nat} (hc : ComponentTransBelow R XSub N) :
      ∀ (b : InstanceType R X), b.compDepth ≤ N → ∀ (Γ : List R) (a c : InstanceType R X),
        Entity.FreshTriple Γ (.instance a) (.instance b) (.instance c) →
        InstanceType.Sub XSub a b → InstanceType.Sub XSub b c → InstanceType.Sub XSub a c
    | ⟨_, es⟩, hd, _, ⟨_, _⟩, ⟨_, _⟩, hw, .mk h₁, .mk h₂ =>
      .mk (Entity.ListSub.trans_of
        (fun n a b c ha hb hc' => Entity.Sub.trans_list hX hc es hd n b hb _ a c
          (hw.instance ha hb hc')) h₁ h₂)

  theorem Entity.Sub.trans_list (hX : ∀ x y z, XSub x y → XSub y z → XSub x z) {N : Nat}
      (hc : ComponentTransBelow R XSub N) :
      ∀ (es : List (String × Entity R X)), Entity.compDepthList es ≤ N →
        ∀ (n : String) (b : Entity R X), (n, b) ∈ es → ∀ (Γ : List R) (a c : Entity R X),
          Entity.FreshTriple Γ a b c →
          Entity.Sub XSub a b → Entity.Sub XSub b c → Entity.Sub XSub a c
    | [], _, _, _, h => nomatch h
    | (_, e) :: es, hd, n, b, h => by
      simp only [Entity.compDepthList, Nat.max_le] at hd
      rcases List.mem_cons.1 h with h | h
      · cases h; exact Entity.Sub.trans_below hX hc e hd.1
      · exact Entity.Sub.trans_list hX hc es hd.2 n b h
end

/-- Transitivity of entity subtyping for every sort, for Barendregt triples, given
transitivity of `XSub` and of component-type subtyping (`ComponentTrans`, proved as
`componentTrans` in `Types/Subtype/Trans.lean`, which states the unconditional
`Entity.Sub.trans`). -/
theorem Entity.Sub.trans_of_componentTrans (hX : ∀ x y z, XSub x y → XSub y z → XSub x z)
    (hc : ComponentTrans R XSub) {Γ : List R} {a b c : Entity R X}
    (hw : Entity.FreshTriple Γ a b c) (h₁ : Entity.Sub XSub a b)
    (h₂ : Entity.Sub XSub b c) : Entity.Sub XSub a c :=
  Entity.Sub.trans_below hX (hc.below b.compDepth) b (Nat.le_refl _) Γ a c hw h₁ h₂

theorem TypeDef.Sub.trans_of_componentTrans (hX : ∀ x y z, XSub x y → XSub y z → XSub x z)
    (hc : ComponentTrans R XSub) {Γ : List R} {a b c : TypeDef R X}
    (hw : Entity.FreshTriple Γ (.type a) (.type b) (.type c)) (h₁ : TypeDef.Sub XSub a b)
    (h₂ : TypeDef.Sub XSub b c) : TypeDef.Sub XSub a c :=
  TypeDef.Sub.trans_below hX (hc.below b.compDepth) b (Nat.le_refl _) Γ a c hw h₁ h₂

theorem InstanceType.Sub.trans_of_componentTrans (hX : ∀ x y z, XSub x y → XSub y z → XSub x z)
    (hc : ComponentTrans R XSub) {Γ : List R} {a b c : InstanceType R X}
    (hw : Entity.FreshTriple Γ (.instance a) (.instance b) (.instance c))
    (h₁ : InstanceType.Sub XSub a b) (h₂ : InstanceType.Sub XSub b c) :
    InstanceType.Sub XSub a c :=
  InstanceType.Sub.trans_below hX (hc.below b.compDepth) b (Nat.le_refl _) Γ a c hw h₁ h₂

theorem Entity.ListSub.trans_of_componentTrans (hX : ∀ x y z, XSub x y → XSub y z → XSub x z)
    (hc : ComponentTrans R XSub) {Γ : List R} {as bs cs : List (String × Entity R X)}
    (hw : ∀ n a b c, (n, a) ∈ as → (n, b) ∈ bs → (n, c) ∈ cs → Entity.FreshTriple Γ a b c)
    (h₁ : Entity.ListSub XSub as bs) (h₂ : Entity.ListSub XSub bs cs) :
    Entity.ListSub XSub as cs :=
  Entity.ListSub.trans_of
    (fun n a b c ha hb hc' => Entity.Sub.trans_of_componentTrans hX hc (hw n a b c ha hb hc')) h₁ h₂

end Trans

end Silmaril.Wasm.Component.Types
