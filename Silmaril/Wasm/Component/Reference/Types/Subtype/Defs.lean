module

public import Silmaril.Wasm.Component.Reference.Types.Basic.Defs

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

/-- wasmparser's `Remapping` of resource variables, as an association list (first entry
wins). -/
abbrev Remapping (R : Type u) := List (R × R)

/-- The target of `r` in the remapping, if any (first entry wins). -/
def Remapping.find? [DecidableEq R] : Remapping R → R → Option R
  | [], _ => none
  | (a, b) :: m, r => if a = r then some b else Remapping.find? m r

/-- The renaming function of a remapping restricted to `binders`: identity outside `binders`
and on binders the remapping leaves unmapped. -/
def Remapping.apply [DecidableEq R] (m : Remapping R) (binders : List R) (r : R) : R :=
  if r ∈ binders then (m.find? r).getD r else r

/-! ## Core module types -/

/-- Core module subtyping (wasmparser `module_type`): every import of `a` is present in `b`
with `XSub (b's import) (a's import)` (contravariant), and every export of `b` is present in
`a` with `XSub (a's export) (b's export)` (covariant). -/
def CoreModuleType.Sub (XSub : X → X → Prop) (a b : CoreModuleType X) : Prop :=
  (∀ k x, (k, x) ∈ a.imports → ∃ y, (k, y) ∈ b.imports ∧ XSub y x) ∧
    (∀ k y, (k, y) ∈ b.exports → ∃ x, (k, x) ∈ a.exports ∧ XSub x y)

theorem CoreModuleType.Sub.trans {XSub : X → X → Prop}
    (hX : ∀ x y z, XSub x y → XSub y z → XSub x z) {a b c : CoreModuleType X}
    (h₁ : CoreModuleType.Sub XSub a b) (h₂ : CoreModuleType.Sub XSub b c) :
    CoreModuleType.Sub XSub a c := by
  refine ⟨fun k x hx => ?_, fun k z hz => ?_⟩
  · obtain ⟨y, hy, hyx⟩ := h₁.1 k x hx
    obtain ⟨z, hz, hzy⟩ := h₂.1 k y hy
    exact ⟨z, hz, hX _ _ _ hzy hyx⟩
  · obtain ⟨y, hy, hyz⟩ := h₂.2 k z hz
    obtain ⟨x, hx, hxy⟩ := h₁.2 k y hy
    exact ⟨x, hx, hX _ _ _ hxy hyz⟩

/-! ## Binders, variables and renaming targets

`binders` lists every binder occurrence at any depth; `vars` lists every variable occurrence
(binders included, free or bound); `ComponentType.inner` are the binders *nested* in the
imports and exports of a component type (its own top-level `imported`/`defined` excluded).
`ComponentType.RenameTarget a b v` is the range constraint of the renamings of
`ComponentType.Sub a b`: `v` occurs in `a` or `b` and is not a nested binder of either. -/

mutual
  /-- Every binder occurrence (`InstanceType.defined`, `ComponentType.imported`/`defined`) at
  any depth, in order, with repetitions. -/
  def TypeDef.binders : TypeDef R X → List R
    | .val _ | .resource _ | .func _ => []
    | .instance t => t.binders
    | .component t => t.binders

  def Entity.binders : Entity R X → List R
    | .module _ | .func _ | .value _ => []
    | .type t => t.binders
    | .instance t => t.binders
    | .component t => t.binders

  def InstanceType.binders : InstanceType R X → List R
    | ⟨d, es⟩ => d ++ Entity.bindersList es

  def ComponentType.binders : ComponentType R X → List R
    | ⟨i, is, d, es⟩ => i ++ d ++ (Entity.bindersList is ++ Entity.bindersList es)

  def Entity.bindersList : List (String × Entity R X) → List R
    | [] => []
    | (_, e) :: es => e.binders ++ Entity.bindersList es
end

mutual
  /-- Every variable occurrence at any depth (binders and occurrences, free or bound), in
  order, with repetitions. -/
  def TypeDef.vars : TypeDef R X → List R
    | .val t => t.fv
    | .resource r => [r]
    | .func t => t.fv
    | .instance t => t.vars
    | .component t => t.vars

  def Entity.vars : Entity R X → List R
    | .module _ => []
    | .func t => t.fv
    | .value t => t.fv
    | .type t => t.vars
    | .instance t => t.vars
    | .component t => t.vars

  def InstanceType.vars : InstanceType R X → List R
    | ⟨d, es⟩ => d ++ Entity.varsList es

  def ComponentType.vars : ComponentType R X → List R
    | ⟨i, is, d, es⟩ => i ++ d ++ (Entity.varsList is ++ Entity.varsList es)

  def Entity.varsList : List (String × Entity R X) → List R
    | [] => []
    | (_, e) :: es => e.vars ++ Entity.varsList es
end

/-- The binders nested in the imports and exports of a component type. -/
def ComponentType.inner (t : ComponentType R X) : List R :=
  Entity.bindersList t.imports ++ Entity.bindersList t.exports

/-- The range constraint on the renamings of `ComponentType.Sub a b`: `v` occurs in `a` or `b`
and is not a binder nested in either (wasmparser's renamings target resources found on the
other side, never ones bound inside an entity). -/
def ComponentType.RenameTarget (a b : ComponentType R X) (v : R) : Prop :=
  v ∈ a.vars ++ b.vars ∧ v ∉ a.inner ++ b.inner

/-! ## The subtyping relation -/

mutual
  /-- Entity subtyping (wasmparser `component_entity_type`): sorts agree, then dispatch. -/
  inductive Entity.Sub (XSub : X → X → Prop) : Entity R X → Entity R X → Prop
    | module {a b : CoreModuleType X} :
        CoreModuleType.Sub XSub a b → Entity.Sub XSub (.module a) (.module b)
    /-- Function types: exact equality (names, types, `async_`). -/
    | func {t : FuncType R} : Entity.Sub XSub (.func t) (.func t)
    /-- Value types: exact structural equality. -/
    | value {t : ValType R} : Entity.Sub XSub (.value t) (.value t)
    | type {a b : TypeDef R X} : TypeDef.Sub XSub a b → Entity.Sub XSub (.type a) (.type b)
    | «instance» {a b : InstanceType R X} :
        InstanceType.Sub XSub a b → Entity.Sub XSub (.instance a) (.instance b)
    | component {a b : ComponentType R X} :
        ComponentType.Sub XSub a b → Entity.Sub XSub (.component a) (.component b)

  /-- Subtyping of what a `type` export denotes (wasmparser `component_any_type_id`). -/
  inductive TypeDef.Sub (XSub : X → X → Prop) : TypeDef R X → TypeDef R X → Prop
    | val {t : ValType R} : TypeDef.Sub XSub (.val t) (.val t)
    /-- Resources: equal variables. -/
    | resource {r : R} : TypeDef.Sub XSub (.resource r) (.resource r)
    | func {t : FuncType R} : TypeDef.Sub XSub (.func t) (.func t)
    | «instance» {a b : InstanceType R X} :
        InstanceType.Sub XSub a b → TypeDef.Sub XSub (.instance a) (.instance b)
    | component {a b : ComponentType R X} :
        ComponentType.Sub XSub a b → TypeDef.Sub XSub (.component a) (.component b)

  /-- Instance width subtyping (wasmparser `instance_type`). -/
  inductive InstanceType.Sub (XSub : X → X → Prop) : InstanceType R X → InstanceType R X → Prop
    | mk {a b : InstanceType R X} :
        Entity.ListSub XSub a.exports b.exports → InstanceType.Sub XSub a b

  /-- Component subtyping (wasmparser `component_type`) with explicit renamings: `f` moves only
  `a`'s ∀-variables and makes `b`'s imports satisfy `a`'s imports, and `g` moves only `b`'s
  ∃-variables and makes `a`'s exports (after `f`) satisfy `b`'s exports. Each moved variable is
  sent to itself or to a `ComponentType.RenameTarget a b` (a variable of `a` or `b` that is not
  a nested binder), the relational counterpart of wasmparser mapping to the resources found on
  the other side (see the module docstring).

  Deviation (incompleteness): complete w.r.t. wasmparser only for hoisted types (every import-
  or export-position instance type has `defined = []`, as wasmparser's
  `prepare_instance_import`/`prepare_instance_export` and `WIT/Encode.lean` produce). A
  non-hoisted pair such as `exNestedA <: exNestedB` (`Subtype/Trans.lean`), accepted by
  wasmparser and by the relation without the range constraint, is rejected (see the module
  docstring). -/
  inductive ComponentType.Sub (XSub : X → X → Prop) :
      ComponentType R X → ComponentType R X → Prop
    | mk {a b : ComponentType R X} (f g : R → R)
        (hf : ∀ r, r ∉ a.imported → f r = r)
        (hfr : ∀ r ∈ a.imported, f r = r ∨ ComponentType.RenameTarget a b (f r))
        (imports : Entity.ListSub XSub b.imports (Entity.mapList f a.imports))
        (hg : ∀ r, r ∉ b.defined → g r = r)
        (hgr : ∀ r ∈ b.defined, g r = r ∨ ComponentType.RenameTarget a b (g r))
        (exports : Entity.ListSub XSub (Entity.mapList f a.exports)
          (Entity.mapList g b.exports)) :
        ComponentType.Sub XSub a b

  /-- `ListSub as bs`: every entry `(n, b)` of `bs` has an entry `(n, a)` in `as` with
  `a <: b` (name-keyed width subtyping of export/import lists). -/
  inductive Entity.ListSub (XSub : X → X → Prop) :
      List (String × Entity R X) → List (String × Entity R X) → Prop
    | nil {as : List (String × Entity R X)} : Entity.ListSub XSub as []
    | cons {as bs : List (String × Entity R X)} {n : String} {a b : Entity R X} :
        (n, a) ∈ as → Entity.Sub XSub a b → Entity.ListSub XSub as bs →
          Entity.ListSub XSub as ((n, b) :: bs)
end

variable {XSub : X → X → Prop}

/-! ## Pointwise characterisation of `ListSub` -/

/-! ## Reflexivity -/

/-! ## Closure under injective renaming -/

/-- Transport a renaming `f` of `R` along `h : R → S`: `h (f r)` at `h r`, identity outside the
range of `h`. -/
noncomputable def conjRenaming (h : R → S) (f : R → R) (s : S) : S :=
  open Classical in
  if hs : ∃ r, h r = s then h (f hs.choose) else s

/-! ## Nesting depth

`depth` counts nested `type`/`instance`/`component` entity layers. It is invariant under
renaming (`Entity.depth_map`) and bounds the recursion of the executable checker. -/

mutual
  def TypeDef.depth : TypeDef R X → Nat
    | .val _ | .resource _ | .func _ => 0
    | .instance t => t.depth
    | .component t => t.depth

  def Entity.depth : Entity R X → Nat
    | .module _ | .func _ | .value _ => 0
    | .type t => t.depth + 1
    | .instance t => t.depth + 1
    | .component t => t.depth + 1

  def InstanceType.depth : InstanceType R X → Nat
    | ⟨_, es⟩ => Entity.depthList es

  def ComponentType.depth : ComponentType R X → Nat
    | ⟨_, is, _, es⟩ => max (Entity.depthList is) (Entity.depthList es)

  def Entity.depthList : List (String × Entity R X) → Nat
    | [] => 0
    | (_, e) :: es => max e.depth (Entity.depthList es)
end

mutual
  @[simp] theorem TypeDef.depth_map (f : R → S) : ∀ t : TypeDef R X, (t.map f).depth = t.depth
    | .val _ | .resource _ | .func _ => rfl
    | .instance t => by simp only [TypeDef.map, TypeDef.depth, InstanceType.depth_map f t]
    | .component t => by simp only [TypeDef.map, TypeDef.depth, ComponentType.depth_map f t]

  @[simp] theorem Entity.depth_map (f : R → S) : ∀ e : Entity R X, (e.map f).depth = e.depth
    | .module _ | .func _ | .value _ => rfl
    | .type t => by simp only [Entity.map, Entity.depth, TypeDef.depth_map f t]
    | .instance t => by simp only [Entity.map, Entity.depth, InstanceType.depth_map f t]
    | .component t => by simp only [Entity.map, Entity.depth, ComponentType.depth_map f t]

  @[simp] theorem InstanceType.depth_map (f : R → S) :
      ∀ t : InstanceType R X, (t.map f).depth = t.depth
    | ⟨_, es⟩ => by simp only [InstanceType.map, InstanceType.depth, Entity.depthList_map f es]

  @[simp] theorem ComponentType.depth_map (f : R → S) :
      ∀ t : ComponentType R X, (t.map f).depth = t.depth
    | ⟨_, is, _, es⟩ => by
      simp only [ComponentType.map, ComponentType.depth, Entity.depthList_map f is,
        Entity.depthList_map f es]

  @[simp] theorem Entity.depthList_map (f : R → S) :
      ∀ es : List (String × Entity R X), Entity.depthList (Entity.mapList f es) =
        Entity.depthList es
    | [] => rfl
    | (_, e) :: es => by
      simp only [Entity.mapList, Entity.depthList, Entity.depth_map f e,
        Entity.depthList_map f es]
end

/-! ## Component nesting depth

`compDepth` counts only nested `component` layers (`type`/`instance` layers are transparent). A
middle type with `compDepth = 0` contains no component type at all, so transitivity through it
needs no hypothesis (`Entity.Sub.trans_of_compDepth_eq_zero`); `ComponentTransBelow R XSub N`
speaks about component middles of `compDepth < N`, the measure of the induction in
`Types/Subtype/Trans.lean`. -/

mutual
  def TypeDef.compDepth : TypeDef R X → Nat
    | .val _ | .resource _ | .func _ => 0
    | .instance t => t.compDepth
    | .component t => t.compDepth + 1

  def Entity.compDepth : Entity R X → Nat
    | .module _ | .func _ | .value _ => 0
    | .type t => t.compDepth
    | .instance t => t.compDepth
    | .component t => t.compDepth + 1

  def InstanceType.compDepth : InstanceType R X → Nat
    | ⟨_, es⟩ => Entity.compDepthList es

  def ComponentType.compDepth : ComponentType R X → Nat
    | ⟨_, is, _, es⟩ => max (Entity.compDepthList is) (Entity.compDepthList es)

  def Entity.compDepthList : List (String × Entity R X) → Nat
    | [] => 0
    | (_, e) :: es => max e.compDepth (Entity.compDepthList es)
end

mutual
  @[simp] theorem TypeDef.compDepth_map (f : R → S) :
      ∀ t : TypeDef R X, (t.map f).compDepth = t.compDepth
    | .val _ | .resource _ | .func _ => rfl
    | .instance t => by
      simp only [TypeDef.map, TypeDef.compDepth, InstanceType.compDepth_map f t]
    | .component t => by
      simp only [TypeDef.map, TypeDef.compDepth, ComponentType.compDepth_map f t]

  @[simp] theorem Entity.compDepth_map (f : R → S) :
      ∀ e : Entity R X, (e.map f).compDepth = e.compDepth
    | .module _ | .func _ | .value _ => rfl
    | .type t => by simp only [Entity.map, Entity.compDepth, TypeDef.compDepth_map f t]
    | .instance t => by
      simp only [Entity.map, Entity.compDepth, InstanceType.compDepth_map f t]
    | .component t => by
      simp only [Entity.map, Entity.compDepth, ComponentType.compDepth_map f t]

  @[simp] theorem InstanceType.compDepth_map (f : R → S) :
      ∀ t : InstanceType R X, (t.map f).compDepth = t.compDepth
    | ⟨_, es⟩ => by
      simp only [InstanceType.map, InstanceType.compDepth, Entity.compDepthList_map f es]

  @[simp] theorem ComponentType.compDepth_map (f : R → S) :
      ∀ t : ComponentType R X, (t.map f).compDepth = t.compDepth
    | ⟨_, is, _, es⟩ => by
      simp only [ComponentType.map, ComponentType.compDepth, Entity.compDepthList_map f is,
        Entity.compDepthList_map f es]

  @[simp] theorem Entity.compDepthList_map (f : R → S) :
      ∀ es : List (String × Entity R X), Entity.compDepthList (Entity.mapList f es) =
        Entity.compDepthList es
    | [] => rfl
    | (_, e) :: es => by
      simp only [Entity.mapList, Entity.compDepthList, Entity.compDepth_map f e,
        Entity.compDepthList_map f es]
end

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

theorem Entity.binders_sublist_of_mem {es : List (String × Entity R X)} {n : String}
    {e : Entity R X} (h : (n, e) ∈ es) : e.binders.Sublist (Entity.bindersList es) := by
  induction es with
  | nil => exact nomatch h
  | cons p es ih =>
    obtain ⟨n', e'⟩ := p
    simp only [Entity.bindersList]
    rcases List.mem_cons.1 h with h | h
    · cases h; exact List.sublist_append_left _ _
    · exact (ih h).trans (List.sublist_append_right _ _)

/-- Nodup/freshness of binder lists is inherited by sub-lists, each losing a prefix `D` that
joins the context. -/
theorem fresh_nest {Γ A B C A' B' C' Da Db Dc : List R}
    (hnd : (A ++ B ++ C).Nodup) (hΓ : ∀ r ∈ A ++ B ++ C, r ∉ Γ)
    (ha : (Da ++ A').Sublist A) (hb : (Db ++ B').Sublist B) (hc : (Dc ++ C').Sublist C) :
    (A' ++ B' ++ C').Nodup ∧ ∀ r ∈ A' ++ B' ++ C', r ∉ Γ ++ Da ++ Db ++ Dc := by
  have hs : ((Da ++ A') ++ (Db ++ B') ++ (Dc ++ C')).Sublist (A ++ B ++ C) :=
    (ha.append hb).append hc
  have hp : ((Da ++ A') ++ (Db ++ B') ++ (Dc ++ C')).Perm
      ((A' ++ B' ++ C') ++ (Da ++ Db ++ Dc)) := by
    classical
    rw [List.perm_iff_count]; intro x; simp only [List.count_append]; omega
  have hnd' := hp.nodup_iff.1 (hnd.sublist hs)
  rw [List.nodup_append] at hnd'
  refine ⟨hnd'.1, fun r hr hr' => ?_⟩
  have hmem : r ∈ A ++ B ++ C :=
    hs.subset (hp.symm.subset (List.mem_append_left _ hr))
  simp only [List.append_assoc, List.mem_append] at hr'
  rcases hr' with hr' | hr'
  · exact hΓ r hmem hr'
  · exact hnd'.2.2 r hr r (by simp only [List.append_assoc, List.mem_append]; exact hr') rfl

section Fresh

variable [DecidableEq R]

/-- The Barendregt convention for a transitivity triple (see the section docstring). -/
def Entity.FreshTriple (Γ : List R) (a b c : Entity R X) : Prop :=
  a.WellScoped Γ ∧ b.WellScoped Γ ∧ c.WellScoped Γ ∧
    (a.binders ++ b.binders ++ c.binders).Nodup ∧
      ∀ r ∈ a.binders ++ b.binders ++ c.binders, r ∉ Γ

theorem Entity.mem_fvList_of_mem {es : List (String × Entity R X)} {n : String}
    {e : Entity R X} (h : (n, e) ∈ es) {r : R} (hr : r ∈ e.fv) : r ∈ Entity.fvList es := by
  induction es with
  | nil => exact nomatch h
  | cons p es ih =>
    obtain ⟨n', e'⟩ := p
    simp only [Entity.fvList, List.mem_append]
    rcases List.mem_cons.1 h with h | h
    · cases h; exact Or.inl hr
    · exact Or.inr (ih h)

/-- An entry of an instance type is scoped in the context extended by its `defined`. -/
theorem Entity.WellScoped.instance_entry {Γ d : List R} {es : List (String × Entity R X)}
    (h : (Entity.instance ⟨d, es⟩ : Entity R X).WellScoped Γ) {n : String} {e : Entity R X}
    (he : (n, e) ∈ es) (Δ : List R) (hΔ : ∀ r, r ∈ Γ ∨ r ∈ d → r ∈ Δ) : e.WellScoped Δ := by
  intro r hr
  have hl := Entity.mem_fvList_of_mem he hr
  by_cases hd : r ∈ d
  · exact hΔ r (Or.inr hd)
  · exact hΔ r (Or.inl (h r (mem_unbind.2 ⟨hl, hd⟩)))

/-- The Barendregt condition passes to same-named entries of three instance types, in the
context extended by the three `defined` lists. -/
theorem Entity.FreshTriple.instance {Γ da db dc : List R}
    {ea eb ec : List (String × Entity R X)}
    (h : Entity.FreshTriple Γ (.instance ⟨da, ea⟩) (.instance ⟨db, eb⟩) (.instance ⟨dc, ec⟩))
    {n : String} {a b c : Entity R X} (ha : (n, a) ∈ ea) (hb : (n, b) ∈ eb)
    (hc : (n, c) ∈ ec) : Entity.FreshTriple (Γ ++ da ++ db ++ dc) a b c := by
  obtain ⟨sa, sb, sc, hnd, hΓ⟩ := h
  have hf := fresh_nest (Da := da) (Db := db) (Dc := dc) hnd hΓ
    ((Entity.binders_sublist_of_mem ha).append_left da)
    ((Entity.binders_sublist_of_mem hb).append_left db)
    ((Entity.binders_sublist_of_mem hc).append_left dc)
  refine ⟨sa.instance_entry ha _ ?_, sb.instance_entry hb _ ?_, sc.instance_entry hc _ ?_,
    hf.1, hf.2⟩ <;>
    · intro r hr; simp only [List.append_assoc, List.mem_append]; tauto

end Fresh

/-! ## Transitivity (modulo component types) -/

section NoComponent

/-! Middles without component types (`compDepth = 0`): transitivity needs only a transitive
`XSub`, and no freshness condition. -/

end NoComponent

section Trans

variable [DecidableEq R]

/-- Transitivity of component-type subtyping for Barendregt triples (`Entity.FreshTriple`),
taken as a hypothesis by `Entity.Sub.trans_of_componentTrans` and proved as `componentTrans`
in `Types/Subtype/Trans.lean`. Without the freshness premise the statement is false
(`componentTrans_unscoped_false`). -/
def ComponentTrans (R : Type u) [DecidableEq R] (XSub : X → X → Prop) : Prop :=
  ∀ (Γ : List R) (a b c : ComponentType R X),
    Entity.FreshTriple Γ (.component a) (.component b) (.component c) →
    ComponentType.Sub XSub a b → ComponentType.Sub XSub b c → ComponentType.Sub XSub a c

/-- `ComponentTrans` restricted to middle types of `compDepth < N` (the induction hypothesis
shape of the structural induction `Entity.Sub.trans_below`). -/
def ComponentTransBelow (R : Type u) [DecidableEq R] (XSub : X → X → Prop) (N : Nat) : Prop :=
  ∀ (Γ : List R) (a b c : ComponentType R X), b.compDepth < N →
    Entity.FreshTriple Γ (.component a) (.component b) (.component c) →
    ComponentType.Sub XSub a b → ComponentType.Sub XSub b c → ComponentType.Sub XSub a c

end Trans

end Silmaril.Wasm.Component.Types
