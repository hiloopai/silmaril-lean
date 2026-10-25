module

public import Silmaril.Logic.Metamath.Model.Basic
public import Silmaril.Logic.SetTheory.Formula
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-!
# Environment models

The standard models of set.mm-like predicate calculus (Carneiro, *Models for
Metamath*, §3.3). Fix a domain `D` of objects and an infinite type `N` of
object-language variable names. An environment assigns an object to each name
(`SetTheory.Env D N`).

Each syntax sort is of one of three kinds (`Env.Kind`):

* a name sort, such as set.mm's `setvar`, whose values are names;
* a formula sort, such as `wff`, whose values are formulas `Env D N → Prop`
  with finite support;
* a term sort with values in a type `T`, such as `class` (`T = Set D`), whose
  values are functions of environments into `T` with finite support
  (`Env.Term`).

Freshness (`Env.Kind.Fresh`) is distinctness between names, "not free"
between a name and a formula or term (`Env.NotFree`: it ignores the value of
the name), and always true between formulas and terms. It is symmetric, and every kind has a
value fresh for finitely many given values (`Env.Kind.exists_fresh`): a
constant term, or a name outside the finitely many names and supports.

An environment model (`EnvModel`) assigns a kind to each sort and interprets
the syntax rules on these domains, compositionally for freshness, together
with a truth predicate. It is a model of the grammar (`EnvModel.toModel`). A
disjoint-variable condition `$d x ph` between a set variable and a formula
variable then says that the formula does not depend on the name of `x`
(`Env.notFree_iff`, relating to `SetTheory.Wff.NotFree`).

Finitely supported terms are closed under the operations used by set.mm's
syntax (`Env.Term.map`, `Env.Term.map₂`, the binder `Env.Term.bind` and the
names `Env.Term.name`), which preserve "not free" as freshness requires.
-/

namespace Silmaril.Logic.Metamath

open Silmaril.Logic.SetTheory Function

universe u w

namespace Env

variable {D N : Type w} [DecidableEq N]

/-- `f` only depends on the values of the names in `S`. -/
def DependsOn {T : Sort*} (f : Env D N → T) (S : Finset N) : Prop :=
  ∀ ρ ρ' : Env D N, (∀ x ∈ S, ρ x = ρ' x) → f ρ = f ρ'

/-- `f` ignores the value of the name `x`. -/
def NotFree {T : Sort*} (x : N) (f : Env D N → T) : Prop := ∀ ρ m, f (update ρ x m) = f ρ

theorem DependsOn.notFree {T : Sort*} {f : Env D N → T} {S : Finset N} (h : DependsOn f S)
    {x : N} (hx : x ∉ S) : NotFree x f :=
  fun _ _ => h _ _ fun y hy => update_of_ne (by rintro rfl; exact hx hy) _ _

omit [DecidableEq N] in
theorem DependsOn.mono {T : Sort*} {f : Env D N → T} {S S' : Finset N} (h : DependsOn f S)
    (hS : S ⊆ S') : DependsOn f S' :=
  fun ρ ρ' hρ => h ρ ρ' fun x hx => hρ x (hS hx)

omit [DecidableEq N] in
theorem dependsOn_const {T : Sort*} (t : T) : DependsOn (D := D) (N := N) (fun _ => t) ∅ :=
  fun _ _ _ => rfl

/-- For formulas, "not free" is `SetTheory.Wff.NotFree`. -/
theorem notFree_iff {x : N} {φ : Env D N → Prop} : NotFree x φ ↔ Wff.NotFree x φ :=
  ⟨fun h ρ m => h ρ m ▸ Iff.rfl, fun h ρ m => propext (h ρ m)⟩

variable (D N) in
/-- Functions of environments into `T` with finite support. -/
abbrev Term (T : Type*) := {f : Env D N → T // ∃ S : Finset N, DependsOn f S}

/-- The constant term. -/
def Term.const {T : Type*} (t : T) : Term D N T := ⟨fun _ => t, ∅, dependsOn_const t⟩

namespace Term

variable {T T' T'' : Type*}

/-- Apply a function to the value of a term. -/
def map (g : T → T') (f : Term D N T) : Term D N T' :=
  ⟨fun ρ => g (f.1 ρ), f.2.imp fun _ h ρ ρ' hρ => congrArg g (h ρ ρ' hρ)⟩

/-- Combine the values of two terms. -/
def map₂ (g : T → T' → T'') (f : Term D N T) (f' : Term D N T') : Term D N T'' :=
  ⟨fun ρ => g (f.1 ρ) (f'.1 ρ), by
    obtain ⟨S, h⟩ := f.2
    obtain ⟨S', h'⟩ := f'.2
    exact ⟨S ∪ S', fun ρ ρ' hρ => congrArg₂ g (h ρ ρ' fun x hx => hρ x (Finset.mem_union_left _ hx))
      (h' ρ ρ' fun x hx => hρ x (Finset.mem_union_right _ hx))⟩⟩

/-- Bind the name `x`: `g` receives the value of the term as a function of the
value of `x`. Quantifiers and class abstraction are binders. -/
def bind (x : N) (g : (D → T) → T') (f : Term D N T) : Term D N T' :=
  ⟨fun ρ => g fun m => f.1 (update ρ x m), by
    obtain ⟨S, h⟩ := f.2
    refine ⟨S.erase x, fun ρ ρ' hρ => congrArg g (funext fun m => h _ _ fun y hy => ?_)⟩
    by_cases hyx : y = x
    · subst hyx
      simp
    · rw [update_of_ne hyx, update_of_ne hyx]
      exact hρ y (Finset.mem_erase.2 ⟨hyx, hy⟩)⟩

/-- A function of the value of the name `x`. -/
def name (x : N) (g : D → T) : Term D N T :=
  ⟨fun ρ => g (ρ x), {x}, fun _ _ hρ => congrArg g (hρ x (Finset.mem_singleton_self x))⟩

theorem notFree_map {y : N} {g : T → T'} {f : Term D N T} (h : NotFree y f.1) :
    NotFree y (map g f).1 :=
  fun ρ m => congrArg g (h ρ m)

theorem notFree_map₂ {y : N} {g : T → T' → T''} {f : Term D N T} {f' : Term D N T'}
    (h : NotFree y f.1) (h' : NotFree y f'.1) : NotFree y (map₂ g f f').1 :=
  fun ρ m => congrArg₂ g (h ρ m) (h' ρ m)

theorem notFree_bind_self {x : N} {g : (D → T) → T'} {f : Term D N T} :
    NotFree x (bind x g f).1 :=
  fun ρ m => by simp only [bind, update_idem]

theorem notFree_bind {x y : N} (hxy : y ≠ x) {g : (D → T) → T'} {f : Term D N T}
    (h : NotFree y f.1) : NotFree y (bind x g f).1 :=
  fun ρ m => congrArg g (funext fun m' => by rw [update_comm hxy, h])

theorem notFree_name {x y : N} (hxy : y ≠ x) {g : D → T} : NotFree y (name (D := D) x g).1 :=
  fun ρ m => congrArg g (update_of_ne (Ne.symm hxy) m ρ)

end Term
/-- The kind of a syntax sort in an environment model. -/
inductive Kind : Type (w + 1)
  /-- Values are names. -/
  | name
  /-- Values are finitely supported formulas `Env D N → Prop`. -/
  | formula
  /-- Values are finitely supported functions of environments into `T`. -/
  | term (T : Type w) (default : T)

namespace Kind

variable (D N) in
/-- The values of a kind. -/
abbrev Carrier : Kind.{w} → Type w
  | .name => N
  | .formula => Term D N Prop
  | .term T _ => Term D N T

variable (D N) in
/-- The name a value is, if it is a name. -/
def nameOf : (k : Kind.{w}) → k.Carrier D N → Option N
  | .name, x => some x
  | .formula, _ => none
  | .term _ _, _ => none

variable (D N) in
/-- The value ignores the name `x`: it is not free in it. Names ignore every
name. -/
def Ignores : (k : Kind.{w}) → k.Carrier D N → N → Prop
  | .name, _, _ => True
  | .formula, φ, x => NotFree x φ.1
  | .term _ _, f, x => NotFree x f.1

variable (D N) in
/-- Freshness: names of the two values are distinct, and each value ignores
the name of the other. -/
def Fresh (k k' : Kind.{w}) (a : k.Carrier D N) (b : k'.Carrier D N) : Prop :=
  (∀ x ∈ nameOf D N k a, ∀ y ∈ nameOf D N k' b, x ≠ y) ∧
    (∀ x ∈ nameOf D N k a, Ignores D N k' b x) ∧ ∀ y ∈ nameOf D N k' b, Ignores D N k a y

omit [DecidableEq N] in
@[simp] theorem nameOf_name (x : N) : nameOf D N .name x = some x := rfl

omit [DecidableEq N] in
@[simp] theorem nameOf_formula (φ : Term D N Prop) : nameOf D N .formula φ = none := rfl

omit [DecidableEq N] in
@[simp] theorem nameOf_term {T : Type w} {d : T} (f : Term D N T) :
    nameOf D N (.term T d) f = none := rfl

@[simp] theorem ignores_name (x y : N) : Ignores D N .name x y := trivial

@[simp] theorem ignores_formula (φ : Term D N Prop) (x : N) :
    Ignores D N .formula φ x ↔ NotFree x φ.1 := Iff.rfl

@[simp] theorem ignores_term {T : Type w} {d : T} (f : Term D N T) (x : N) :
    Ignores D N (.term T d) f x ↔ NotFree x f.1 := Iff.rfl

theorem fresh_name_name {x y : N} : Fresh D N .name .name x y ↔ x ≠ y := by
  simp [Fresh]

theorem fresh_name_formula {x : N} {φ : Term D N Prop} :
    Fresh D N .name .formula x φ ↔ NotFree x φ.1 := by
  simp [Fresh]

theorem fresh_formula_name {x : N} {φ : Term D N Prop} :
    Fresh D N .formula .name φ x ↔ NotFree x φ.1 := by
  simp [Fresh]

theorem fresh_name_term {T : Type w} {d : T} {x : N} {f : Term D N T} :
    Fresh D N .name (.term T d) x f ↔ NotFree x f.1 := by
  simp [Fresh]

theorem fresh_term_name {T : Type w} {d : T} {x : N} {f : Term D N T} :
    Fresh D N (.term T d) .name f x ↔ NotFree x f.1 := by
  simp [Fresh]

/-- Values that are not names are fresh for each other. -/
theorem fresh_of_nameOf {k k' : Kind.{w}} {a : k.Carrier D N} {b : k'.Carrier D N}
    (ha : nameOf D N k a = none) (hb : nameOf D N k' b = none) : Fresh D N k k' a b := by
  simp [Fresh, ha, hb]

theorem fresh_symm {k k' : Kind.{w}} {a : k.Carrier D N} {b : k'.Carrier D N}
    (h : Fresh D N k k' a b) : Fresh D N k' k b a :=
  ⟨fun y hy x hx => (h.1 x hx y hy).symm, h.2.2, h.2.1⟩

/-- A value that is not a name is fresh for `a` when it ignores the name `a`
may be. -/
theorem fresh_of_ignores {k k' : Kind.{w}} {a : k.Carrier D N} {b : k'.Carrier D N}
    (hb : nameOf D N k' b = none) (h : ∀ x ∈ nameOf D N k a, Ignores D N k' b x) :
    Fresh D N k k' a b :=
  ⟨fun _ _ _ hy => by simp [hb] at hy, h, fun _ hy => by simp [hb] at hy⟩

theorem Fresh.of_name {k k' : Kind.{w}} {a : k.Carrier D N} {b : k'.Carrier D N}
    (h : Fresh D N k k' a b) {x : N} (hx : x ∈ nameOf D N k a) :
    (∀ y ∈ nameOf D N k' b, x ≠ y) ∧ Ignores D N k' b x :=
  ⟨h.1 x hx, h.2.1 x hx⟩

/-- The finitely many names a value involves. -/
noncomputable def support : (k : Kind.{w}) → k.Carrier D N → Finset N
  | .name, x => {x}
  | .formula, φ => Classical.choose φ.2
  | .term _ _, f => Classical.choose f.2

theorem ignores_of_not_mem_support {x : N} :
    ∀ {k : Kind.{w}} (b : k.Carrier D N), x ∉ support k b → Ignores D N k b x
  | .name, _, _ => trivial
  | .formula, φ, hx => (Classical.choose_spec φ.2).notFree hx
  | .term _ _, f, hx => (Classical.choose_spec f.2).notFree hx

omit [DecidableEq N] in
theorem mem_support_of_nameOf {y : N} :
    ∀ {k : Kind.{w}} (b : k.Carrier D N), y ∈ nameOf D N k b → y ∈ support k b
  | .name, x, h => (Option.some.inj h : x = y) ▸ Finset.mem_singleton_self _
  | .formula, _, h => absurd (Eq.symm h) (Option.some_ne_none y)
  | .term _ _, _, h => absurd (Eq.symm h) (Option.some_ne_none y)

/-- Every kind has a value fresh for finitely many given values. -/
theorem exists_fresh [Infinite N] (k : Kind.{w}) (W : List (Σ k' : Kind.{w}, k'.Carrier D N)) :
    ∃ a : k.Carrier D N, ∀ w ∈ W, Fresh D N k w.1 a w.2 := by
  have hconst : ∀ {k : Kind.{w}} (a : k.Carrier D N), nameOf D N k a = none →
      (∀ y, Ignores D N k a y) → ∀ w ∈ W, Fresh D N k w.1 a w.2 := by
    intro k a ha hi w _
    exact ⟨by simp [ha], by simp [ha], fun y _ => hi y⟩
  cases k with
  | name =>
    classical
    let F : Finset N := (W.map fun w => support w.1 w.2).foldr (· ∪ ·) ∅
    have hF : ∀ w ∈ W, support w.1 w.2 ⊆ F := by
      intro w hw
      have : ∀ (l : List (Finset N)) (S : Finset N), S ∈ l → S ⊆ l.foldr (· ∪ ·) ∅ := by
        intro l S hS
        induction l with
        | nil => simp at hS
        | cons T l ih =>
          rcases List.mem_cons.1 hS with rfl | hS
          · exact Finset.subset_union_left
          · exact (ih hS).trans Finset.subset_union_right
      exact this _ _ (List.mem_map_of_mem hw)
    obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset F
    refine ⟨x, fun w hw => ⟨?_, ?_, fun _ _ => trivial⟩⟩
    · intro x' hx' y hy
      simp only [nameOf_name, Option.mem_def, Option.some.injEq] at hx'
      subst hx'
      rintro rfl
      exact hx (hF w hw (mem_support_of_nameOf w.2 hy))
    · intro x' hx'
      simp only [nameOf_name, Option.mem_def, Option.some.injEq] at hx'
      subst hx'
      exact ignores_of_not_mem_support w.2 fun h => hx (hF w hw h)
  | formula => exact ⟨Term.const True, hconst _ rfl fun _ _ _ => rfl⟩
  | term T d => exact ⟨Term.const d, hconst _ rfl fun _ _ _ => rfl⟩

end Kind

end Env

open Env

/-- An environment model of a grammar over the objects `D` and the names `N`:
a kind for each sort, an interpretation of each syntax rule that is
compositional for freshness, and a truth predicate. -/
structure EnvModel {C V L : Type u} (G : Grammar L C V) (D N : Type w) [DecidableEq N] where
  kind : C → Kind.{w}
  op : ∀ {s : C} (o : G.signature.Op s),
    ((j : Fin (G.signature.arity o)) → (kind (G.signature.argSort o j)).Carrier D N) →
      (kind s).Carrier D N
  fresh_op : ∀ {s t : C} (a : (kind s).Carrier D N) (o : G.signature.Op t)
    (args : (j : Fin (G.signature.arity o)) → (kind (G.signature.argSort o j)).Carrier D N),
    (∀ j, Kind.Fresh D N (kind s) _ a (args j)) → Kind.Fresh D N (kind s) (kind t) a (op o args)
  IsTrue : ∀ {c s : C}, G.prov c = some s → (kind s).Carrier D N → Prop

namespace EnvModel

variable {C V L : Type u} {G : Grammar L C V} {D N : Type w} [DecidableEq N]

/-- An environment model is a model of the grammar. -/
abbrev toModel [Infinite N] (M : EnvModel G D N) : Model.{u, w} G where
  Carrier s := (M.kind s).Carrier D N
  op := M.op
  Fresh {s t} a b := Kind.Fresh D N (M.kind s) (M.kind t) a b
  fresh_symm := Kind.fresh_symm
  fresh_op := M.fresh_op
  exists_fresh s _ W := (Kind.exists_fresh (M.kind s) (W.map fun w => ⟨M.kind w.1, w.2⟩)).imp
    fun _ h _ hw => h _ (List.mem_map_of_mem hw)
  IsTrue := M.IsTrue

end EnvModel

end Silmaril.Logic.Metamath
