module

public import Silmaril.Logic.Metamath.Category.Rewrite
public import Mathlib.CategoryTheory.Category.Basic

@[expose] public section

/-!
# The category of grammatical axiom sets

An object `X : GAxSet` bundles types of rule labels, constants and variables
(`X.L`, `X.C`, `X.V`, all in `Type u`), a grammar `X.G` and a set of
well-formed tree axioms `X.axioms`. Bundling the types puts axiom sets over
different languages into one category, `GAxSet.{u}`, a large category with
morphisms in `Type u`.

A morphism `X ⟶ Y` is a syntax rewrite `Rewrite X.G Y.G` (a typecode map, an
injective variable renaming and a template for every syntax rule) that sends
every well-formed tree theorem of `X` to a tree theorem of `Y`. Theorem
preservation makes composition hold without assumptions. When `Y` has
infinitely many variables it is equivalent to sending every axiom of `X` to a
theorem of `Y` (`GAxSet.Hom.map_derivable_iff`, by tree cut admissibility),
and `GAxSet.Hom.ofAxioms` builds morphisms from that criterion.
`GAxSet.Hom.ofImage` needs no cut: the rewrite sends axioms to axioms.

Morphisms are equal when their typecode maps, renamings and templates agree
(`GAxSet.hom_ext`); the theorem-preservation condition is a proposition.
-/

namespace Silmaril.Logic.Metamath

open CategoryTheory Grammar

universe u

/-- A grammatical axiom set: a grammar and a set of well-formed tree axioms
over it, together with its types of rule labels, constants and variables. -/
structure GAxSet : Type (u + 1) where
  /-- Rule labels. -/
  L : Type u
  /-- Constants, including typecodes. -/
  C : Type u
  /-- Variables. -/
  V : Type u
  [decEq : DecidableEq V]
  /-- The grammar. -/
  G : Grammar L C V
  /-- The logical axioms. -/
  axioms : Set (TAssertion L C V)
  wf : ∀ A ∈ axioms, A.WellFormed G

attribute [instance] GAxSet.decEq

namespace GAxSet

/-- Package a grammar and well-formed axioms. -/
abbrev of {L C V : Type u} [DecidableEq V] (G : Grammar L C V) (Γ : Set (TAssertion L C V))
    (hΓ : ∀ A ∈ Γ, A.WellFormed G) : GAxSet.{u} := ⟨L, C, V, G, Γ, hΓ⟩

/-- A morphism of grammatical axiom sets: a syntax rewrite sending well-formed
tree theorems to tree theorems. -/
structure Hom (X Y : GAxSet.{u}) extends Rewrite X.G Y.G where
  map_derivable : ∀ A, A.WellFormed X.G → TDerivable X.G X.axioms A →
    TDerivable Y.G Y.axioms (toRewrite.assertion A)

namespace Hom

variable {X Y Z : GAxSet.{u}}

theorem ext' {f g : Hom X Y} (h : f.toRewrite = g.toRewrite) : f = g := by
  cases f; cases g; cases h; rfl

/-- The identity morphism. -/
def id (X : GAxSet.{u}) : Hom X X where
  toRewrite := Rewrite.id X.G
  map_derivable A hA h := by rw [Rewrite.id_assertion hA]; exact h

/-- Composition of morphisms. -/
def comp (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  toRewrite := f.toRewrite.comp g.toRewrite
  map_derivable A hA h := by
    rw [Rewrite.comp_assertion _ _ hA]
    exact g.map_derivable _ (f.wellFormed hA) (f.map_derivable A hA h)

end Hom

instance : Category GAxSet.{u} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext' (Rewrite.id_comp f.toRewrite)
  comp_id f := Hom.ext' (Rewrite.comp_id f.toRewrite)
  assoc f g h := Hom.ext' (Rewrite.comp_assoc f.toRewrite g.toRewrite h.toRewrite)

variable {X Y Z : GAxSet.{u}}

/-- Morphisms are determined by their typecode maps, renamings and templates. -/
@[ext]
theorem hom_ext {f g : X ⟶ Y} (htc : f.tc = g.tc) (hvar : f.var = g.var)
    (htmpl : f.tmpl = g.tmpl) : f = g :=
  Hom.ext' (Rewrite.ext htc hvar htmpl)

theorem hom_ext_iff' {f g : X ⟶ Y} : f = g ↔ f.toRewrite = g.toRewrite :=
  ⟨fun h => h ▸ rfl, Hom.ext'⟩

@[simp] theorem id_toRewrite (X : GAxSet.{u}) : (𝟙 X : X ⟶ X).toRewrite = Rewrite.id X.G := rfl

@[simp] theorem comp_toRewrite (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toRewrite = f.toRewrite.comp g.toRewrite := rfl

@[simp] theorem id_tc (X : GAxSet.{u}) (c : X.C) : (𝟙 X : X ⟶ X).tc c = c := rfl

@[simp] theorem id_var (X : GAxSet.{u}) (v : X.V) : (𝟙 X : X ⟶ X).var v = v := rfl

@[simp] theorem comp_tc (f : X ⟶ Y) (g : Y ⟶ Z) (c : X.C) : (f ≫ g).tc c = g.tc (f.tc c) := rfl

@[simp] theorem comp_var (f : X ⟶ Y) (g : Y ⟶ Z) (v : X.V) :
    (f ≫ g).var v = g.var (f.var v) := rfl

theorem comp_tmpl (f : X ⟶ Y) (g : Y ⟶ Z) (l : X.L) :
    (f ≫ g).tmpl l = g.tree (f.tmpl l) := rfl

namespace Hom

/-- A morphism sends every axiom to a theorem. -/
theorem derivable_axiom (f : X ⟶ Y) {A : TAssertion X.L X.C X.V} (hA : A ∈ X.axioms) :
    TDerivable Y.G Y.axioms (f.assertion A) :=
  f.map_derivable A (X.wf A hA) (TDerivable.of_mem hA (X.wf A hA))

/-- A morphism sends every well-formed theorem to a theorem. -/
theorem map_tderivable (f : X ⟶ Y) {A : TAssertion X.L X.C X.V} (hA : A.WellFormed X.G)
    (h : TDerivable X.G X.axioms A) : TDerivable Y.G Y.axioms (f.assertion A) :=
  f.map_derivable A hA h

/-- With infinitely many target variables, preserving theorems is equivalent
to sending each axiom to a theorem. -/
theorem map_derivable_iff [Infinite Y.V] (f : Rewrite X.G Y.G) :
    (∀ A, A.WellFormed X.G → TDerivable X.G X.axioms A →
        TDerivable Y.G Y.axioms (f.assertion A)) ↔
      ∀ A ∈ X.axioms, TDerivable Y.G Y.axioms (f.assertion A) :=
  ⟨fun h A hA => h A (X.wf A hA) (TDerivable.of_mem hA (X.wf A hA)),
    fun h _ hA hd => TDerivable.rewrite_of_derivable f X.wf h hA hd⟩

/-- A rewrite sending each axiom to a theorem, into an axiom set with
infinitely many variables. -/
def ofAxioms [Infinite Y.V] (f : Rewrite X.G Y.G)
    (h : ∀ A ∈ X.axioms, TDerivable Y.G Y.axioms (f.assertion A)) : X ⟶ Y :=
  ⟨f, (map_derivable_iff f).2 h⟩

@[simp] theorem ofAxioms_toRewrite [Infinite Y.V] (f : Rewrite X.G Y.G)
    (h : ∀ A ∈ X.axioms, TDerivable Y.G Y.axioms (f.assertion A)) :
    (ofAxioms f h).toRewrite = f := rfl

/-- A rewrite sending each axiom to an axiom. -/
def ofImage (f : Rewrite X.G Y.G) (h : ∀ A ∈ X.axioms, f.assertion A ∈ Y.axioms) : X ⟶ Y :=
  ⟨f, fun A hA hd => (hd.rewrite f X.wf hA).mono (by rintro _ ⟨B, hB, rfl⟩; exact h B hB)⟩

@[simp] theorem ofImage_toRewrite (f : Rewrite X.G Y.G)
    (h : ∀ A ∈ X.axioms, f.assertion A ∈ Y.axioms) : (ofImage f h).toRewrite = f := rfl

/-- A morphism translates each tree derivation from the axioms of `X` into a
tree derivation from the translated axioms. -/
noncomputable def mapTDerivation (f : X ⟶ Y) {A : TAssertion X.L X.C X.V}
    {e : TExpr X.L X.C X.V} (d : TDerivation X.G X.axioms A e) :
    TDerivation Y.G (f.assertion '' X.axioms) (f.assertion A) (f.texpr e) :=
  d.rewrite f.toRewrite X.wf

end Hom

end GAxSet

end Silmaril.Logic.Metamath
