module

public import Silmaril.Semantics.RuntimeWires.Computations.Defs

public section

/-! Internal bookkeeping for morphisms whose boundary words agree by tensor laws. -/

namespace Silmaril.RuntimeWires.Proofs

open CategoryTheory
open scoped MonoidalCategory

universe u v

section
variable {C : Type u} [Category.{v} C]

/-- Equality of arrows including equality of both boundaries. -/
structure SameArrow {A B A' B' : C} (f : A ⟶ B) (g : A' ⟶ B') : Prop where
  source : A = A'
  target : B = B'
  arrow : HEq f g

namespace SameArrow

scoped infix:50 " ≈ₐ " => SameArrow

variable {A B D A' B' D' A'' B'' : C}
variable {f : A ⟶ B} {g : A' ⟶ B'} {h : A'' ⟶ B''}

theorem refl (f : A ⟶ B) : f ≈ₐ f := ⟨rfl, rfl, HEq.rfl⟩

theorem symm (e : f ≈ₐ g) : g ≈ₐ f := ⟨e.source.symm, e.target.symm, e.arrow.symm⟩

theorem trans (e : f ≈ₐ g) (d : g ≈ₐ h) : f ≈ₐ h :=
  ⟨e.source.trans d.source, e.target.trans d.target, e.arrow.trans d.arrow⟩

instance : Trans (@SameArrow C _ A B A' B') (@SameArrow C _ A' B' A'' B'')
    (@SameArrow C _ A B A'' B'') where
  trans := trans

theorem of_eq {f g : A ⟶ B} (e : f = g) : f ≈ₐ g := e ▸ refl f

theorem eq {f g : A ⟶ B} (e : f ≈ₐ g) : f = g := eq_of_heq e.arrow

theorem square (e : f ≈ₐ g) (p : A = A') (q : B = B') :
    f ≫ eqToHom q = eqToHom p ≫ g := by
  subst p
  subst q
  simp [e.eq]

theorem id (p : A = A') : 𝟙 A ≈ₐ 𝟙 A' := by
  subst p
  exact refl _

theorem eqToHom_id (p : A = B) : eqToHom p ≈ₐ 𝟙 A := by
  subst p
  exact refl _

theorem comp {k : B ⟶ D} {l : B' ⟶ D'} (e : f ≈ₐ g) (d : k ≈ₐ l) :
    f ≫ k ≈ₐ g ≫ l := by
  obtain ⟨rfl, rfl, ef⟩ := e
  obtain ⟨_, rfl, ek⟩ := d
  cases eq_of_heq ef
  cases eq_of_heq ek
  exact refl _

theorem cast_comp {X : C} (p : X = A) : eqToHom p ≫ f ≈ₐ f := by
  subst p
  simp [refl]

theorem comp_cast {X : C} (p : B = X) : f ≫ eqToHom p ≈ₐ f := by
  subst p
  simp [refl]

/-- Compose through an equality of the middle boundaries. -/
@[expose] def join {X : C} (f : A ⟶ B) (g : X ⟶ D) (p : B = X) : A ⟶ D :=
  f ≫ eqToHom p ≫ g

theorem join_eq {k : B ⟶ D} (p : B = B) : join f k p = f ≫ k := by
  simp [join]

theorem comp_join {X : C} {k : B ⟶ D} {l : X ⟶ D'} (e : f ≈ₐ g) (d : k ≈ₐ l) (p : B' = X) :
    f ≫ k ≈ₐ join g l p := by
  obtain ⟨rfl, rfl, ef⟩ := e
  obtain ⟨rfl, rfl, ek⟩ := d
  simp [join_eq, eq_of_heq ef, eq_of_heq ek, refl]

theorem join_congr {X X' : C} {k : X ⟶ D} {l : X' ⟶ D'}
    (e : f ≈ₐ g) (d : k ≈ₐ l) (p : B = X) (q : B' = X') :
    join f k p ≈ₐ join g l q := by
  subst p
  simpa only [join_eq] using e.comp_join d q

theorem join_assoc {X Y Z W : C} (f : A ⟶ B) (g : X ⟶ Y) (h : Z ⟶ W)
    (p : B = X) (q : Y = Z) : join (join f g p) h q = join f (join g h q) p := by
  simp [join, Category.assoc]

theorem join_id {X : C} (p : B = X) :
    join f (𝟙 X) p ≈ₐ f := by
  subst p
  simp [join, refl]

theorem id_join {X : C} {k : X ⟶ D} (p : A = X) :
    join (𝟙 A) k p ≈ₐ k := by
  subst p
  simp [join, refl]

theorem join_map {D : Type*} [Category* D] (F : C ⥤ D) {X : C}
    (f : A ⟶ B) (k : X ⟶ B') (p : B = X) :
    F.map (join f k p) = join (F.map f) (F.map k) (congrArg F.obj p) := by
  cases p
  simp [join]

theorem inv {i : A ≅ B} {j : A' ≅ B'} (e : i.hom ≈ₐ j.hom) : i.inv ≈ₐ j.inv := by
  obtain ⟨rfl, rfl, e⟩ := e
  cases Iso.ext (eq_of_heq e)
  exact refl _

section
variable [MonoidalCategoryStruct C]

theorem tensor {X Y X' Y' : C} {k : X ⟶ Y} {l : X' ⟶ Y'}
    (e : f ≈ₐ g) (d : k ≈ₐ l) : f ⊗ₘ k ≈ₐ g ⊗ₘ l := by
  obtain ⟨rfl, rfl, ef⟩ := e
  obtain ⟨rfl, rfl, ek⟩ := d
  cases eq_of_heq ef
  cases eq_of_heq ek
  exact refl _

theorem whiskerLeft (e : f ≈ₐ g) {X X' : C} (p : X = X') : X ◁ f ≈ₐ X' ◁ g := by
  subst p
  obtain ⟨rfl, rfl, ef⟩ := e
  cases eq_of_heq ef
  exact refl _

theorem whiskerRight (e : f ≈ₐ g) {X X' : C} (p : X = X') : f ▷ X ≈ₐ g ▷ X' := by
  subst p
  obtain ⟨rfl, rfl, ef⟩ := e
  cases eq_of_heq ef
  exact refl _

end

variable [MonoidalCategory C]

theorem join_whiskerRight {X : C} (f : A ⟶ B) (k : X ⟶ D) (p : B = X) (Y : C) :
    (join f k p) ▷ Y = join (f ▷ Y) (k ▷ Y) (congrArg (· ⊗ Y) p) :=
  join_map (MonoidalCategory.tensorRight Y) f k p

theorem whiskerLeft_join {X : C} (Y : C) (f : A ⟶ B) (k : X ⟶ D) (p : B = X) :
    Y ◁ (join f k p) = join (Y ◁ f) (Y ◁ k) (congrArg (Y ⊗ ·) p) :=
  join_map (MonoidalCategory.tensorLeft Y) f k p

end SameArrow
end

namespace RuntimeCoherence

open Presentation
open Diagram.Presented
open scoped SameArrow

variable {G : EffectfulPolygraph.{u,v}}
local notation "V" => valueWord (G := G)
local notation "R" => runtime G

theorem word_ext {X Y : Runtime G} (h : X.word = Y.word) : X = Y := by
  cases X
  cases Y
  cases h
  rfl

theorem tensor_word (X Y : Runtime G) : (X ⊗ Y).word = X.word ++ Y.word := rfl
theorem empty_word : (𝟙_ (Runtime G)).word = [] := rfl
theorem value_word (A : List G.Obj) : (V A).word = A.map some := rfl
theorem boundary_word (A : Computations G) : A.boundary.word = none :: A.word.map some := rfl
theorem concat_word (A B : Computations G) : (A.concat B).word = A.word ++ B.word := rfl
theorem runtime_word' : (R : Runtime G).word = [none] := rfl

scoped macro "runtime_word" : tactic =>
  `(tactic| (first | rfl | apply word_ext <;>
    simp only [tensor_word, empty_word, value_word, runtime_word', boundary_word, concat_word,
      List.map_append,
      List.map_nil, List.map_cons, List.append_assoc, List.cons_append, List.nil_append,
      List.append_nil] <;> rfl))

scoped macro:80 f:term:81 " ≫ₐ " g:term:80 : term =>
  `(SameArrow.join $f $g (by runtime_word))

theorem word_append (A B : List G.Obj) : V (A ++ B) = V A ⊗ V B :=
  congrArg Diagram.Presented.mk (List.map_append ..)

theorem assoc_hom_eq (X Y Z : Runtime G) :
    (α_ X Y Z).hom = eqToHom (concat_assoc X Y Z) := rfl

theorem assoc_inv_eq (X Y Z : Runtime G) :
    (α_ X Y Z).inv = eqToHom (concat_assoc X Y Z).symm := rfl

theorem assoc_hom (X Y Z : Runtime G) : (α_ X Y Z).hom ≈ₐ 𝟙 ((X ⊗ Y) ⊗ Z) :=
  SameArrow.eqToHom_id (concat_assoc X Y Z)

theorem assoc_inv (X Y Z : Runtime G) : (α_ X Y Z).inv ≈ₐ 𝟙 (X ⊗ (Y ⊗ Z)) :=
  SameArrow.eqToHom_id (concat_assoc X Y Z).symm

theorem left_hom (X : Runtime G) : (λ_ X).hom ≈ₐ 𝟙 (𝟙_ (Runtime G) ⊗ X) :=
  SameArrow.eqToHom_id (empty_concat X)

theorem left_inv (X : Runtime G) : (λ_ X).inv ≈ₐ 𝟙 X :=
  SameArrow.eqToHom_id (empty_concat X).symm

theorem right_hom (X : Runtime G) : (ρ_ X).hom ≈ₐ 𝟙 (X ⊗ 𝟙_ (Runtime G)) :=
  SameArrow.eqToHom_id (concat_empty X)

theorem right_inv (X : Runtime G) : (ρ_ X).inv ≈ₐ 𝟙 X :=
  SameArrow.eqToHom_id (concat_empty X).symm

theorem whiskerLeft_unit {X Y : Runtime G} (f : X ⟶ Y) :
    (𝟙_ (Runtime G)) ◁ f ≈ₐ f := by
  calc
    _ ≈ₐ (𝟙_ (Runtime G)) ◁ f ≫ (λ_ Y).hom := by
      simpa using (SameArrow.refl ((𝟙_ (Runtime G)) ◁ f)).comp (left_hom Y).symm
    _ ≈ₐ (λ_ X).hom ≫ f := .of_eq (MonoidalCategory.leftUnitor_naturality f)
    _ ≈ₐ f := by
      simpa using ((left_hom X).trans (.id (empty_concat X))).comp (.refl f)

theorem whiskerRight_unit {X Y : Runtime G} (f : X ⟶ Y) :
    f ▷ (𝟙_ (Runtime G)) ≈ₐ f := by
  calc
    _ ≈ₐ f ▷ (𝟙_ (Runtime G)) ≫ (ρ_ Y).hom := by
      simpa using (SameArrow.refl (f ▷ (𝟙_ (Runtime G)))).comp (right_hom Y).symm
    _ ≈ₐ (ρ_ X).hom ≫ f := .of_eq (MonoidalCategory.rightUnitor_naturality f)
    _ ≈ₐ f := by
      simpa using ((right_hom X).trans (.id (concat_empty X))).comp (.refl f)

theorem whisker_right_right {X Y : Runtime G} (f : X ⟶ Y) (Z W : Runtime G) :
    (f ▷ Z) ▷ W ≈ₐ f ▷ (Z ⊗ W) := by
  calc
    _ ≈ₐ ((f ▷ Z) ▷ W) ≫ (α_ Y Z W).hom := by
      simpa using (SameArrow.refl ((f ▷ Z) ▷ W)).comp (assoc_hom Y Z W).symm
    _ ≈ₐ (α_ X Z W).hom ≫ f ▷ (Z ⊗ W) :=
      .of_eq (MonoidalCategory.associator_naturality_left f Z W)
    _ ≈ₐ f ▷ (Z ⊗ W) := by
      simpa using
        ((assoc_hom X Z W).trans (.id (concat_assoc X Z W))).comp (.refl (f ▷ (Z ⊗ W)))

theorem whisker_left_right (X : Runtime G) {Y Z : Runtime G} (f : Y ⟶ Z) (W : Runtime G) :
    (X ◁ f) ▷ W ≈ₐ X ◁ (f ▷ W) := by
  calc
    _ ≈ₐ ((X ◁ f) ▷ W) ≫ (α_ X Z W).hom := by
      simpa using (SameArrow.refl ((X ◁ f) ▷ W)).comp (assoc_hom X Z W).symm
    _ ≈ₐ (α_ X Y W).hom ≫ X ◁ (f ▷ W) :=
      .of_eq (MonoidalCategory.associator_naturality_middle X f W)
    _ ≈ₐ X ◁ (f ▷ W) := by
      simpa using
        ((assoc_hom X Y W).trans (.id (concat_assoc X Y W))).comp (.refl (X ◁ (f ▷ W)))

theorem whisker_left_left (X Y : Runtime G) {Z W : Runtime G} (f : Z ⟶ W) :
    (X ⊗ Y) ◁ f ≈ₐ X ◁ (Y ◁ f) := by
  calc
    _ ≈ₐ ((X ⊗ Y) ◁ f) ≫ (α_ X Y W).hom := by
      simpa using (SameArrow.refl ((X ⊗ Y) ◁ f)).comp (assoc_hom X Y W).symm
    _ ≈ₐ (α_ X Y Z).hom ≫ X ◁ (Y ◁ f) :=
      .of_eq (MonoidalCategory.associator_naturality_right X Y f)
    _ ≈ₐ X ◁ (Y ◁ f) := by
      simpa using
        ((assoc_hom X Y Z).trans (.id (concat_assoc X Y Z))).comp (.refl (X ◁ (Y ◁ f)))

end RuntimeCoherence
end Silmaril.RuntimeWires.Proofs
