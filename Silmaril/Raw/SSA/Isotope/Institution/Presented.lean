module

public import Silmaril.Logic.Institution.Theory
public import Silmaril.Raw.SSA.Isotope.Logic.Metatheory.Theory.ModelReindex

@[expose] public section

/-!
# The institution of presented operation syntax

The Isotope model theory (`Silmaril.Logic.Metatheory.TheoryModel`) works with a many-sorted
operation signature together with a chosen *initial* algebra: the free syntax of a calculus,
whose elements are terms with their (data-valued) typing derivations. This file packages that
setting as an institution in the sense of `Silmaril.Logic.Institution`:

* signatures are `PresSig`: a signature with a chosen initial algebra; signature morphisms are
  the existing `TheoryModel.Signature.Hom` (operation translations preserving argument lists);
* sentences over `X` are equations `⟨i, a, b⟩` between two syntax elements at a common sort;
* models over `X` are all operation algebras of `X.Sig`, with all homomorphisms;
* `M ⊨ ⟨i, a, b⟩` iff the unique fold of the syntax into `M` identifies `a` and `b`;
* sentence translation along `f` is the unique fold `X.Syn ⟶ f*(Y.Syn)` (`translate`), and model
  reduction is the existing `TheoryModel.Algebra.reduct f`.

The satisfaction condition is the existing lemma `TheoryModel.reindex_fold_map` (evaluation in a
reduct is evaluation of the translated syntax).

The theories of this institution at `X` are exactly the existing congruences on `X.Syn`
(`closedOrderIso`): the sentences of a congruence are closed (completeness of the quotient
model, `TheoryModel.semantic_iff`), and every closed set of equations is a congruence. The
existing category `TheoryModel.Models hA E` is equivalent to the institution's category of models
of the corresponding theory (`modelsEquivalence`).
-/

namespace Silmaril.Isotope.Institution

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution
open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory
open Silmaril.Logic.Metatheory.TheoryModel (reindex_fold_map)
open Silmaril.Logic.Metatheory.TheoryModel (semantic_iff)

universe a b c

/-- A presented syntax: a many-sorted operation signature with a chosen initial algebra. -/
structure PresSig where
  /-- The sorts. -/
  Idx : Type a
  /-- The operation signature. -/
  Sig : TheoryModel.Signature.{a, b} Idx
  /-- The free syntax algebra. -/
  Syn : TheoryModel.Algebra.{a, b, c} Sig
  /-- The syntax algebra is initial: every algebra receives a unique fold. -/
  isInitial : IsInitial Syn

namespace PresSig

/-- Presented syntaxes and signature morphisms. Translations of syntax are not part of the
data: they are determined by initiality (`translate`). -/
instance category : Category.{max a b} PresSig.{a, b, c} where
  Hom X Y := TheoryModel.Signature.Hom X.Sig Y.Sig
  id X := TheoryModel.Signature.Hom.id X.Sig
  comp f g := TheoryModel.Signature.Hom.comp g f
  id_comp f := TheoryModel.Signature.Hom.comp_id f
  comp_id f := TheoryModel.Signature.Hom.id_comp f
  assoc f g h := TheoryModel.Signature.Hom.comp_assoc h g f

variable {X Y Z : PresSig.{a, b, c}}

/-- A morphism of presented syntaxes, viewed as a signature morphism. -/
abbrev toHom (f : X ⟶ Y) : TheoryModel.Signature.Hom X.Sig Y.Sig := f

@[simp] theorem toHom_id (X : PresSig.{a, b, c}) : toHom (𝟙 X) = TheoryModel.Signature.Hom.id X.Sig := rfl

@[simp] theorem toHom_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    toHom (f ≫ g) = (toHom g).comp (toHom f) := rfl

/-- The syntax translation along a signature morphism: the unique fold into the reduct of the
target syntax. -/
def translate (f : X ⟶ Y) : X.Syn ⟶ TheoryModel.Algebra.reductObj (toHom f) Y.Syn :=
  X.isInitial.to _

theorem translate_id (X : PresSig.{a, b, c}) : translate (𝟙 X) = 𝟙 X.Syn :=
  X.isInitial.hom_ext _ _

@[simp] theorem translate_id_map (X : PresSig.{a, b, c}) {i : X.Idx} (x : X.Syn.Carrier i) :
    (translate (𝟙 X)).map x = x :=
  congrArg (fun k : X.Syn ⟶ X.Syn => k.map x) (translate_id X)

/-- Translation along a composite is the composite of translations. -/
theorem translate_comp_map (f : X ⟶ Y) (g : Y ⟶ Z) {i : X.Idx} (x : X.Syn.Carrier i) :
    (translate (f ≫ g)).map x = (translate g).map ((translate f).map x) := by
  have h : translate (f ≫ g) ≫ (TheoryModel.Algebra.reductCompIso (toHom g) (toHom f) Z.Syn).hom =
      translate f ≫ TheoryModel.Algebra.reductMap (toHom f) (translate g) :=
    X.isInitial.hom_ext _ _
  exact congrArg (fun k => TheoryModel.Algebra.Hom.map k x) h

/-! ### Sentences, models and satisfaction -/

/-- Sentences: equations between two syntax elements of a common sort. -/
abbrev Equation (X : PresSig.{a, b, c}) : Type (max a c) :=
  Σ i : X.Idx, X.Syn.Carrier i × X.Syn.Carrier i

/-- An algebra satisfies an equation when the unique fold of the syntax identifies its sides. -/
def Holds (X : PresSig.{a, b, c}) (M : TheoryModel.Algebra.{a, b, c} X.Sig) (e : X.Equation) : Prop :=
  (X.isInitial.to M).map e.2.1 = (X.isInitial.to M).map e.2.2

/-- The room of a presented syntax. -/
def room (X : PresSig.{a, b, c}) : Room.{max a c, max a c, max a b (c + 1)} :=
  ⟨X.Equation, Cat.of (TheoryModel.Algebra.{a, b, c} X.Sig), X.Holds⟩

/-- Translate an equation along a signature morphism. -/
def mapEquation (f : X ⟶ Y) (e : X.Equation) : Y.Equation :=
  ⟨(toHom f).sort e.1, (translate f).map e.2.1, (translate f).map e.2.2⟩

/-- The satisfaction condition, from `TheoryModel.reindex_fold_map`. -/
theorem holds_mapEquation_iff (f : X ⟶ Y) (M : TheoryModel.Algebra.{a, b, c} Y.Sig)
    (e : X.Equation) :
    Y.Holds M (mapEquation f e) ↔ X.Holds (TheoryModel.Algebra.reductObj (toHom f) M) e := by
  have h₁ := reindex_fold_map (toHom f) X.isInitial Y.isInitial (translate f) M e.2.1
  have h₂ := reindex_fold_map (toHom f) X.isInitial Y.isInitial (translate f) M e.2.2
  exact ⟨fun h => h₁.trans (h.trans h₂.symm), fun h => h₁.symm.trans (h.trans h₂)⟩

/-- The corridor of a signature morphism: translate equations, reduce algebras. -/
def corridor (f : X ⟶ Y) : X.room ⟶ Y.room :=
  ⟨mapEquation f, TheoryModel.Algebra.reduct (toHom f), fun M e => holds_mapEquation_iff f M e⟩

/-- An identity-on-elements algebra map between equal algebras is `eqToHom`. -/
theorem eq_eqToHom_of_heq {I : Type a} {Sig : TheoryModel.Signature.{a, b} I}
    {M N : TheoryModel.Algebra.{a, b, c} Sig} (h : M = N) (φ : M ⟶ N)
    (hφ : ∀ {i : I} (x : M.Carrier i), HEq (φ.map x) x) : φ = eqToHom h := by
  subst h
  apply TheoryModel.Algebra.Hom.ext
  intro i x
  rw [eqToHom_refl]
  exact eq_of_heq (hφ x)

/-- Reducts compose strictly. The objects agree by `TheoryModel.Algebra.reductObj_comp`; the
comparison is the existing identity-on-carriers isomorphism `TheoryModel.Algebra.reductComp`. -/
theorem reduct_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    TheoryModel.Algebra.reduct (toHom (f ≫ g)) =
      TheoryModel.Algebra.reduct (toHom g) ⋙ TheoryModel.Algebra.reduct (toHom f) :=
  Functor.ext_of_iso (TheoryModel.Algebra.reductComp (toHom g) (toHom f))
    (fun M => TheoryModel.Algebra.reductObj_comp (toHom g) (toHom f) M)
    (fun _ => eq_eqToHom_of_heq _ _ fun _ => HEq.rfl)

/-- The institution of presented operation syntax, as a functor into rooms. -/
def inst : PresSig.{a, b, c} ⥤ Room.{max a c, max a c, max a b (c + 1)} where
  obj := room
  map := corridor
  map_id X := Room.hom_ext (funext fun e => by
      obtain ⟨i, x, y⟩ := e
      change (⟨i, (translate (𝟙 X)).map x, (translate (𝟙 X)).map y⟩ : X.Equation) = ⟨i, x, y⟩
      rw [translate_id_map, translate_id_map]) rfl
  map_comp {X Y Z} f g := Room.hom_ext (funext fun e => by
      obtain ⟨i, x, y⟩ := e
      change (⟨_, (translate (f ≫ g)).map x, (translate (f ≫ g)).map y⟩ : Z.Equation) =
        (⟨_, (translate g).map ((translate f).map x),
          (translate g).map ((translate f).map y)⟩ : Z.Equation)
      rw [translate_comp_map, translate_comp_map]
      rfl) (reduct_comp f g)

@[simp] theorem inst_obj_sat (X : PresSig.{a, b, c}) (M : TheoryModel.Algebra.{a, b, c} X.Sig)
    (e : X.Equation) : (inst.obj X).Sat M e ↔ X.Holds M e := Iff.rfl

@[simp] theorem inst_map_sen (f : X ⟶ Y) (e : X.Equation) :
    (inst.map f).sen e = mapEquation f e := rfl

@[simp] theorem inst_map_mod_obj (f : X ⟶ Y) (M : TheoryModel.Algebra.{a, b, c} Y.Sig) :
    (inst.map f).mod.obj M = TheoryModel.Algebra.reductObj (toHom f) M := rfl

/-! ### Theories are congruences -/

/-- The equations of a congruence, as a set of sentences. -/
def equations (E : TheoryModel.Congruence X.Syn) : Set X.Equation := {e | E.Rel e.2.1 e.2.2}

theorem mem_modelsOf_equations_iff (E : TheoryModel.Congruence X.Syn) (M : TheoryModel.Algebra.{a, b, c} X.Sig) :
    M ∈ (inst.obj X).modelsOf (equations E) ↔
      ∀ {i : X.Idx} {x y : X.Syn.Carrier i}, E.Rel x y →
        (X.isInitial.to M).map x = (X.isInitial.to M).map y :=
  ⟨fun h _ x y hxy => h ⟨_, x, y⟩ hxy, fun h _ he => h he⟩

/-- Algebras satisfying the equations of `E` are the existing `TheoryModel.Models`. -/
def modelOfMem (E : TheoryModel.Congruence X.Syn) (M : TheoryModel.Algebra.{a, b, c} X.Sig)
    (hM : M ∈ (inst.obj X).modelsOf (equations E)) : TheoryModel.Models X.isInitial E :=
  ⟨M, fun h => (mem_modelsOf_equations_iff E M).1 hM h⟩

/-- Semantic consequence from a congruence is membership in it: this is the institution form of
completeness of the quotient model, `TheoryModel.semantic_iff`. -/
theorem entails_equations_iff (E : TheoryModel.Congruence X.Syn) (e : X.Equation) :
    (inst.obj X).Entails (equations E) e ↔ E.Rel e.2.1 e.2.2 := by
  rw [semantic_iff X.isInitial E e.2.1 e.2.2]
  constructor
  · intro h M
    exact h M.algebra ((mem_modelsOf_equations_iff E M.algebra).2 M.sound)
  · intro h M hM
    exact h (modelOfMem E M hM)

/-- The equations of a congruence form a closed set of sentences. -/
theorem isClosed_equations (E : TheoryModel.Congruence X.Syn) : (inst.obj X).IsClosed (equations E) := by
  ext e
  exact entails_equations_iff E e

/-- A closed set of equations is a congruence. -/
def congruenceOfClosed (Γ : Set X.Equation) (hΓ : (inst.obj X).IsClosed Γ) :
    TheoryModel.Congruence X.Syn where
  Rel x y := (⟨_, x, y⟩ : X.Equation) ∈ Γ
  equivalence i := by
    refine ⟨fun x => ?_, fun {x y} h => ?_, fun {x y z} h k => ?_⟩
    · rw [← hΓ]
      exact fun _ _ => rfl
    · rw [← hΓ] at h ⊢
      exact fun M hM => (h M hM).symm
    · rw [← hΓ] at h k ⊢
      exact fun M hM => (h M hM).trans (k M hM)
  compatible o x y h := by
    have h' : ∀ j, (⟨_, x j, y j⟩ : X.Equation) ∈ (inst.obj X).closure Γ := fun j => by
      rw [hΓ]
      exact h j
    rw [← hΓ]
    intro M hM
    change (X.isInitial.to M).map (X.Syn.op o x) = (X.isInitial.to M).map (X.Syn.op o y)
    rw [(X.isInitial.to M).comm, (X.isInitial.to M).comm]
    exact congrArg (M.op o) (funext fun j => h' j M hM)

/-- Congruences on the syntax are exactly the theories (closed sentence sets) at `X`. -/
def closedOrderIso (X : PresSig.{a, b, c}) :
    TheoryModel.Congruence X.Syn ≃o {Γ : Set X.Equation // (inst.obj X).IsClosed Γ} where
  toFun E := ⟨equations E, isClosed_equations E⟩
  invFun Γ := congruenceOfClosed Γ.1 Γ.2
  left_inv _ := TheoryModel.Congruence.ext fun _ _ => Iff.rfl
  right_inv _ := Subtype.ext (Set.ext fun _ => Iff.rfl)
  map_rel_iff' {E _} :=
    ⟨fun h _ _ _ hxy => h (show (⟨_, _, _⟩ : X.Equation) ∈ equations E from hxy),
      fun h _ he => h he⟩

/-! ### Theories in an institution built from presented syntax -/

section Theories

variable {C : Type*} [Category C] (F : C ⥤ PresSig.{a, b, c})

/-- The theory of a congruence on the syntax at `F.obj P`, in the institution `F ⋙ inst`. -/
def theoryAt (P : C) (E : TheoryModel.Congruence (F.obj P).Syn) : Silmaril.Logic.Institution.Theory (F ⋙ inst) :=
  ⟨⟨P, equations E⟩, isClosed_equations E⟩

/-- A signature morphism whose translation is sound for two congruences is a theory morphism. -/
def theoryAtHom {P Q : C} (g : P ⟶ Q) {E : TheoryModel.Congruence (F.obj P).Syn}
    {E' : TheoryModel.Congruence (F.obj Q).Syn}
    (sound : ∀ {i} {x y : (F.obj P).Syn.Carrier i}, E.Rel x y →
      E'.Rel ((translate (F.map g)).map x) ((translate (F.map g)).map y)) :
    theoryAt F P E ⟶ theoryAt F Q E' :=
  Silmaril.Logic.Institution.Theory.homMk g fun _ he => sound he

/-- The existing models of a congruence are the institution's models of its theory. -/
def modelsEquivalence (P : C) (E : TheoryModel.Congruence (F.obj P).Syn) :
    TheoryModel.Models (F.obj P).isInitial E ≌ Silmaril.Logic.Institution.Theory.Models (theoryAt F P E) where
  functor :=
    { obj M := ⟨M.algebra, fun _ he => M.sound he⟩
      map f := ObjectProperty.homMk f }
  inverse :=
    { obj N := ⟨N.obj, fun h => N.property ⟨_, _, _⟩ h⟩
      map f := f.hom }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- Restriction of existing models along a sound translation (`TheoryModel.Models.reindex`)
is the reduct of the institution along the corresponding theory morphism. -/
theorem modelsEquivalence_reindex {P Q : C} (g : P ⟶ Q) {E : TheoryModel.Congruence (F.obj P).Syn}
    {E' : TheoryModel.Congruence (F.obj Q).Syn}
    (sound : ∀ {i} {x y : (F.obj P).Syn.Carrier i}, E.Rel x y →
      E'.Rel ((translate (F.map g)).map x) ((translate (F.map g)).map y))
    (M : TheoryModel.Models (F.obj Q).isInitial E') :
    ((modelsEquivalence F P E).functor.obj
        ((TheoryModel.Models.reindex (toHom (F.map g)) (F.obj P).isInitial (F.obj Q).isInitial
          (translate (F.map g)) sound).obj M)).obj =
      ((Silmaril.Logic.Institution.Theory.reduct (theoryAtHom F g sound)).obj ((modelsEquivalence F Q E').functor.obj M)).obj :=
  rfl

end Theories

end PresSig

end Silmaril.Isotope.Institution
