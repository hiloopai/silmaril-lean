module

public import Silmaril.Semantics.RuntimeWires.EffectfulExtension.Thms
public import Silmaril.Proofs.Semantics.RuntimeWires.Coherence.Whiskering

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.EffectfulUniversal

open CategoryTheory MonoidalCategory Presentation RuntimeCoherence
open scoped MonoidalCategory SameArrow RuntimeCoherence

universe u v

variable {G : EffectfulPolygraph.{u,v}}

local notation "V" => valueWord (G := G)
local notation "σ" => crossingWord (G := G)

/-- Value words on the two sides of a single runtime wire. -/
structure Position (G : EffectfulPolygraph.{u,v}) where
  before : List G.Obj
  after : List G.Obj

namespace Position

def computation (X : Position G) : Computations G := ⟨X.before ++ X.after⟩

def ambient (X : Position G) : Runtime G := V X.before ⊗ (⟨X.after⟩ : Computations G).boundary

def split (X : Position G) : X.computation.boundary ≅ X.ambient :=
  (⟨X.before⟩ : Computations G).splitLeft ⟨X.after⟩

def prepend (A : List G.Obj) (X : Position G) : Position G := ⟨A ++ X.before, X.after⟩

def append (X : Position G) (A : List G.Obj) : Position G := ⟨X.before, X.after ++ A⟩

/-- Read an arrow at the leftmost runtime position by conjugating with its boundary crossings. -/
def normalize {X Y : Position G} (f : X.ambient ⟶ Y.ambient) : X.computation ⟶ Y.computation :=
  show X.computation.boundary ⟶ Y.computation.boundary from X.split.hom ≫ f ≫ Y.split.inv

theorem normalize_id (X : Position G) :
    normalize (𝟙 X.ambient) = 𝟙 X.computation := by
  change X.split.hom ≫ 𝟙 X.ambient ≫ X.split.inv = 𝟙 X.computation.boundary
  simp

theorem normalize_comp {X Y Z : Position G} (f : X.ambient ⟶ Y.ambient)
    (g : Y.ambient ⟶ Z.ambient) : normalize (f ≫ g) = normalize f ≫ normalize g := by
  change X.split.hom ≫ (f ≫ g) ≫ Z.split.inv =
    (X.split.hom ≫ f ≫ Y.split.inv) ≫ (Y.split.hom ≫ g ≫ Z.split.inv)
  simp [Category.assoc]

theorem split_hom (X : Position G) : X.split.hom ≈ₐ (σ X.before).hom ▷ V X.after :=
  splitLeft_hom ⟨X.before⟩ ⟨X.after⟩

theorem split_inv (X : Position G) : X.split.inv ≈ₐ (σ X.before).inv ▷ V X.after :=
  splitLeft_inv ⟨X.before⟩ ⟨X.after⟩

theorem append_split_hom (X : Position G) (A : List G.Obj) :
    (X.append A).split.hom ≈ₐ X.split.hom ▷ V A :=
  (split_hom (X.append A)).trans (((SameArrow.refl _).whiskerRight (word_append X.after A)).trans
    ((whisker_right_right (σ X.before).hom (V X.after) (V A)).symm.trans
      ((split_hom X).whiskerRight rfl).symm))

theorem append_split_inv (X : Position G) (A : List G.Obj) :
    (X.append A).split.inv ≈ₐ X.split.inv ▷ V A :=
  (split_inv (X.append A)).trans (((SameArrow.refl _).whiskerRight (word_append X.after A)).trans
    ((whisker_right_right (σ X.before).inv (V X.after) (V A)).symm.trans
      ((split_inv X).whiskerRight rfl).symm))

theorem prepend_split_hom (A : List G.Obj) (X : Position G) :
    (prepend A X).split.hom ≈ₐ
      ((⟨A⟩ : Computations G).splitLeft X.computation).hom ≫ₐ (V A ◁ X.split.hom) := by
  have e := (crossing_append A X.before).whiskerRight (X := V X.after) rfl
  rw [SameArrow.join_whiskerRight] at e
  refine (split_hom (prepend A X)).trans (e.trans ?_)
  have ea := (whisker_right_right (σ A).hom (V X.before) (V X.after)).trans
    (((SameArrow.refl _).whiskerRight (word_append X.before X.after).symm).trans
      (splitLeft_hom (⟨A⟩ : Computations G) X.computation).symm)
  have eb := (whisker_left_right (V A) (σ X.before).hom (V X.after)).trans
    ((split_hom X).symm.whiskerLeft (X := V A) rfl)
  exact ea.join_congr eb _ _

theorem prepend_split_inv (A : List G.Obj) (X : Position G) :
    (prepend A X).split.inv ≈ₐ
      (V A ◁ X.split.inv) ≫ₐ ((⟨A⟩ : Computations G).splitLeft X.computation).inv := by
  have e := (crossing_append_inv A X.before).whiskerRight (X := V X.after) rfl
  rw [SameArrow.join_whiskerRight] at e
  refine (split_inv (prepend A X)).trans (e.trans ?_)
  have ea := (whisker_right_right (σ A).inv (V X.before) (V X.after)).trans
    (((SameArrow.refl _).whiskerRight (word_append X.before X.after).symm).trans
      (splitLeft_inv (⟨A⟩ : Computations G) X.computation).symm)
  have eb := (whisker_left_right (V A) (σ X.before).inv (V X.after)).trans
    ((split_inv X).symm.whiskerLeft (X := V A) rfl)
  exact eb.join_congr ea _ _

end Position
end Silmaril.RuntimeWires.Proofs.EffectfulUniversal

namespace Silmaril.RuntimeWires.Proofs.EffectfulUniversal.Position

open CategoryTheory Presentation RuntimeCoherence
open scoped SameArrow

universe u v

variable {G : EffectfulPolygraph.{u,v}}

def find : List (Wire G.Obj) → Position G
  | [] => ⟨[], []⟩
  | none :: A => ⟨[], eraseBoundary A⟩
  | some x :: A => ⟨x :: (find A).before, (find A).after⟩

theorem find_split (A B : List G.Obj) : find (G := G) (values A ++ none :: values B) = ⟨A, B⟩ := by
  induction A with
  | nil =>
    change (⟨[], eraseBoundary (values B)⟩ : Position G) = ⟨[], B⟩
    rw [eraseBoundary_values]
  | cons a A ih =>
    change (⟨a :: (find (G := G) (values A ++ none :: values B)).before,
      (find (G := G) (values A ++ none :: values B)).after⟩ : Position G) = ⟨a :: A, B⟩
    rw [ih]

theorem find_ambient (X : Position G) : find X.ambient.word = X := by
  cases X with
  | mk A B => exact find_split A B

theorem ambient_injective : Function.Injective (ambient (G := G)) :=
  (show Function.LeftInverse (fun A : Runtime G => find A.word) ambient from find_ambient).injective

theorem ambient_find {A : Runtime G} (h : runtimeCount A.word = 1) : (find A.word).ambient = A := by
  obtain ⟨L, R, hA⟩ := runtimeCount_one_split h
  apply word_ext
  rw [hA, find_split]
  rfl

theorem count_ambient (X : Position G) : runtimeCount X.ambient.word = 1 := by
  change runtimeCount (values X.before ++ none :: values X.after) = 1
  rw [runtimeCount_append, runtimeCount_values]
  exact congrArg Nat.succ ((Nat.zero_add _).trans (runtimeCount_values X.after))

theorem normalize_congr {A B X Y : Position G} {f : A.ambient ⟶ B.ambient}
    {g : X.ambient ⟶ Y.ambient} (h : f ≈ₐ g) :
    (show A.computation.boundary ⟶ B.computation.boundary from normalize f) ≈ₐ
      (show X.computation.boundary ⟶ Y.computation.boundary from normalize g) := by
  have p := ambient_injective h.source
  have q := ambient_injective h.target
  subst p
  subst q
  rw [h.eq]
  exact SameArrow.refl _

end Silmaril.RuntimeWires.Proofs.EffectfulUniversal.Position
