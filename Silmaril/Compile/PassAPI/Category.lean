module

public import Silmaril.Compile.PassAPI.Pass
public import Mathlib.CategoryTheory.Category.Basic

@[expose] public section

/-! # IRs and verified translations over one semantic domain

Fix a semantic carrier `S` and a preorder `D.Rel`, with
`D.Rel source replacement` meaning that the replacement is acceptable. An `IR D`
provides programs, their denotation in `S`, and an invariant. A `Translation A B`
is a total transformation preserving the invariant and relating the source
and target denotations through `D.Rel`.

Identity and composition form a category. Composition is diagrammatic: `f ≫ g`
runs `f` first. `endEquiv` identifies translations from an IR to itself with
passes for its pulled-back contract, preserving this sequencing convention.
Mathlib's endomorphism monoid instead uses function-composition order.

`HomLe` compares translations by pointwise refinement of their outputs on
invariant-satisfying inputs. `whisker_left_mono` proves monotonicity under
precomposition. Monotonicity under postcomposition would additionally require
the postcomposed transformation to preserve the semantic relation; soundness
alone does not supply that requirement.

This API uses one semantic domain. Relating languages with different domains,
interfaces or observations requires an additional semantic bridge. No such
bridge, execution semantics or institution correspondence is asserted here.
-/

namespace Silmaril.Compile.PassAPI

open CategoryTheory

/-- A semantic domain on the carrier `S`: a preorder of acceptable replacements. -/
structure Domain (S : Type) where
  Rel : S → S → Prop
  refl : ∀ s, Rel s s
  trans : ∀ {a b c : S}, Rel a b → Rel b c → Rel a c

/-- An IR over `D`: programs, a denotation in the chosen semantic domain, and
an invariant. -/
structure IR {S : Type} (D : Domain S) where
  Prog : Type
  den : Prog → S
  Inv : Prog → Prop

variable {S : Type} {D : Domain S}

/-- The contract of an IR: the domain's preorder pulled back along the denotation. -/
def IR.contract (A : IR D) : Contract A.Prog :=
  Contract.pullback D.Rel D.refl D.trans A.den A.Inv

/-- **A verified translation** between IRs over the same domain. -/
@[ext] structure Translation (A B : IR D) where
  run : A.Prog → B.Prog
  inv_run : ∀ {x}, A.Inv x → B.Inv (run x)
  sound : ∀ {x}, A.Inv x → D.Rel (A.den x) (B.den (run x))

namespace Translation

/-- The identity translation. -/
protected def id (A : IR D) : Translation A A := ⟨fun x => x, fun h => h, fun {_} _ => D.refl _⟩

/-- Composition, diagrammatic. -/
def comp {A B E : IR D} (f : Translation A B) (g : Translation B E) : Translation A E where
  run x := g.run (f.run x)
  inv_run h := g.inv_run (f.inv_run h)
  sound h := D.trans (f.sound h) (g.sound (f.inv_run h))

end Translation

/-- **The category of IRs over `D` and verified translations.** -/
instance instCategory : Category.{0} (IR D) where
  Hom := Translation
  id := Translation.id
  comp f g := Translation.comp f g
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] theorem id_run (A : IR D) (x : A.Prog) : Translation.run (𝟙 A) x = x := rfl

@[simp] theorem comp_run {A B E : IR D} (f : A ⟶ B) (g : B ⟶ E) (x : A.Prog) :
    Translation.run (f ≫ g) x = Translation.run g (Translation.run f x) := rfl

/-! ## Endomorphisms are passes -/

/-- **`End A` is the pass monoid of `A`** (as types: the identity on fields). -/
def endEquiv (A : IR D) : (A ⟶ A) ≃ Pass A.contract where
  toFun f := ⟨f.run, f.inv_run, f.sound⟩
  invFun p := ⟨p.run, p.inv_run, p.sound⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem endEquiv_id (A : IR D) : endEquiv A (𝟙 A) = 1 := rfl

theorem endEquiv_comp (A : IR D) (f g : A ⟶ A) :
    endEquiv A (f ≫ g) = endEquiv A f * endEquiv A g := rfl

/-- Pipelines of passes are composites of endomorphisms. -/
theorem endEquiv_symm_pipeline (A : IR D) (p q : Pass A.contract) :
    (endEquiv A).symm (Pass.pipeline [p, q]) = (endEquiv A).symm p ≫ (endEquiv A).symm q := rfl

/-! ## Preorder enrichment -/

/-- Pointwise refinement of translations. -/
def HomLe {A B : IR D} (f g : A ⟶ B) : Prop :=
  ∀ x, A.Inv x → D.Rel (B.den (Translation.run f x)) (B.den (Translation.run g x))

theorem HomLe.refl {A B : IR D} (f : A ⟶ B) : HomLe f f := fun _ _ => D.refl _

theorem HomLe.trans {A B : IR D} {f g h : A ⟶ B} (h₁ : HomLe f g) (h₂ : HomLe g h) :
    HomLe f h := fun x hx => D.trans (h₁ x hx) (h₂ x hx)

/-- Precomposition is monotone (left whiskering). -/
theorem whisker_left_mono {A B E : IR D} (k : A ⟶ B) {f g : B ⟶ E} (h : HomLe f g) :
    HomLe (k ≫ f) (k ≫ g) := fun _ hx => h _ (Translation.inv_run k hx)

/-- **Every pass lies above the identity** in the enrichment: that is its soundness field. -/
theorem id_le_of_end {A : IR D} (f : A ⟶ A) : HomLe (𝟙 A) f := fun _ hx => Translation.sound f hx

end Silmaril.Compile.PassAPI
