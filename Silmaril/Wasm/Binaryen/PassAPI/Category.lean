module

public import Silmaril.Wasm.Binaryen.PassAPI.Pass
public import Mathlib.CategoryTheory.Category.Basic

@[expose] public section

/-! # Pass API: the category of IRs and verified translations

Passes *within* one IR form a monoid (`PassAPI/Pass.lean`). Passes *between* IRs
(lowering Binaryen IR to Core Wasm, lifting back, an IR-to-IR compiler stage) form a
category, and the pass monoid of an IR is its endomorphism monoid.

**Objects.** Fix a semantic domain `D`: a carrier `S` with a preorder `D.Rel`
(`D.Rel s t`: `t` may replace `s`; for Wasm, export refinement on Core modules). An
`IR D` is a type of programs `Prog`, a denotation `den : Prog → D.S` (for an IR over
Wasm: its lowering, the defining semantics) and an invariant `Inv`.

**Morphisms.** `Translation A B`: `run : A.Prog → B.Prog` preserving the invariant and
sound, `D.Rel (A.den x) (B.den (run x))`. Identity and composition are the identity
pass and `seq`; the laws hold by `rfl` (`instCategory`).

**Endomorphisms are passes.** `endEquiv : Translation A A ≃ Pass A.contract` is the
identity on fields, sends `𝟙` to `1` and `f ≫ g` to `endEquiv f * endEquiv g`
(diagrammatic in both). So the endomorphism monoid of `A` is the pass monoid
(`Mathlib`'s `CategoryTheory.End` multiplies by `∘`, so it is the opposite monoid).

**Enrichment.** For fixed `A B`, translations are preordered by
`f ≤ g := ∀ x, A.Inv x → D.Rel (B.den (f x)) (B.den (g x))` (pointwise refinement of
outputs), and composition is monotone on the left: a 2-cell. `whisker_left_mono`
records the left action; right whiskering needs a monotone (congruent) `run` and is
not formalized here.

Single-domain scope: translations between IRs with *different* semantic domains (a
compiler to another target, a logic translation) need a semantic bridge between the
domains; institution comorphisms are one possible shape for such a bridge.
This module does not formalize a bridge between different semantic domains.
-/

namespace Silmaril.Wasm.Binaryen.PassAPI

open CategoryTheory

/-- A semantic domain on the carrier `S`: a preorder of acceptable replacements. -/
structure Domain (S : Type) where
  Rel : S → S → Prop
  refl : ∀ s, Rel s s
  trans : ∀ {a b c : S}, Rel a b → Rel b c → Rel a c

/-- An IR over the domain `D`: programs, a denotation (the defining semantics, for an IR
over Wasm its lowering) and an invariant. -/
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

end Silmaril.Wasm.Binaryen.PassAPI
