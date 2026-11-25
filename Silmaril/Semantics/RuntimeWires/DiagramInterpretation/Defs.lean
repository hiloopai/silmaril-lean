module

public import Silmaril.Semantics.RuntimeWires.StrictEffectful.Thms

@[expose] public section

/-!
# Interpretation on typed words

This supplies the interpretation of pure generators in Lemma 3.13
(pp. 9:10–9:11), and the algebraic part of the free monoidal construction
in Lemma 3.4 and Theorem 3.6 (pp. 9:7–9:8) of Mario Román and Paweł
Sobociński, *String Diagrams for Premonoidal Categories*, arXiv:2305.06075v5.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.Diagram

open CategoryTheory
open scoped MonoidalCategory

universe u v u' v'

/-- Data for interpreting term syntax before imposing its congruence.
The object map is defined on words, so it can erase the runtime. -/
structure Interpretation {O : Type u} (S : Signature.{u,v} O) (C : Type u')
    [Category.{v'} C] [MonoidalCategoryStruct C] where
  obj : List O → C
  empty : obj [] = 𝟙_ C
  append (A B : List O) : obj (A ++ B) = obj A ⊗ obj B
  edge (e : S.Edge) : obj (S.source e) ⟶ obj (S.target e)

namespace Interpretation

variable {O : Type u} {S : Signature.{u,v} O}
variable {C : Type u'} [Category.{v'} C] [MonoidalCategoryStruct C]

/-- Transport a morphism to another presentation of its boundary objects. -/
def transport {A B X Y : C} (p : A = X) (q : B = Y) (f : A ⟶ B) : X ⟶ Y :=
  eqToHom p.symm ≫ f ≫ eqToHom q

/-- Evaluate a raw term. When the target is premonoidal this uses its
specified sequential tensor. -/
def eval (I : Interpretation S C) : {A B : List O} → Diagram S A B → (I.obj A ⟶ I.obj B)
  | _, _, .id A => 𝟙 (I.obj A)
  | _, _, .gen e => I.edge e
  | _, _, .comp f g => I.eval f ≫ I.eval g
  | _, _, .tensor (A := A) (B := B) (C := D) (D := E) f g =>
    transport (I.append A D).symm (I.append B E).symm (I.eval f ⊗ₘ I.eval g)

end Interpretation
end Silmaril.RuntimeWires.Diagram
