module

public import Silmaril.Semantics.RuntimeWires.EffectfulExtension.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.EffectfulUniversal.Unique

@[expose] public section

/-!
# The free strict effectful category

Lemma 3.13 and Theorem 3.14 (pp. 9:10–9:13) of Mario Román and Paweł
Sobociński, *String Diagrams for Premonoidal Categories*, arXiv:2305.06075v5.
This is the universal property for the algebraic runtime presentation.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.StrictEffectful.Assignment

open CategoryTheory Diagram Presentation
open scoped MonoidalCategory

universe u v u' v' u₁ v₁

variable {V : Type u} {C : Type u'} [Category.{v} V] [Category.{v'} C]
variable [MonoidalCategory V] [PremonoidalCategory C] [IsStrictTensor V] [IsStrictTensor C]
variable {T : StrictEffectful V C} {G : EffectfulPolygraph.{u₁,v₁}}

variable (F : T.Assignment G)

/-- Agreement on value sorts determines agreement on all value words. These
are the object equalities used to compare the generator arrows in `Extends`. -/
theorem wordObjects_of_sortObjects (H : (strictRuntime G).Hom T)
    (h : ∀ x : G.Obj, H.value.obj ⟨[x]⟩ = F.obj x) (X : Pure G) :
    H.value.obj X = wordObject F.obj X.word :=
  Proofs.EffectfulUniversal.wordObjects_of_sortObjects F H h X

/-- Lemma 3.13. The prescribed pure and effectful generators extend to a
unique strict effectful functor, including the commuting pure square. -/
theorem uniqueExtension : ∃! H : (strictRuntime G).Hom T, F.Extends H :=
  ⟨F.extension, F.extension_extends, fun _ h =>
    Proofs.EffectfulUniversal.unique F h F.extension_extends⟩

end Silmaril.RuntimeWires.StrictEffectful.Assignment

namespace Silmaril.RuntimeWires.Presentation

open CategoryTheory
open scoped MonoidalCategory

universe u v u' v' u₁ v₁

variable {V : Type u} {C : Type u'} [Category.{v} V] [Category.{v'} C]
variable [MonoidalCategory V] [PremonoidalCategory C] [IsStrictTensor V] [IsStrictTensor C]

/-- Theorem 3.14. The strict effectful runtime presentation is free over its
effectful polygraph, and its computation homs are precisely the runtime
morphisms with the single runtime at the left of each boundary. The clique
hom-set equivalence implementing this identification is `leftmostEquiv`. -/
theorem freeRuntime (G : EffectfulPolygraph.{u₁,v₁}) (T : StrictEffectful V C) :
    (∀ F : T.Assignment G, ∃! H : (strictRuntime G).Hom T, F.Extends H) ∧
      (∀ A B : List G.Obj, Nonempty (Clique.Hom (braidClique A) (braidClique B) ≃
        ((⟨A⟩ : Computations G) ⟶ ⟨B⟩))) :=
  ⟨fun F => F.uniqueExtension, fun A B => ⟨leftmostEquiv A B⟩⟩

end Silmaril.RuntimeWires.Presentation
