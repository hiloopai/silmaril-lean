module

public import Silmaril.Semantics.RuntimeWires.EffectfulUniversal.Thms

@[expose] public section

/-!
# The category of strict effectful categories

Corollary 5.4 (p. 9:16) of Mario Román and Paweł Sobociński,
*String Diagrams for Premonoidal Categories*, arXiv:2305.06075v5.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.StrictEffectful

open CategoryTheory

universe u v

/-- Bundling the categories allows the free runtime construction to be a functor.
The hom universe also fits words over the object type and dependent generator boundaries. -/
structure Bundled where
  Value : Type u
  Computation : Type u
  [valueCategory : Category.{max u v} Value]
  [computationCategory : Category.{max u v} Computation]
  [valueMonoidal : MonoidalCategory Value]
  [computationPremonoidal : PremonoidalCategory Computation]
  [valueStrict : IsStrictTensor Value]
  [computationStrict : IsStrictTensor Computation]
  model : StrictEffectful Value Computation

attribute [instance] Bundled.valueCategory Bundled.computationCategory Bundled.valueMonoidal
  Bundled.computationPremonoidal Bundled.valueStrict Bundled.computationStrict

namespace Bundled

/-- Bundle the strict runtime computation model. -/
def runtime (G : EffectfulPolygraph.{u,max u v}) : Bundled.{u,v} where
  Value := Presentation.Pure G
  Computation := Presentation.Computations G
  model := Presentation.strictRuntime G

/-- The signature of all value arrows or all computation arrows, indexed by
words of values. The function `object` assigns a target object to each word. -/
def wordSignature {V : Type u} {C : Type u} [Category.{max u v} C]
    (object : List V → C) : Signature.{u,max u v} V where
  Edge := Σ A B : List V, object A ⟶ object B
  source e := e.1
  target e := e.2.1

/-- The underlying effectful polygraph of a strict effectful category. -/
def polygraph (X : Bundled.{u,v}) : EffectfulPolygraph.{u,max u v} where
  Obj := X.Value
  pure := wordSignature (wordObject id)
  effect := wordSignature (X.model.pure.obj ∘ wordObject id)

end Bundled
end Silmaril.RuntimeWires.StrictEffectful
