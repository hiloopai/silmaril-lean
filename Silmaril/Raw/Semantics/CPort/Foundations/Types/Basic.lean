module

/-!
# Type-former capabilities

Each capability supplies an operation on type codes. Semantic laws and
interpretations are separate; the bundles only collect operations.
-/

@[expose] public section

universe u

namespace Silmaril

class HasProduct (τ : Type u) where
  product : τ → τ → τ

class HasCoproduct (τ : Type u) where
  coprod : τ → τ → τ

class HasUnit (τ : Type u) where
  unit : τ

class HasEmpty (τ : Type u) where
  empty : τ

/-- Binary products and their unit, sufficient for sequential type syntax. -/
class ProductTypeFormers (τ : Type u) extends HasProduct τ, HasUnit τ

/-- Binary coproducts and the empty type. -/
class CoproductTypeFormers (τ : Type u) extends HasCoproduct τ, HasEmpty τ

/-- The full signature used by SSA and let-iter. -/
class TypeFormers (τ : Type u) extends ProductTypeFormers τ, CoproductTypeFormers τ

variable {τ : Type u}

def product [HasProduct τ] (A B : τ) : τ := HasProduct.product A B
def coprod [HasCoproduct τ] (A B : τ) : τ := HasCoproduct.coprod A B
def unit [HasUnit τ] : τ := HasUnit.unit
def empty [HasEmpty τ] : τ := HasEmpty.empty

namespace TypeFormers

export HasProduct (product)
export HasCoproduct (coprod)
export HasUnit (unit)
export HasEmpty (empty)

end TypeFormers

end Silmaril
