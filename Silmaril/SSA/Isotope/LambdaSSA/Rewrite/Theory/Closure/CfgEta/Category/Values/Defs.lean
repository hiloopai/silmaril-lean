module

public import Mathlib.CategoryTheory.Widesubcategory
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Purity.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Singleton.Defs

/-! # Pure returns in the one-block CFG η quotient

Ghalayini and Krishnaswami define `ret e` as `br out e` and use its image as
the pure wide subcategory in §5.4, *The Denotational Semantics of SSA*,
arXiv:2411.09347v2. Here `out` is label zero, and the computation category
requires constructor-valued branch arguments. `returnRegion` binds the
returned value before branching and lowers unary expression lets by sequencing
their returns. `PureReturn` uses the image of these representatives at empty
capture, with equality inherited from the existing computation classes.
-/

@[expose] public section

universe v w u

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory

open CategoryTheory

/-- Return the value of an expression. An expression let sequences its two
returns by label substitution. Other expressions are evaluated once before
a constructor-valued branch. -/
def returnRegion {Φ : Type u} : Tm Φ → Region Φ
  | .let₁ a b => (returnRegion a).lsubst (fun _ => returnRegion b)
  | a => .let₁ a (.br 0 (.var 0))

variable {τ : Type v} [TypeFormers τ] {Φ : Type u} [HasTy Φ τ]
variable {ε : Type w} [HasEff Φ ε]

/-- A computation class at empty capture is pure when it is represented by
returning a typed pure expression. Equality is inherited from the computation category. -/
def PureReturn (pe : ε) : MorphismProperty (TypeCategory Φ ([] : VCtx τ)) :=
  fun A B f => ∃ (a : Tm Φ), Tm.HasType ([A] : VCtx τ) a B ∧ Tm.Pure pe a ∧
    ∃ h : ValueBranches ([A] : VCtx τ) (returnRegion a) [B], f = ofRegion h

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory
