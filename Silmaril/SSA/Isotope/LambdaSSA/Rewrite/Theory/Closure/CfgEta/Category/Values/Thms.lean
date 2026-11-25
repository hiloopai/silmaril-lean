module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.CategoryValues

/-! # The pure-return value subcategory of the CFG η presentation -/

public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory

open CategoryTheory

variable {τ : Type v} [TypeFormers τ] {Φ : Type u} [HasTy Φ τ]
  {Γ : VCtx τ} {B : τ} {a : Tm Φ}

/-- A typed returning expression gives a region with only value branches. -/
theorem returnRegion_typed (h : Tm.HasType Γ a B) : ValueBranches Γ (returnRegion a) [B] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Values.returnRegion_typed h

/-- The lowered return of a constructor value agrees with the paper's literal branch
by the native branch-let equation. -/
theorem returnRegion_branchValue (h : Tm.BranchValue Γ a B) :
    RewriteEquiv Γ (returnRegion a) (.br 0 a) [B] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Values.returnRegion_branchValue h

variable {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "Comp" => TypeCategory Φ ([] : VCtx τ)

/-- The lowered return of any exactly typed pure expression lies in the value image. -/
theorem pureReturn_ofRegion {A : τ} (h : Tm.HasType [A] a B) (hp : Tm.Pure pe a) :
    PureReturn pe (ofRegion (returnRegion_typed h)) :=
  ⟨a, h, hp, returnRegion_typed h, rfl⟩

theorem pureReturn_id (A : Comp) : PureReturn pe (𝟙 A) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Values.pureReturn_id A

theorem pureReturn_comp {X Y Z : Comp} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : PureReturn pe f) (hg : PureReturn pe g) : PureReturn pe (f ≫ g) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Values.pureReturn_comp hf hg

instance pureReturn_multiplicative : (PureReturn (τ := τ) (Φ := Φ) pe).IsMultiplicative where
  id_mem := pureReturn_id pe
  comp_mem _ _ := pureReturn_comp pe

/-- The wide category of computation classes with pure return representatives. -/
abbrev ValueCategory := WideSubcategory (PureReturn (τ := τ) (Φ := Φ) pe)

/-- Include the pure-return computation classes as computation arrows. -/
@[expose] def values : ValueCategory (τ := τ) (Φ := Φ) pe ⥤ Comp :=
  wideSubcategoryInclusion _

instance values_faithful : (values (τ := τ) (Φ := Φ) pe).Faithful :=
  inferInstanceAs (wideSubcategoryInclusion _).Faithful

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory
