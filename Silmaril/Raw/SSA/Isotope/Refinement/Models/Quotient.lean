module

public import Silmaril.Raw.SSA.Isotope.Refinement.Derivation
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Algebra
public import Silmaril.Raw.SSA.Isotope.Logic.Metatheory.Theory.OrderedModel

@[expose] public section
noncomputable section

/-! # Initial quotients for the written quantitative refinement theories

The same construction applies to let-seq, let-case, and let-iter via the native
fragment parameter.  Models have genuine quantitative constructor operations;
ordered-model morphisms preserve those operations and the carrier orders.
The quotient identifies exactly mutual derivability in the formed written
judgment, including its effect, usage, and directed uniformity conditions.
-/

namespace Silmaril.Isotope.Refinement.Models

open Silmaril.Logic.Metatheory.TheoryModel CategoryTheory Silmaril.Logic.Metatheory.TheoryModel

universe u v w
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]

/-- Every native operation is monotone for derivable written refinement. -/
def refinementPreorder (F : Fragment) (R : Relation τ Φ) :
    CompatiblePreorder (syntaxAlgebra (τ := τ) Φ ε F) where
  Rel {i} a b := Refines (ε := ε) F R i.context a.1 b.1 i.result
  refl a := .refl ⟨a.2⟩
  trans := Refines.trans
  compatible o a b h := by
    cases o with
    | var i hv => exact .refl ⟨.var i hv⟩
    | op f => exact .op (h 0)
    | let₁ A B s => exact .let₁ s (h 0) (h 1)
    | unit hd => exact .refl ⟨.unit hd⟩
    | pair A B s => exact .pair s (h 0) (h 1)
    | let₂ A B C s => exact .let₂ s (h 0) (h 1)
    | inl A B f => exact .inl f (h 0)
    | inr A B f => exact .inr f (h 0)
    | case A B C f s => exact .case f s (h 0) (h 1) (h 2)
    | abort C f => exact .abort f (h 0)
    | iter A B f s u => exact .iter f s u (h 0) (h 1)

/-- Equivalence in the written calculus is mutual refinement. -/
def equationCongruence (F : Fragment) (R : Relation τ Φ) :
    Congruence (syntaxAlgebra (τ := τ) Φ ε F) := (refinementPreorder F R).equationalCore

/-- Models of the actual operations validating mutual refinement. -/
abbrev EquationalModels (F : Fragment) (R : Relation τ Φ) :=
  Silmaril.Logic.Metatheory.TheoryModel.Models (syntaxIsInitial (τ := τ) Φ ε F) (equationCongruence F R)

def syntacticModel (F : Fragment) (R : Relation τ Φ) : EquationalModels (ε := ε) F R :=
  quotientModel (syntaxIsInitial (τ := τ) Φ ε F) (equationCongruence F R)

def syntacticModelIsInitial (F : Fragment) (R : Relation τ Φ) :
    CategoryTheory.Limits.IsInitial (syntacticModel (ε := ε) F R) :=
  quotientIsInitial (syntaxIsInitial (τ := τ) Φ ε F) (equationCongruence F R)

/-- Ordered constructor models validating the directed rules. -/
abbrev RefinementModels (F : Fragment) (R : Relation τ Φ) :=
  OrderedModels (syntaxIsInitial (τ := τ) Φ ε F) (refinementPreorder F R)

def orderedSyntacticModel (F : Fragment) (R : Relation τ Φ) : RefinementModels (ε := ε) F R :=
  orderedQuotientModel (syntaxIsInitial (τ := τ) Φ ε F) (refinementPreorder F R)

/-- Antisymmetrization is categorically initial among all validating ordered models. -/
def orderedSyntacticModelIsInitial (F : Fragment) (R : Relation τ Φ) :
    CategoryTheory.Limits.IsInitial (orderedSyntacticModel (ε := ε) F R) :=
  orderedQuotientIsInitial (syntaxIsInitial (τ := τ) Φ ε F) (refinementPreorder F R)

/-- No extra directed inequalities are introduced by the initial model. -/
theorem orderedSyntacticModel_le_iff (F : Fragment) (R : Relation τ Φ)
    {i : TypingIndex τ} (a b : Carrier Φ ε F i) :
    (show (orderedSyntacticModel (ε := ε) F R).algebra.Carrier i from
      (quotientMap (refinementPreorder (ε := ε) F R).equationalCore).map a) ≤
      (quotientMap (refinementPreorder (ε := ε) F R).equationalCore).map b ↔
      Refines (ε := ε) F R i.context a.1 b.1 i.result := Iff.rfl

/-- Derivability is exactly validity in every ordered operation model. -/
theorem refinement_iff_all_models (F : Fragment) (R : Relation τ Φ)
    {i : TypingIndex τ} (a b : Carrier Φ ε F i) :
    SemanticallyRefines (syntaxIsInitial (τ := τ) Φ ε F) (refinementPreorder F R) a b ↔
      Refines (ε := ε) F R i.context a.1 b.1 i.result :=
  semanticallyRefines_iff (syntaxIsInitial (τ := τ) Φ ε F) (refinementPreorder F R) a b

/-- Equality in every ordered model is precisely mutual refinement. -/
theorem mutual_refinement_iff_all_models (F : Fragment) (R : Relation τ Φ)
    {i : TypingIndex τ} (a b : Carrier Φ ε F i) :
    (∀ M : RefinementModels (ε := ε) F R,
      ((syntaxIsInitial (τ := τ) Φ ε F).to M.algebra.toAlgebra).map a =
        ((syntaxIsInitial (τ := τ) Φ ε F).to M.algebra.toAlgebra).map b) ↔
      Equates (ε := ε) F R i.context a.1 b.1 i.result :=
  semanticallyEqual_iff (syntaxIsInitial (τ := τ) Φ ε F) (refinementPreorder F R) a b

/-- The analogous equational-model completeness result for the mutual theory. -/
theorem equation_iff_all_models (F : Fragment) (R : Relation τ Φ)
    {i : TypingIndex τ} (a b : Carrier Φ ε F i) :
    Equates (ε := ε) F R i.context a.1 b.1 i.result ↔
      ∀ M : EquationalModels (ε := ε) F R,
        ((syntaxIsInitial (τ := τ) Φ ε F).to M.algebra).map a =
          ((syntaxIsInitial (τ := τ) Φ ε F).to M.algebra).map b :=
  Silmaril.Logic.Metatheory.TheoryModel.semantic_iff
    (syntaxIsInitial (τ := τ) Φ ε F) (equationCongruence F R) a b

end Silmaril.Isotope.Refinement.Models
