module

public import Silmaril.Raw.SSA.Isotope.Theory.Models.Theories
public import Silmaril.Raw.SSA.Isotope.Theory.Refinement

@[expose] public section

/-!
# Initial ordered refinement models for let-seq, let-case, and let-iter

The objects are partial-order algebras interpreting every constructor, with
monotone operations and validation of the exact generated refinement theory.
Arrows preserve operations and orders. Each syntax quotient by mutual refinement
is initial, and its order records exactly derivable refinement.
-/

universe u v w r

namespace Silmaril.Isotope.LetSeq.LocallyNameless.Models

open Silmaril.Isotope.Theory Silmaril.Logic.Metatheory.TheoryModel CategoryTheory Silmaril.Logic.Metatheory.TheoryModel

variable {τ : Type u} [HasProduct τ] [HasUnit τ] {ν : Type w} [DecidableEq ν]
variable {Φ : Type v} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε]

/-- Generated refinement specializes the common contextual-model construction. -/
def refinementPreorder (pureEff : ε) (Γ : Ctx ν τ) (R : TypedRelation ν Φ τ) :
    CompatiblePreorder (syntaxAlgebra Φ Γ) :=
  theoryPrecongruence (refinementTheory pureEff Γ R)

/-- Genuine ordered models of the exact refinement theory. -/
abbrev RefinementModels (pureEff : ε) (Γ : Ctx ν τ) (R : TypedRelation ν Φ τ) :=
  OrderedModels (syntaxIsInitial Φ Γ) (refinementPreorder pureEff Γ R)

/-- Exact typed syntax quotiented by mutual refinement, retaining all operations. -/
noncomputable def orderedSyntacticModel (pureEff : ε) (Γ : Ctx ν τ)
    (R : TypedRelation ν Φ τ) : RefinementModels pureEff Γ R :=
  orderedQuotientModel (syntaxIsInitial Φ Γ) (refinementPreorder pureEff Γ R)

/-- Every validating ordered algebra admits exactly one monotone constructor homomorphism. -/
noncomputable def orderedSyntacticModelIsInitial (pureEff : ε) (Γ : Ctx ν τ)
    (R : TypedRelation ν Φ τ) :
    CategoryTheory.Limits.IsInitial (orderedSyntacticModel pureEff Γ R) :=
  orderedQuotientIsInitial (syntaxIsInitial Φ Γ) (refinementPreorder pureEff Γ R)

/-- The order on syntactic classes is precisely the generated exact refinement. -/
theorem orderedSyntacticModel_le_iff (pureEff : ε) (Γ : Ctx ν τ)
    (R : TypedRelation ν Φ τ) {i : TypingIndex τ} (a b : Carrier Φ Γ i) :
    (show (orderedSyntacticModel pureEff Γ R).algebra.Carrier i from
      (quotientMap (refinementPreorder pureEff Γ R).equationalCore).map a) ≤
      (quotientMap (refinementPreorder pureEff Γ R).equationalCore).map b ↔
      Refinement pureEff Γ R i.bound a.1 b.1 i.result := Iff.rfl

/-- Equality of classes means mutual derivability, rather than a symmetry rule. -/
theorem orderedSyntacticModel_eq_iff (pureEff : ε) (Γ : Ctx ν τ)
    (R : TypedRelation ν Φ τ) {i : TypingIndex τ} (a b : Carrier Φ Γ i) :
    (quotientMap (refinementPreorder pureEff Γ R).equationalCore).map a =
      (quotientMap (refinementPreorder pureEff Γ R).equationalCore).map b ↔
      Refinement pureEff Γ R i.bound a.1 b.1 i.result ∧
      Refinement pureEff Γ R i.bound b.1 a.1 i.result :=
  quotientMap_eq_iff (refinementPreorder pureEff Γ R).equationalCore a b

/-- Validity in every ordered operation model is exactly derivable refinement. -/
theorem refinement_iff_all_models (pureEff : ε) (Γ : Ctx ν τ)
    (R : TypedRelation ν Φ τ) {i : TypingIndex τ} (a b : Carrier Φ Γ i) :
    SemanticallyRefines (syntaxIsInitial Φ Γ) (refinementPreorder pureEff Γ R) a b ↔
      Refinement pureEff Γ R i.bound a.1 b.1 i.result :=
  semanticallyRefines_iff (syntaxIsInitial Φ Γ) (refinementPreorder pureEff Γ R) a b

/-- Equality in every ordered model is exactly mutual derivability. -/
theorem mutual_refinement_iff_all_models (pureEff : ε) (Γ : Ctx ν τ)
    (R : TypedRelation ν Φ τ) {i : TypingIndex τ} (a b : Carrier Φ Γ i) :
    (∀ M : RefinementModels pureEff Γ R,
      ((syntaxIsInitial Φ Γ).to M.algebra.toAlgebra).map a =
        ((syntaxIsInitial Φ Γ).to M.algebra.toAlgebra).map b) ↔
      Refinement pureEff Γ R i.bound a.1 b.1 i.result ∧
      Refinement pureEff Γ R i.bound b.1 a.1 i.result :=
  semanticallyEqual_iff (syntaxIsInitial Φ Γ) (refinementPreorder pureEff Γ R) a b

end Silmaril.Isotope.LetSeq.LocallyNameless.Models

namespace Silmaril.Isotope.LetCase.LocallyNameless.Models

open Silmaril.Isotope.Theory Silmaril.Logic.Metatheory.TheoryModel CategoryTheory Silmaril.Logic.Metatheory.TheoryModel

variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
variable {Φ : Type v} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε]

/-- Generated refinement specializes the common contextual-model construction. -/
def refinementPreorder (pureEff : ε) (Γ : Ctx ν τ) (R : TypedRelation ν Φ τ) :
    CompatiblePreorder (syntaxAlgebra Φ Γ) :=
  theoryPrecongruence (refinementTheory pureEff Γ R)

/-- Genuine ordered models of the exact refinement theory. -/
abbrev RefinementModels (pureEff : ε) (Γ : Ctx ν τ) (R : TypedRelation ν Φ τ) :=
  OrderedModels (syntaxIsInitial Φ Γ) (refinementPreorder pureEff Γ R)

/-- Exact typed syntax quotiented by mutual refinement, retaining all operations. -/
noncomputable def orderedSyntacticModel (pureEff : ε) (Γ : Ctx ν τ)
    (R : TypedRelation ν Φ τ) : RefinementModels pureEff Γ R :=
  orderedQuotientModel (syntaxIsInitial Φ Γ) (refinementPreorder pureEff Γ R)

/-- Every validating ordered algebra admits exactly one monotone constructor homomorphism. -/
noncomputable def orderedSyntacticModelIsInitial (pureEff : ε) (Γ : Ctx ν τ)
    (R : TypedRelation ν Φ τ) :
    CategoryTheory.Limits.IsInitial (orderedSyntacticModel pureEff Γ R) :=
  orderedQuotientIsInitial (syntaxIsInitial Φ Γ) (refinementPreorder pureEff Γ R)

/-- The order on syntactic classes is precisely the generated exact refinement. -/
theorem orderedSyntacticModel_le_iff (pureEff : ε) (Γ : Ctx ν τ)
    (R : TypedRelation ν Φ τ) {i : TypingIndex τ} (a b : Carrier Φ Γ i) :
    (show (orderedSyntacticModel pureEff Γ R).algebra.Carrier i from
      (quotientMap (refinementPreorder pureEff Γ R).equationalCore).map a) ≤
      (quotientMap (refinementPreorder pureEff Γ R).equationalCore).map b ↔
      Refinement pureEff Γ R i.bound a.1 b.1 i.result := Iff.rfl

/-- Equality of classes means mutual derivability, rather than a symmetry rule. -/
theorem orderedSyntacticModel_eq_iff (pureEff : ε) (Γ : Ctx ν τ)
    (R : TypedRelation ν Φ τ) {i : TypingIndex τ} (a b : Carrier Φ Γ i) :
    (quotientMap (refinementPreorder pureEff Γ R).equationalCore).map a =
      (quotientMap (refinementPreorder pureEff Γ R).equationalCore).map b ↔
      Refinement pureEff Γ R i.bound a.1 b.1 i.result ∧
      Refinement pureEff Γ R i.bound b.1 a.1 i.result :=
  quotientMap_eq_iff (refinementPreorder pureEff Γ R).equationalCore a b

/-- Validity in every ordered operation model is exactly derivable refinement. -/
theorem refinement_iff_all_models (pureEff : ε) (Γ : Ctx ν τ)
    (R : TypedRelation ν Φ τ) {i : TypingIndex τ} (a b : Carrier Φ Γ i) :
    SemanticallyRefines (syntaxIsInitial Φ Γ) (refinementPreorder pureEff Γ R) a b ↔
      Refinement pureEff Γ R i.bound a.1 b.1 i.result :=
  semanticallyRefines_iff (syntaxIsInitial Φ Γ) (refinementPreorder pureEff Γ R) a b

/-- Equality in every ordered model is exactly mutual derivability. -/
theorem mutual_refinement_iff_all_models (pureEff : ε) (Γ : Ctx ν τ)
    (R : TypedRelation ν Φ τ) {i : TypingIndex τ} (a b : Carrier Φ Γ i) :
    (∀ M : RefinementModels pureEff Γ R,
      ((syntaxIsInitial Φ Γ).to M.algebra.toAlgebra).map a =
        ((syntaxIsInitial Φ Γ).to M.algebra.toAlgebra).map b) ↔
      Refinement pureEff Γ R i.bound a.1 b.1 i.result ∧
      Refinement pureEff Γ R i.bound b.1 a.1 i.result :=
  semanticallyEqual_iff (syntaxIsInitial Φ Γ) (refinementPreorder pureEff Γ R) a b

end Silmaril.Isotope.LetCase.LocallyNameless.Models

namespace Silmaril.Isotope.LetIter.LocallyNameless.Models

open Silmaril.Isotope.Theory Silmaril.Logic.Metatheory.TheoryModel CategoryTheory Silmaril.Logic.Metatheory.TheoryModel

variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
variable {Φ : Type v} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε]

/-- Generated refinement specializes the common contextual-model construction. -/
def refinementPreorder (pureEff : ε) (Γ : Ctx ν τ) (R : TypedRelation ν Φ τ) :
    CompatiblePreorder (syntaxAlgebra Φ Γ) :=
  theoryPrecongruence (refinementTheory pureEff Γ R)

/-- Genuine ordered models of the exact refinement theory. -/
abbrev RefinementModels (pureEff : ε) (Γ : Ctx ν τ) (R : TypedRelation ν Φ τ) :=
  OrderedModels (syntaxIsInitial Φ Γ) (refinementPreorder pureEff Γ R)

/-- Exact typed syntax quotiented by mutual refinement, retaining all operations. -/
noncomputable def orderedSyntacticModel (pureEff : ε) (Γ : Ctx ν τ)
    (R : TypedRelation ν Φ τ) : RefinementModels pureEff Γ R :=
  orderedQuotientModel (syntaxIsInitial Φ Γ) (refinementPreorder pureEff Γ R)

/-- Every validating ordered algebra admits exactly one monotone constructor homomorphism. -/
noncomputable def orderedSyntacticModelIsInitial (pureEff : ε) (Γ : Ctx ν τ)
    (R : TypedRelation ν Φ τ) :
    CategoryTheory.Limits.IsInitial (orderedSyntacticModel pureEff Γ R) :=
  orderedQuotientIsInitial (syntaxIsInitial Φ Γ) (refinementPreorder pureEff Γ R)

/-- The order on syntactic classes is precisely the generated exact refinement. -/
theorem orderedSyntacticModel_le_iff (pureEff : ε) (Γ : Ctx ν τ)
    (R : TypedRelation ν Φ τ) {i : TypingIndex τ} (a b : Carrier Φ Γ i) :
    (show (orderedSyntacticModel pureEff Γ R).algebra.Carrier i from
      (quotientMap (refinementPreorder pureEff Γ R).equationalCore).map a) ≤
      (quotientMap (refinementPreorder pureEff Γ R).equationalCore).map b ↔
      Refinement pureEff Γ R i.bound a.1 b.1 i.result := Iff.rfl

/-- Equality of classes means mutual derivability, rather than a symmetry rule. -/
theorem orderedSyntacticModel_eq_iff (pureEff : ε) (Γ : Ctx ν τ)
    (R : TypedRelation ν Φ τ) {i : TypingIndex τ} (a b : Carrier Φ Γ i) :
    (quotientMap (refinementPreorder pureEff Γ R).equationalCore).map a =
      (quotientMap (refinementPreorder pureEff Γ R).equationalCore).map b ↔
      Refinement pureEff Γ R i.bound a.1 b.1 i.result ∧
      Refinement pureEff Γ R i.bound b.1 a.1 i.result :=
  quotientMap_eq_iff (refinementPreorder pureEff Γ R).equationalCore a b

/-- Validity in every ordered operation model is exactly derivable refinement. -/
theorem refinement_iff_all_models (pureEff : ε) (Γ : Ctx ν τ)
    (R : TypedRelation ν Φ τ) {i : TypingIndex τ} (a b : Carrier Φ Γ i) :
    SemanticallyRefines (syntaxIsInitial Φ Γ) (refinementPreorder pureEff Γ R) a b ↔
      Refinement pureEff Γ R i.bound a.1 b.1 i.result :=
  semanticallyRefines_iff (syntaxIsInitial Φ Γ) (refinementPreorder pureEff Γ R) a b

/-- Equality in every ordered model is exactly mutual derivability. -/
theorem mutual_refinement_iff_all_models (pureEff : ε) (Γ : Ctx ν τ)
    (R : TypedRelation ν Φ τ) {i : TypingIndex τ} (a b : Carrier Φ Γ i) :
    (∀ M : RefinementModels pureEff Γ R,
      ((syntaxIsInitial Φ Γ).to M.algebra.toAlgebra).map a =
        ((syntaxIsInitial Φ Γ).to M.algebra.toAlgebra).map b) ↔
      Refinement pureEff Γ R i.bound a.1 b.1 i.result ∧
      Refinement pureEff Γ R i.bound b.1 a.1 i.result :=
  semanticallyEqual_iff (syntaxIsInitial Φ Γ) (refinementPreorder pureEff Γ R) a b

end Silmaril.Isotope.LetIter.LocallyNameless.Models
