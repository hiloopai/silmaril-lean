module

public import Silmaril.Raw.SSA.Isotope.Theory.Models.RawQuotient
public import Silmaril.Raw.SSA.Isotope.Logic.Metatheory.Theory.OrderedModel

/-!
# Initial ordered quotient models over scoped untyped syntax

These theorems apply to arbitrary raw contextual refinements. In particular they
do not require the type-erased unit and sum laws, whose collapse is documented
separately. Model maps preserve the full constructor algebra.
-/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LetSeq.LocallyNameless.RawModels

open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel
open CategoryTheory CategoryTheory.Limits

variable {ν : Type u} {Φ : Type v}

/-- Context compatibility gives compatibility with every constructor operation. -/
def compatiblePreorder (E : RefinementTheory (rawSyntax ν Φ)) :
    CompatiblePreorder (termAlgebra ν Φ) where
  Rel := E.Rel
  refl := E.refl
  trans := E.trans
  compatible := contextual_compatible E

/-- Ordered constructor algebras validating the selected raw refinement theory. -/
abbrev RefinementModels (R : RefinementTheory (rawSyntax ν Φ)) :=
  OrderedModels (termIsInitial ν Φ) (compatiblePreorder R)

/-- The raw syntax quotient by mutual refinement has monotone constructor operations. -/
noncomputable def orderedSyntacticModel (R : RefinementTheory (rawSyntax ν Φ)) :
    RefinementModels R := orderedQuotientModel (termIsInitial ν Φ) (compatiblePreorder R)

/-- Initiality is among monotone maps preserving every constructor. -/
noncomputable def orderedSyntacticModelIsInitial (R : RefinementTheory (rawSyntax ν Φ)) :
    IsInitial (orderedSyntacticModel R) :=
  orderedQuotientIsInitial (termIsInitial ν Φ) (compatiblePreorder R)

/-- The induced order on classes remembers exactly the original refinement. -/
theorem quotient_le_iff (R : RefinementTheory (rawSyntax ν Φ)) {n : Nat}
    (a b : Tm ν Φ n) :
    (show (orderedSyntacticModel R).algebra.Carrier n from
      (quotientMap (compatiblePreorder R).equationalCore).map a) ≤
      (quotientMap (compatiblePreorder R).equationalCore).map b ↔ R.Rel a b := Iff.rfl

end Silmaril.Isotope.LetSeq.LocallyNameless.RawModels

namespace Silmaril.Isotope.LetCase.LocallyNameless.RawModels

open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel
open CategoryTheory CategoryTheory.Limits

variable {ν : Type u} {Φ : Type v}

/-- Context compatibility gives compatibility with every constructor operation. -/
def compatiblePreorder (E : RefinementTheory (rawSyntax ν Φ)) :
    CompatiblePreorder (termAlgebra ν Φ) where
  Rel := E.Rel
  refl := E.refl
  trans := E.trans
  compatible := contextual_compatible E

/-- Ordered constructor algebras validating the selected raw refinement theory. -/
abbrev RefinementModels (R : RefinementTheory (rawSyntax ν Φ)) :=
  OrderedModels (termIsInitial ν Φ) (compatiblePreorder R)

/-- The raw syntax quotient by mutual refinement has monotone constructor operations. -/
noncomputable def orderedSyntacticModel (R : RefinementTheory (rawSyntax ν Φ)) :
    RefinementModels R := orderedQuotientModel (termIsInitial ν Φ) (compatiblePreorder R)

/-- Initiality is among monotone maps preserving every constructor. -/
noncomputable def orderedSyntacticModelIsInitial (R : RefinementTheory (rawSyntax ν Φ)) :
    IsInitial (orderedSyntacticModel R) :=
  orderedQuotientIsInitial (termIsInitial ν Φ) (compatiblePreorder R)

/-- The induced order on classes remembers exactly the original refinement. -/
theorem quotient_le_iff (R : RefinementTheory (rawSyntax ν Φ)) {n : Nat}
    (a b : Tm ν Φ n) :
    (show (orderedSyntacticModel R).algebra.Carrier n from
      (quotientMap (compatiblePreorder R).equationalCore).map a) ≤
      (quotientMap (compatiblePreorder R).equationalCore).map b ↔ R.Rel a b := Iff.rfl

end Silmaril.Isotope.LetCase.LocallyNameless.RawModels

namespace Silmaril.Isotope.LetIter.LocallyNameless.RawModels

open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel
open CategoryTheory CategoryTheory.Limits

variable {ν : Type u} {Φ : Type v}

/-- Context compatibility gives compatibility with every constructor operation. -/
def compatiblePreorder (E : RefinementTheory (rawSyntax ν Φ)) :
    CompatiblePreorder (termAlgebra ν Φ) where
  Rel := E.Rel
  refl := E.refl
  trans := E.trans
  compatible := contextual_compatible E

/-- Ordered constructor algebras validating the selected raw refinement theory. -/
abbrev RefinementModels (R : RefinementTheory (rawSyntax ν Φ)) :=
  OrderedModels (termIsInitial ν Φ) (compatiblePreorder R)

/-- The raw syntax quotient by mutual refinement has monotone constructor operations. -/
noncomputable def orderedSyntacticModel (R : RefinementTheory (rawSyntax ν Φ)) :
    RefinementModels R := orderedQuotientModel (termIsInitial ν Φ) (compatiblePreorder R)

/-- Initiality is among monotone maps preserving every constructor. -/
noncomputable def orderedSyntacticModelIsInitial (R : RefinementTheory (rawSyntax ν Φ)) :
    IsInitial (orderedSyntacticModel R) :=
  orderedQuotientIsInitial (termIsInitial ν Φ) (compatiblePreorder R)

/-- The induced order on classes remembers exactly the original refinement. -/
theorem quotient_le_iff (R : RefinementTheory (rawSyntax ν Φ)) {n : Nat}
    (a b : Tm ν Φ n) :
    (show (orderedSyntacticModel R).algebra.Carrier n from
      (quotientMap (compatiblePreorder R).equationalCore).map a) ≤
      (quotientMap (compatiblePreorder R).equationalCore).map b ↔ R.Rel a b := Iff.rfl

end Silmaril.Isotope.LetIter.LocallyNameless.RawModels

