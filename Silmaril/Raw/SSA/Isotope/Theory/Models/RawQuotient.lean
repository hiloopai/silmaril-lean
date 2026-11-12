module

public import Silmaril.Raw.SSA.Isotope.Theory.Models.Raw

/-!
# Initial quotient models over scoped untyped syntax

These theorems apply to arbitrary raw contextual equations. In particular they
do not require the type-erased unit and sum laws, whose collapse is documented
separately. Model maps preserve the full constructor algebra.
-/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LetSeq.LocallyNameless.RawModels

open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel Silmaril.Logic.Metatheory
open CategoryTheory CategoryTheory.Limits

variable {ν : Type u} {Φ : Type v}

/-- One-hole contextual closure implies simultaneous constructor compatibility.
This single proof is shared by the equational and directed model constructions. -/
theorem contextual_compatible (E : RefinementTheory (rawSyntax ν Φ)) :
    (termAlgebra ν Φ).Compatible E.Rel := by
  intro n o a b h
  cases o with
  | fv _ => exact E.refl _
  | bv _ => exact E.refl _
  | unit => exact E.refl _
  | op f => exact E.congr _ (.op f) (h 0)
  | let₁ =>
    exact E.congr₂ Tm.let₁ RawContext.let₁_left RawContext.let₁_right (h 0) (h 1)
  | pair =>
    exact E.congr₂ Tm.pair RawContext.pair_left RawContext.pair_right (h 0) (h 1)
  | let₂ =>
    exact E.congr₂ Tm.let₂ RawContext.let₂_left RawContext.let₂_right (h 0) (h 1)

/-- Context compatibility gives compatibility with every constructor operation. -/
def congruence (E : EquationalTheory (rawSyntax ν Φ)) : Congruence (termAlgebra ν Φ) where
  Rel := E.Rel
  equivalence _ := ⟨E.refl, E.symm, E.trans⟩
  compatible := contextual_compatible E.toRefinementTheory

/-- Constructor algebras whose interpretations validate the chosen raw theory. -/
abbrev EquationalModels (E : EquationalTheory (rawSyntax ν Φ)) :=
  TheoryModel.Models (termIsInitial ν Φ) (congruence E)

/-- The actual raw syntax quotient, with descended constructor operations. -/
noncomputable def syntacticModel (E : EquationalTheory (rawSyntax ν Φ)) :
    EquationalModels E := quotientModel (termIsInitial ν Φ) (congruence E)

/-- Quotiented raw syntax is initial in the corresponding algebra model category. -/
noncomputable def syntacticModelIsInitial (E : EquationalTheory (rawSyntax ν Φ)) :
    IsInitial (syntacticModel E) := quotientIsInitial (termIsInitial ν Φ) (congruence E)

/-- The quotient identifies exactly the selected raw equations. -/
theorem quotient_eq_iff (E : EquationalTheory (rawSyntax ν Φ)) {n : Nat}
    (a b : Tm ν Φ n) :
    (quotientMap (congruence E)).map a = (quotientMap (congruence E)).map b ↔ E.Rel a b :=
  quotientMap_eq_iff (congruence E) a b

end Silmaril.Isotope.LetSeq.LocallyNameless.RawModels

namespace Silmaril.Isotope.LetCase.LocallyNameless.RawModels

open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel Silmaril.Logic.Metatheory
open CategoryTheory CategoryTheory.Limits

variable {ν : Type u} {Φ : Type v}

/-- One-hole contextual closure implies simultaneous constructor compatibility.
This single proof is shared by the equational and directed model constructions. -/
theorem contextual_compatible (E : RefinementTheory (rawSyntax ν Φ)) :
    (termAlgebra ν Φ).Compatible E.Rel := by
  intro n o a b h
  cases o with
  | fv _ => exact E.refl _
  | bv _ => exact E.refl _
  | unit => exact E.refl _
  | op f => exact E.congr _ (.op f) (h 0)
  | let₁ =>
    exact E.congr₂ Tm.let₁ RawContext.let₁_left RawContext.let₁_right (h 0) (h 1)
  | pair =>
    exact E.congr₂ Tm.pair RawContext.pair_left RawContext.pair_right (h 0) (h 1)
  | let₂ =>
    exact E.congr₂ Tm.let₂ RawContext.let₂_left RawContext.let₂_right (h 0) (h 1)
  | inl => exact E.congr _ .inl (h 0)
  | inr => exact E.congr _ .inr (h 0)
  | abort => exact E.congr _ .abort (h 0)
  | case =>
    exact E.congr₃ Tm.case RawContext.case_scrutinee RawContext.case_left RawContext.case_right
      (h 0) (h 1) (h 2)

/-- Context compatibility gives compatibility with every constructor operation. -/
def congruence (E : EquationalTheory (rawSyntax ν Φ)) : Congruence (termAlgebra ν Φ) where
  Rel := E.Rel
  equivalence _ := ⟨E.refl, E.symm, E.trans⟩
  compatible := contextual_compatible E.toRefinementTheory

/-- Constructor algebras whose interpretations validate the chosen raw theory. -/
abbrev EquationalModels (E : EquationalTheory (rawSyntax ν Φ)) :=
  TheoryModel.Models (termIsInitial ν Φ) (congruence E)

/-- The actual raw syntax quotient, with descended constructor operations. -/
noncomputable def syntacticModel (E : EquationalTheory (rawSyntax ν Φ)) :
    EquationalModels E := quotientModel (termIsInitial ν Φ) (congruence E)

/-- Quotiented raw syntax is initial in the corresponding algebra model category. -/
noncomputable def syntacticModelIsInitial (E : EquationalTheory (rawSyntax ν Φ)) :
    IsInitial (syntacticModel E) := quotientIsInitial (termIsInitial ν Φ) (congruence E)

/-- The quotient identifies exactly the selected raw equations. -/
theorem quotient_eq_iff (E : EquationalTheory (rawSyntax ν Φ)) {n : Nat}
    (a b : Tm ν Φ n) :
    (quotientMap (congruence E)).map a = (quotientMap (congruence E)).map b ↔ E.Rel a b :=
  quotientMap_eq_iff (congruence E) a b

end Silmaril.Isotope.LetCase.LocallyNameless.RawModels

namespace Silmaril.Isotope.LetIter.LocallyNameless.RawModels

open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel Silmaril.Logic.Metatheory
open CategoryTheory CategoryTheory.Limits

variable {ν : Type u} {Φ : Type v}

/-- One-hole contextual closure implies simultaneous constructor compatibility.
This single proof is shared by the equational and directed model constructions. -/
theorem contextual_compatible (E : RefinementTheory (rawSyntax ν Φ)) :
    (termAlgebra ν Φ).Compatible E.Rel := by
  intro n o a b h
  cases o with
  | fv _ => exact E.refl _
  | bv _ => exact E.refl _
  | unit => exact E.refl _
  | op f => exact E.congr _ (.op f) (h 0)
  | let₁ =>
    exact E.congr₂ Tm.let₁ RawContext.let₁_left RawContext.let₁_right (h 0) (h 1)
  | pair =>
    exact E.congr₂ Tm.pair RawContext.pair_left RawContext.pair_right (h 0) (h 1)
  | let₂ =>
    exact E.congr₂ Tm.let₂ RawContext.let₂_left RawContext.let₂_right (h 0) (h 1)
  | inl => exact E.congr _ .inl (h 0)
  | inr => exact E.congr _ .inr (h 0)
  | abort => exact E.congr _ .abort (h 0)
  | case =>
    exact E.congr₃ Tm.case RawContext.case_scrutinee RawContext.case_left RawContext.case_right
      (h 0) (h 1) (h 2)
  | iter =>
    exact E.congr₂ Tm.iter RawContext.iter_left RawContext.iter_right (h 0) (h 1)

/-- Context compatibility gives compatibility with every constructor operation. -/
def congruence (E : EquationalTheory (rawSyntax ν Φ)) : Congruence (termAlgebra ν Φ) where
  Rel := E.Rel
  equivalence _ := ⟨E.refl, E.symm, E.trans⟩
  compatible := contextual_compatible E.toRefinementTheory

/-- Constructor algebras whose interpretations validate the chosen raw theory. -/
abbrev EquationalModels (E : EquationalTheory (rawSyntax ν Φ)) :=
  TheoryModel.Models (termIsInitial ν Φ) (congruence E)

/-- The actual raw syntax quotient, with descended constructor operations. -/
noncomputable def syntacticModel (E : EquationalTheory (rawSyntax ν Φ)) :
    EquationalModels E := quotientModel (termIsInitial ν Φ) (congruence E)

/-- Quotiented raw syntax is initial in the corresponding algebra model category. -/
noncomputable def syntacticModelIsInitial (E : EquationalTheory (rawSyntax ν Φ)) :
    IsInitial (syntacticModel E) := quotientIsInitial (termIsInitial ν Φ) (congruence E)

/-- The quotient identifies exactly the selected raw equations. -/
theorem quotient_eq_iff (E : EquationalTheory (rawSyntax ν Φ)) {n : Nat}
    (a b : Tm ν Φ n) :
    (quotientMap (congruence E)).map a = (quotientMap (congruence E)).map b ↔ E.Rel a b :=
  quotientMap_eq_iff (congruence E) a b

end Silmaril.Isotope.LetIter.LocallyNameless.RawModels

