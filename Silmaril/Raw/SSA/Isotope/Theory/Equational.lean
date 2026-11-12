module

public import Silmaril.Raw.SSA.Isotope.Theory.Contexts
public import Silmaril.Raw.SSA.Isotope.Logic.Metatheory.Theory.Basic
public import Silmaril.Raw.SSA.Isotope.LetSeq.LocallyNameless.Equiv
public import Silmaril.Raw.SSA.Isotope.LetCase.LocallyNameless.Equiv
public import Silmaril.Raw.SSA.Isotope.LetIter.LocallyNameless.Equiv

/-!
# Equational theory categories for the three let calculi

Raw and exactly typed syntax carry their actual constructor contexts. Their
independently generated equational theories are objects of the generic theory
categories, with the existing scope and typing indices retained.
-/

@[expose] public section

universe u v w r

namespace Silmaril.Isotope.LetSeq.LocallyNameless

open Silmaril.Isotope.Theory Silmaril.Logic.Metatheory

variable {ν : Type w} {Φ : Type v}

/-- Untyped syntax remains sorted by binder scope. -/
def rawSyntax (ν : Type w) (Φ : Type v) : IndexedSyntax where
  Index := Nat
  Term := Tm ν Φ
  Context := RawContext

variable {ε : Type r} [HasEff Φ ε]

/-- The raw contextual equational theory, with all constructor positions. -/
def rawEquationalTheory (pureEff : ε) : EquationalTheory (rawSyntax ν Φ) where
  Rel := RawEquiv pureEff
  refl := RawEquiv.refl
  trans := RawEquiv.trans
  symm := RawEquiv.symm
  congr _ hc h := by
    cases hc with
    | op f => exact .op h
    | let₁_left b => exact .let₁ h (.refl b)
    | let₁_right a => exact .let₁ (.refl a) h
    | pair_left b => exact .pair h (.refl b)
    | pair_right a => exact .pair (.refl a) h
    | let₂_left b => exact .let₂ h (.refl b)
    | let₂_right a => exact .let₂ (.refl a) h

variable {τ : Type u} [HasProduct τ] [HasUnit τ] [DecidableEq ν] [HasTy Φ τ]

/-- Intrinsic exact typing as an indexed family of syntax fibers. -/
def typedSyntax (Φ : Type v) [HasTy Φ τ] (Γ : Ctx ν τ) : IndexedSyntax where
  Index := TypingIndex τ
  Term := TypedTerm Φ Γ
  Context := TypedContext Γ

/-- The exact theory lives over typed fibers, so reflexivity is total there. -/
def equationalTheory (pureEff : ε) (Γ : Ctx ν τ) :
    EquationalTheory (typedSyntax Φ Γ) where
  Rel {i} a b := Equiv pureEff Γ i.bound a.val b.val i.result
  refl a := Equiv.refl a.property
  trans := Equiv.trans
  symm := Equiv.symm
  congr _ hc h := by
    cases hc with
    | op  => exact .op h
    | let₁_left b => exact .let₁ h (.refl b.property)
    | let₁_right a => exact .let₁ (.refl a.property) h
    | pair_left b => exact .pair h (.refl b.property)
    | pair_right a => exact .pair (.refl a.property) h
    | let₂_left b => exact .let₂ h (.refl b.property)
    | let₂_right a => exact .let₂ (.refl a.property) h

/-- The fixed-syntax category of raw equational theories. -/
abbrev RawEquationalTheories (ν : Type w) (Φ : Type v) :=
  EquationalTheory (rawSyntax ν Φ)

/-- The fixed-syntax category of exactly typed equational theories. -/
abbrev TypedEquationalTheories (Φ : Type v) [HasTy Φ τ] (Γ : Ctx ν τ) :=
  EquationalTheory (typedSyntax Φ Γ)

end Silmaril.Isotope.LetSeq.LocallyNameless

namespace Silmaril.Isotope.LetCase.LocallyNameless

open Silmaril.Isotope.Theory Silmaril.Logic.Metatheory

variable {ν : Type w} {Φ : Type v}

/-- Untyped syntax remains sorted by binder scope. -/
def rawSyntax (ν : Type w) (Φ : Type v) : IndexedSyntax where
  Index := Nat
  Term := Tm ν Φ
  Context := RawContext

variable {ε : Type r} [HasEff Φ ε]

/-- The raw contextual equational theory, with all constructor positions. -/
def rawEquationalTheory (pureEff : ε) : EquationalTheory (rawSyntax ν Φ) where
  Rel := RawEquiv pureEff
  refl := RawEquiv.refl
  trans := RawEquiv.trans
  symm := RawEquiv.symm
  congr _ hc h := by
    cases hc with
    | op f => exact .op h
    | let₁_left b => exact .let₁ h (.refl b)
    | let₁_right a => exact .let₁ (.refl a) h
    | pair_left b => exact .pair h (.refl b)
    | pair_right a => exact .pair (.refl a) h
    | let₂_left b => exact .let₂ h (.refl b)
    | let₂_right a => exact .let₂ (.refl a) h
    | inl  => exact .inl h
    | inr  => exact .inr h
    | case_scrutinee l r => exact .case h (.refl l) (.refl r)
    | case_left e r => exact .case (.refl e) h (.refl r)
    | case_right e l => exact .case (.refl e) (.refl l) h
    | abort  => exact .abort h

variable {τ : Type u} [TypeFormers τ] [DecidableEq ν] [HasTy Φ τ]

/-- Intrinsic exact typing as an indexed family of syntax fibers. -/
def typedSyntax (Φ : Type v) [HasTy Φ τ] (Γ : Ctx ν τ) : IndexedSyntax where
  Index := TypingIndex τ
  Term := TypedTerm Φ Γ
  Context := TypedContext Γ

/-- The exact theory lives over typed fibers, so reflexivity is total there. -/
def equationalTheory (pureEff : ε) (Γ : Ctx ν τ) :
    EquationalTheory (typedSyntax Φ Γ) where
  Rel {i} a b := Equiv pureEff Γ i.bound a.val b.val i.result
  refl a := Equiv.refl a.property
  trans := Equiv.trans
  symm := Equiv.symm
  congr _ hc h := by
    cases hc with
    | op  => exact .op h
    | let₁_left b => exact .let₁ h (.refl b.property)
    | let₁_right a => exact .let₁ (.refl a.property) h
    | pair_left b => exact .pair h (.refl b.property)
    | pair_right a => exact .pair (.refl a.property) h
    | let₂_left b => exact .let₂ h (.refl b.property)
    | let₂_right a => exact .let₂ (.refl a.property) h
    | inl  => exact .inl h
    | inr  => exact .inr h
    | case_scrutinee l r => exact .case h (.refl l.property) (.refl r.property)
    | case_left e r => exact .case (.refl e.property) h (.refl r.property)
    | case_right e l => exact .case (.refl e.property) (.refl l.property) h
    | abort  => exact .abort h

/-- The fixed-syntax category of raw equational theories. -/
abbrev RawEquationalTheories (ν : Type w) (Φ : Type v) :=
  EquationalTheory (rawSyntax ν Φ)

/-- The fixed-syntax category of exactly typed equational theories. -/
abbrev TypedEquationalTheories (Φ : Type v) [HasTy Φ τ] (Γ : Ctx ν τ) :=
  EquationalTheory (typedSyntax Φ Γ)

end Silmaril.Isotope.LetCase.LocallyNameless

namespace Silmaril.Isotope.LetIter.LocallyNameless

open Silmaril.Isotope.Theory Silmaril.Logic.Metatheory

variable {ν : Type w} {Φ : Type v}

/-- Untyped syntax remains sorted by binder scope. -/
def rawSyntax (ν : Type w) (Φ : Type v) : IndexedSyntax where
  Index := Nat
  Term := Tm ν Φ
  Context := RawContext

variable {ε : Type r} [HasEff Φ ε]

/-- The raw contextual equational theory, with all constructor positions. -/
def rawEquationalTheory (pureEff : ε) : EquationalTheory (rawSyntax ν Φ) where
  Rel := RawEquiv pureEff
  refl := RawEquiv.refl
  trans := RawEquiv.trans
  symm := RawEquiv.symm
  congr _ hc h := by
    cases hc with
    | op f => exact .op h
    | let₁_left b => exact .let₁ h (.refl b)
    | let₁_right a => exact .let₁ (.refl a) h
    | pair_left b => exact .pair h (.refl b)
    | pair_right a => exact .pair (.refl a) h
    | let₂_left b => exact .let₂ h (.refl b)
    | let₂_right a => exact .let₂ (.refl a) h
    | inl  => exact .inl h
    | inr  => exact .inr h
    | case_scrutinee l r => exact .case h (.refl l) (.refl r)
    | case_left e r => exact .case (.refl e) h (.refl r)
    | case_right e l => exact .case (.refl e) (.refl l) h
    | abort  => exact .abort h
    | iter_left b => exact .iter h (.refl b)
    | iter_right a => exact .iter (.refl a) h

variable {τ : Type u} [TypeFormers τ] [DecidableEq ν] [HasTy Φ τ]

/-- Intrinsic exact typing as an indexed family of syntax fibers. -/
def typedSyntax (Φ : Type v) [HasTy Φ τ] (Γ : Ctx ν τ) : IndexedSyntax where
  Index := TypingIndex τ
  Term := TypedTerm Φ Γ
  Context := TypedContext Γ

/-- The exact theory lives over typed fibers, so reflexivity is total there. -/
def equationalTheory (pureEff : ε) (Γ : Ctx ν τ) :
    EquationalTheory (typedSyntax Φ Γ) where
  Rel {i} a b := Equiv pureEff Γ i.bound a.val b.val i.result
  refl a := Equiv.refl a.property
  trans := Equiv.trans
  symm := Equiv.symm
  congr _ hc h := by
    cases hc with
    | op  => exact .op h
    | let₁_left b => exact .let₁ h (.refl b.property)
    | let₁_right a => exact .let₁ (.refl a.property) h
    | pair_left b => exact .pair h (.refl b.property)
    | pair_right a => exact .pair (.refl a.property) h
    | let₂_left b => exact .let₂ h (.refl b.property)
    | let₂_right a => exact .let₂ (.refl a.property) h
    | inl  => exact .inl h
    | inr  => exact .inr h
    | case_scrutinee l r => exact .case h (.refl l.property) (.refl r.property)
    | case_left e r => exact .case (.refl e.property) h (.refl r.property)
    | case_right e l => exact .case (.refl e.property) (.refl l.property) h
    | abort  => exact .abort h
    | iter_left b => exact .iter h (.refl b.property)
    | iter_right a => exact .iter (.refl a.property) h

/-- The fixed-syntax category of raw equational theories. -/
abbrev RawEquationalTheories (ν : Type w) (Φ : Type v) :=
  EquationalTheory (rawSyntax ν Φ)

/-- The fixed-syntax category of exactly typed equational theories. -/
abbrev TypedEquationalTheories (Φ : Type v) [HasTy Φ τ] (Γ : Ctx ν τ) :=
  EquationalTheory (typedSyntax Φ Γ)

end Silmaril.Isotope.LetIter.LocallyNameless

