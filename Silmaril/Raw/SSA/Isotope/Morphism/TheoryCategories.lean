module

public import Silmaril.Raw.SSA.Isotope.Morphism.Theory
public import Silmaril.Raw.SSA.Isotope.Theory.Categories

/-!
# The calculus inclusions as theory and inference-system morphisms

Raw and typed inclusions share their syntax translations across equational and
refinement theories. Each translation preserves designated contexts, so it also
supports generic pullback and generated-theory constructions. Forgetting a theory
map to an inference-system morphism preserves the inclusion composites.
-/

@[expose] public section

universe u v w r

namespace Silmaril.Isotope.Morphism.SeqCase

open Silmaril.Logic.Metatheory CategoryTheory Silmaril.Logic.Metatheory
open LetSeq.LocallyNameless

variable {ν : Type u} {Φ : Type v}

/-- The constructor inclusion as a translation of scope-indexed syntax. -/
def rawTranslation : (rawSyntax ν Φ).Translation (LetCase.LocallyNameless.rawSyntax ν Φ) where
  sort n := n
  term := embed

/-- Every source hole translates to the same constructor position in the target. -/
theorem rawTranslation_contextual : (rawTranslation (ν := ν) (Φ := Φ)).Contextual := by
  intro i j c hc
  cases hc with
  | op f => exact ⟨_, .op f, fun _ => rfl⟩
  | let₁_left a => exact ⟨_, .let₁_left (embed a), fun _ => rfl⟩
  | let₁_right a => exact ⟨_, .let₁_right (embed a), fun _ => rfl⟩
  | pair_left a => exact ⟨_, .pair_left (embed a), fun _ => rfl⟩
  | pair_right a => exact ⟨_, .pair_right (embed a), fun _ => rfl⟩
  | let₂_left a => exact ⟨_, .let₂_left (embed a), fun _ => rfl⟩
  | let₂_right a => exact ⟨_, .let₂_right (embed a), fun _ => rfl⟩

variable {ε : Type r} [HasEff Φ ε]

/-- The existing syntax embedding is an arrow between the raw theory objects. -/
def rawEquationalHom (pureEff : ε) :
    rawEquationalObject (ν := ν) (Φ := Φ) pureEff ⟶
      LetCase.LocallyNameless.rawEquationalObject (ν := ν) (Φ := Φ) pureEff where
  toTranslation := rawTranslation
  preserves := embed_rawEquiv

/-- Directed theory translation, under exactly the primitive preservation obligation. -/
def rawRefinementHom (pureEff : ε) (R : RawRelation ν Φ)
    (Q : LetCase.LocallyNameless.RawRelation ν Φ)
    (hRQ : ∀ {n} {a b : Tm ν Φ n}, R a b → Q (embed a) (embed b)) :
    rawRefinementObject pureEff R ⟶ LetCase.LocallyNameless.rawRefinementObject pureEff Q where
  toTranslation := rawTranslation
  preserves := embed_rawRefinement hRQ

/-- The induced map uses the established inference-system morphism interface. -/
def rawEquationalInferenceMorphism (pureEff : ε) :=
  (rawEquationalHom (ν := ν) (Φ := Φ) pureEff).toInferenceMorphism

/-- Directed raw theories induce inference-system morphisms by the same translation. -/
def rawRefinementInferenceMorphism (pureEff : ε) (R : RawRelation ν Φ)
    (Q : LetCase.LocallyNameless.RawRelation ν Φ)
    (hRQ : ∀ {n} {a b : Tm ν Φ n}, R a b → Q (embed a) (embed b)) :=
  (rawRefinementHom pureEff R Q hRQ).toInferenceMorphism

variable {τ : Type w} [TypeFormers τ] [DecidableEq ν] [HasTy Φ τ]

/-- The same inclusion restricted to exact typing fibers. -/
def typedTranslation (Γ : Ctx ν τ) :
    (typedSyntax Φ Γ).Translation (LetCase.LocallyNameless.typedSyntax Φ Γ) where
  sort i := i
  term a := ⟨embed a.val, embed_hasType a.property⟩

/-- Translating a typed hole preserves its bound context and its result type. -/
theorem typedTranslation_contextual (Γ : Ctx ν τ) :
    (typedTranslation (Φ := Φ) Γ).Contextual := by
  intro i j c hc
  cases hc with
  | op => exact ⟨_, .op, fun _ => rfl⟩
  | let₁_left a => exact ⟨_, .let₁_left ⟨embed a.val, embed_hasType a.property⟩, fun _ => rfl⟩
  | let₁_right a => exact ⟨_, .let₁_right ⟨embed a.val, embed_hasType a.property⟩, fun _ => rfl⟩
  | pair_left a => exact ⟨_, .pair_left ⟨embed a.val, embed_hasType a.property⟩, fun _ => rfl⟩
  | pair_right a => exact ⟨_, .pair_right ⟨embed a.val, embed_hasType a.property⟩, fun _ => rfl⟩
  | let₂_left a => exact ⟨_, .let₂_left ⟨embed a.val, embed_hasType a.property⟩, fun _ => rfl⟩
  | let₂_right a => exact ⟨_, .let₂_right ⟨embed a.val, embed_hasType a.property⟩, fun _ => rfl⟩

/-- Exact typing fibers translate by the existing endpoint typing theorem. -/
def equationalHom (pureEff : ε) (Γ : Ctx ν τ) :
    equationalObject (Φ := Φ) pureEff Γ ⟶
      LetCase.LocallyNameless.equationalObject (Φ := Φ) pureEff Γ where
  toTranslation := typedTranslation Γ
  preserves := embed_equiv

def refinementHom (pureEff : ε) (Γ : Ctx ν τ)
    (R : TypedRelation ν Φ τ) (Q : LetCase.LocallyNameless.TypedRelation ν Φ τ)
    (hRQ : ∀ {n} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A},
      R β a b A → Q β (embed a) (embed b) A) :
    refinementObject pureEff Γ R ⟶ LetCase.LocallyNameless.refinementObject pureEff Γ Q where
  toTranslation := typedTranslation Γ
  preserves := embed_refinement hRQ

def equationalInferenceMorphism (pureEff : ε) (Γ : Ctx ν τ) :=
  (equationalHom (Φ := Φ) pureEff Γ).toInferenceMorphism

def refinementInferenceMorphism (pureEff : ε) (Γ : Ctx ν τ)
    (R : TypedRelation ν Φ τ) (Q : LetCase.LocallyNameless.TypedRelation ν Φ τ)
    (hRQ : ∀ {n} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A},
      R β a b A → Q β (embed a) (embed b) A) :=
  (refinementHom pureEff Γ R Q hRQ).toInferenceMorphism

end Silmaril.Isotope.Morphism.SeqCase

namespace Silmaril.Isotope.Morphism.CaseIter

open Silmaril.Logic.Metatheory CategoryTheory Silmaril.Logic.Metatheory
open LetCase.LocallyNameless

variable {ν : Type u} {Φ : Type v}

/-- The constructor inclusion as a translation of scope-indexed syntax. -/
def rawTranslation : (rawSyntax ν Φ).Translation (LetIter.LocallyNameless.rawSyntax ν Φ) where
  sort n := n
  term := embed

/-- Every source hole translates to the same constructor position in the target. -/
theorem rawTranslation_contextual : (rawTranslation (ν := ν) (Φ := Φ)).Contextual := by
  intro i j c hc
  cases hc with
  | op f => exact ⟨_, .op f, fun _ => rfl⟩
  | let₁_left a => exact ⟨_, .let₁_left (embed a), fun _ => rfl⟩
  | let₁_right a => exact ⟨_, .let₁_right (embed a), fun _ => rfl⟩
  | pair_left a => exact ⟨_, .pair_left (embed a), fun _ => rfl⟩
  | pair_right a => exact ⟨_, .pair_right (embed a), fun _ => rfl⟩
  | let₂_left a => exact ⟨_, .let₂_left (embed a), fun _ => rfl⟩
  | let₂_right a => exact ⟨_, .let₂_right (embed a), fun _ => rfl⟩
  | inl => exact ⟨_, .inl, fun _ => rfl⟩
  | inr => exact ⟨_, .inr, fun _ => rfl⟩
  | abort => exact ⟨_, .abort, fun _ => rfl⟩
  | case_scrutinee a b => exact ⟨_, .case_scrutinee (embed a) (embed b), fun _ => rfl⟩
  | case_left a b => exact ⟨_, .case_left (embed a) (embed b), fun _ => rfl⟩
  | case_right a b => exact ⟨_, .case_right (embed a) (embed b), fun _ => rfl⟩

variable {ε : Type r} [HasEff Φ ε]

/-- The existing syntax embedding is an arrow between the raw theory objects. -/
def rawEquationalHom (pureEff : ε) :
    rawEquationalObject (ν := ν) (Φ := Φ) pureEff ⟶
      LetIter.LocallyNameless.rawEquationalObject (ν := ν) (Φ := Φ) pureEff where
  toTranslation := rawTranslation
  preserves := embed_rawEquiv

/-- Directed theory translation, under exactly the primitive preservation obligation. -/
def rawRefinementHom (pureEff : ε) (R : RawRelation ν Φ)
    (Q : LetIter.LocallyNameless.RawRelation ν Φ)
    (hRQ : ∀ {n} {a b : Tm ν Φ n}, R a b → Q (embed a) (embed b)) :
    rawRefinementObject pureEff R ⟶ LetIter.LocallyNameless.rawRefinementObject pureEff Q where
  toTranslation := rawTranslation
  preserves := embed_rawRefinement hRQ

/-- The induced map uses the established inference-system morphism interface. -/
def rawEquationalInferenceMorphism (pureEff : ε) :=
  (rawEquationalHom (ν := ν) (Φ := Φ) pureEff).toInferenceMorphism

/-- Directed raw theories induce inference-system morphisms by the same translation. -/
def rawRefinementInferenceMorphism (pureEff : ε) (R : RawRelation ν Φ)
    (Q : LetIter.LocallyNameless.RawRelation ν Φ)
    (hRQ : ∀ {n} {a b : Tm ν Φ n}, R a b → Q (embed a) (embed b)) :=
  (rawRefinementHom pureEff R Q hRQ).toInferenceMorphism

variable {τ : Type w} [TypeFormers τ] [DecidableEq ν] [HasTy Φ τ]

/-- The same inclusion restricted to exact typing fibers. -/
def typedTranslation (Γ : Ctx ν τ) :
    (typedSyntax Φ Γ).Translation (LetIter.LocallyNameless.typedSyntax Φ Γ) where
  sort i := i
  term a := ⟨embed a.val, embed_hasType a.property⟩

/-- Translating a typed hole preserves its bound context and its result type. -/
theorem typedTranslation_contextual (Γ : Ctx ν τ) :
    (typedTranslation (Φ := Φ) Γ).Contextual := by
  intro i j c hc
  cases hc with
  | op => exact ⟨_, .op, fun _ => rfl⟩
  | let₁_left a => exact ⟨_, .let₁_left ⟨embed a.val, embed_hasType a.property⟩, fun _ => rfl⟩
  | let₁_right a => exact ⟨_, .let₁_right ⟨embed a.val, embed_hasType a.property⟩, fun _ => rfl⟩
  | pair_left a => exact ⟨_, .pair_left ⟨embed a.val, embed_hasType a.property⟩, fun _ => rfl⟩
  | pair_right a => exact ⟨_, .pair_right ⟨embed a.val, embed_hasType a.property⟩, fun _ => rfl⟩
  | let₂_left a => exact ⟨_, .let₂_left ⟨embed a.val, embed_hasType a.property⟩, fun _ => rfl⟩
  | let₂_right a => exact ⟨_, .let₂_right ⟨embed a.val, embed_hasType a.property⟩, fun _ => rfl⟩
  | inl => exact ⟨_, .inl, fun _ => rfl⟩
  | inr => exact ⟨_, .inr, fun _ => rfl⟩
  | abort => exact ⟨_, .abort, fun _ => rfl⟩
  | case_scrutinee a b =>
      exact ⟨_, .case_scrutinee ⟨embed a.val, embed_hasType a.property⟩
        ⟨embed b.val, embed_hasType b.property⟩, fun _ => rfl⟩
  | case_left a b =>
      exact ⟨_, .case_left ⟨embed a.val, embed_hasType a.property⟩
        ⟨embed b.val, embed_hasType b.property⟩, fun _ => rfl⟩
  | case_right a b =>
      exact ⟨_, .case_right ⟨embed a.val, embed_hasType a.property⟩
        ⟨embed b.val, embed_hasType b.property⟩, fun _ => rfl⟩

/-- Exact typing fibers translate by the existing endpoint typing theorem. -/
def equationalHom (pureEff : ε) (Γ : Ctx ν τ) :
    equationalObject (Φ := Φ) pureEff Γ ⟶
      LetIter.LocallyNameless.equationalObject (Φ := Φ) pureEff Γ where
  toTranslation := typedTranslation Γ
  preserves := embed_equiv

def refinementHom (pureEff : ε) (Γ : Ctx ν τ)
    (R : TypedRelation ν Φ τ) (Q : LetIter.LocallyNameless.TypedRelation ν Φ τ)
    (hRQ : ∀ {n} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A},
      R β a b A → Q β (embed a) (embed b) A) :
    refinementObject pureEff Γ R ⟶ LetIter.LocallyNameless.refinementObject pureEff Γ Q where
  toTranslation := typedTranslation Γ
  preserves := embed_refinement hRQ

def equationalInferenceMorphism (pureEff : ε) (Γ : Ctx ν τ) :=
  (equationalHom (Φ := Φ) pureEff Γ).toInferenceMorphism

def refinementInferenceMorphism (pureEff : ε) (Γ : Ctx ν τ)
    (R : TypedRelation ν Φ τ) (Q : LetIter.LocallyNameless.TypedRelation ν Φ τ)
    (hRQ : ∀ {n} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A},
      R β a b A → Q β (embed a) (embed b) A) :=
  (refinementHom pureEff Γ R Q hRQ).toInferenceMorphism

end Silmaril.Isotope.Morphism.CaseIter

namespace Silmaril.Isotope.Morphism.SeqIter

open Silmaril.Logic.Metatheory CategoryTheory Silmaril.Logic.Metatheory

variable {ν : Type u} {Φ : Type v} {ε : Type r} [HasEff Φ ε]

/-- The raw sequential inclusion follows the same categorical path through LetCase. -/
def rawEquationalHom (pureEff : ε) :
    LetSeq.LocallyNameless.rawEquationalObject (ν := ν) (Φ := Φ) pureEff ⟶
      LetIter.LocallyNameless.rawEquationalObject (ν := ν) (Φ := Φ) pureEff :=
  SeqCase.rawEquationalHom pureEff ≫ CaseIter.rawEquationalHom pureEff

def rawEquationalInferenceMorphism (pureEff : ε) :=
  (rawEquationalHom (ν := ν) (Φ := Φ) pureEff).toInferenceMorphism

/-- Raw inference translation commutes with composition of the two inclusions. -/
theorem raw_inference_composition (pureEff : ε) :
    rawEquationalInferenceMorphism (ν := ν) (Φ := Φ) pureEff =
      (CaseIter.rawEquationalInferenceMorphism (ν := ν) (Φ := Φ) pureEff).comp
        (SeqCase.rawEquationalInferenceMorphism (ν := ν) (Φ := Φ) pureEff) := rfl

variable {τ : Type w} [TypeFormers τ] [DecidableEq ν] [HasTy Φ τ]

/-- Sequential-to-iterative theory translation is the categorical composite. -/
def equationalHom (pureEff : ε) (Γ : Ctx ν τ) :
    LetSeq.LocallyNameless.equationalObject (Φ := Φ) pureEff Γ ⟶
      LetIter.LocallyNameless.equationalObject (Φ := Φ) pureEff Γ :=
  SeqCase.equationalHom (Φ := Φ) pureEff Γ ≫ CaseIter.equationalHom (Φ := Φ) pureEff Γ

def equationalInferenceMorphism (pureEff : ε) (Γ : Ctx ν τ) :=
  (equationalHom (Φ := Φ) pureEff Γ).toInferenceMorphism

/-- Translating equations in two stages gives precisely the composed inference map. -/
theorem inference_composition (pureEff : ε) (Γ : Ctx ν τ) :
    (equationalHom (Φ := Φ) pureEff Γ).toInferenceMorphism =
      (CaseIter.equationalInferenceMorphism (Φ := Φ) pureEff Γ).comp
        (SeqCase.equationalInferenceMorphism (Φ := Φ) pureEff Γ) := rfl

end Silmaril.Isotope.Morphism.SeqIter
