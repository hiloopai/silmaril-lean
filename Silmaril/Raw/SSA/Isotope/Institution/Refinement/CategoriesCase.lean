module

public import Silmaril.Raw.SSA.Isotope.Institution.Refinement.Comorphism
public import Silmaril.Raw.SSA.Isotope.Institution.Refinement.ProofRelevant
public import Silmaril.Raw.SSA.Isotope.LetCase.ProofRelevant.LocallyNameless.RefinementCategories

@[expose] public section

/-!
# Proof-relevant let-case refinement categories, institutionally

`LetCase.ProofRelevant.LocallyNameless.RefinementCategories` organizes the generated contextual
refinement theories of proof-relevant let-case into categories: primitive extension is monotone
(`refinementTheory_mono`, `refinementTheoryFunctor`), every refinement theory contains the typed
equations (`equations_le_refinement`), the rewrite-free theory is the equational theory
(`empty_refinementTheory`), and the generated theory is least among contextual theories
validating the equations and the primitive rewrites (`refinementTheory_le_iff`).

This file restates each of these in the refinement institution, over the presented signature
`prCasePSig Φ Γ`, and derives each restatement from its source lemma:

* `prCaseTheoryMono`, `prCaseTheoryFunctor`: from `refinementTheory_mono` and
  `refinementTheoryFunctor`; the morphisms lie over the identity signature morphism.
* `prCase_toRef_mem`: from `equations_le_refinement`; the comorphism image of a typed equation
  lies in every proof-relevant let-case theory.
* `prCaseTheory_empty`, `prCaseTheory_empty_sentences`: from `empty_refinementTheory`; the
  rewrite-free theory is the refinement theory of the typed equational congruence, i.e. the
  closure of the comorphism image of the equational theory (`closure_image_toRef`).
* `prCaseTheory_subset_iff`: from `refinementTheory_le_iff`; the theory of `R` is the least
  closed set of sentences containing the typed equations and the primitive rewrites of `R`.
-/

namespace Silmaril.Isotope.Institution.Refinement

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution
open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel
open Silmaril.Isotope.Theory
open PSig

universe u v w r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable {ν : Type w} [DecidableEq ν] {Φ : Type v} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε]

/-- Primitive extension `R ≤ S` gives a morphism of proof-relevant let-case refinement theories
over the identity signature morphism. Soundness is
`LetCase.ProofRelevant.LocallyNameless.refinementTheory_mono`. -/
def prCaseTheoryMono (pureEff : ε) (Γ : Ctx ν τ)
    {R S : LetCase.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ} (h : R ≤ S) :
    prCaseTheory pureEff Γ R ⟶ prCaseTheory pureEff Γ S :=
  theoryHom (𝟙 (prCasePSig Φ Γ)) (fun {_ _ _} hab => by
    rw [translate_id_map, translate_id_map]
    exact LetCase.ProofRelevant.LocallyNameless.refinementTheory_mono (pureEff := pureEff) h hab)

/-- The underlying signature morphism of `prCaseTheoryMono` is the identity. -/
theorem prCaseTheoryMono_sig (pureEff : ε) (Γ : Ctx ν τ)
    {R S : LetCase.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ} (h : R ≤ S) :
    (prCaseTheoryMono pureEff Γ h).hom.sig = 𝟙 (prCasePSig Φ Γ) :=
  rfl

/-- The institutional form of `LetCase.ProofRelevant.LocallyNameless.refinementTheoryFunctor`:
primitive rewrite theories, ordered by inclusion, map functorially to theories of the
refinement institution. -/
def prCaseTheoryFunctor (pureEff : ε) (Γ : Ctx ν τ) :
    LetCase.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ ⥤
      Silmaril.Logic.Institution.Theory institution.{u, _, _} where
  obj R := prCaseTheory pureEff Γ R
  map f := prCaseTheoryMono pureEff Γ (CategoryTheory.leOfHom f)
  map_id _ := Silmaril.Logic.Institution.Theory.hom_ext rfl
  map_comp _ _ := Silmaril.Logic.Institution.Theory.hom_ext (Category.comp_id _).symm

/-- The comorphism image `a ⊑ b ∧ b ⊑ a` of a typed equation lies in every proof-relevant
let-case refinement theory. From `LetCase.ProofRelevant.LocallyNameless.equations_le_refinement`. -/
theorem prCase_toRef_mem (pureEff : ε) (Γ : Ctx ν τ)
    (R : LetCase.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ) {i : TypingIndex τ}
    (a b : LetCase.ProofRelevant.LocallyNameless.Models.Carrier Φ Γ i)
    (h : LetCase.ProofRelevant.LocallyNameless.TypedEquiv.Related pureEff Γ a.2 b.2) :
    Pair.toRef (⟨i, a, b⟩ : Pair (prCasePSig Φ Γ)) ∈ (prCaseTheory pureEff Γ R).sentences :=
  (toRef_mem_sentencesOf_iff _ _).2
    ⟨LetCase.ProofRelevant.LocallyNameless.equations_le_refinement (pureEff := pureEff) R h,
      LetCase.ProofRelevant.LocallyNameless.equations_le_refinement (pureEff := pureEff) R
        ((LetCase.ProofRelevant.LocallyNameless.equationalTheory pureEff Γ).symm h)⟩

/-- The rewrite-free generated preorder is the typed equational congruence, read as a symmetric
preorder. From `LetCase.ProofRelevant.LocallyNameless.empty_refinementTheory`. -/
theorem prCasePreorder_empty (pureEff : ε) (Γ : Ctx ν τ) :
    LetCase.ProofRelevant.LocallyNameless.Models.refinementPreorder pureEff Γ
        (LetCase.ProofRelevant.LocallyNameless.Refinement.EmptyTheory (Φ := Φ) (Γ := Γ)) =
      congruencePreorder
        (LetCase.ProofRelevant.LocallyNameless.Models.equationCongruence pureEff Γ) := by
  unfold LetCase.ProofRelevant.LocallyNameless.Models.refinementPreorder
  rw [LetCase.ProofRelevant.LocallyNameless.empty_refinementTheory]
  rfl

/-- The rewrite-free proof-relevant let-case theory is the refinement theory of the typed
equational congruence (read as a symmetric preorder). From
`LetCase.ProofRelevant.LocallyNameless.empty_refinementTheory`. -/
theorem prCaseTheory_empty (pureEff : ε) (Γ : Ctx ν τ) :
    prCaseTheory pureEff Γ
        (LetCase.ProofRelevant.LocallyNameless.Refinement.EmptyTheory (Φ := Φ) (Γ := Γ)) =
      theoryOf (P := prCasePSig Φ Γ)
        (congruencePreorder
          (LetCase.ProofRelevant.LocallyNameless.Models.equationCongruence pureEff Γ)) := by
  rw [prCaseTheory, prCasePreorder_empty]

/-- The rewrite-free proof-relevant let-case theory is generated by the comorphism image of the
typed equations. From `prCasePreorder_empty` (the preorder form of `prCaseTheory_empty`) and
`closure_image_toRef`. -/
theorem prCaseTheory_empty_sentences (pureEff : ε) (Γ : Ctx ν τ) :
    (prCaseTheory pureEff Γ
        (LetCase.ProofRelevant.LocallyNameless.Refinement.EmptyTheory (Φ := Φ) (Γ := Γ))).sentences =
      (institution.obj (prCasePSig Φ Γ)).closure
        (Pair.toRef '' eqSentencesOf (P := prCasePSig Φ Γ)
          (LetCase.ProofRelevant.LocallyNameless.Models.equationCongruence pureEff Γ)) := by
  show sentencesOf _ = _
  rw [closure_image_toRef, prCasePreorder_empty]

/-- A compatible preorder on proof-relevant let-case syntax is contextual: every typed one-hole
context is an operation with the remaining arguments fixed. This reverses
`LetCase.ProofRelevant.LocallyNameless.Models.theoryPrecongruence`. -/
def prCaseContextual (Γ : Ctx ν τ)
    (Q : CompatiblePreorder (LetCase.ProofRelevant.LocallyNameless.Models.syntaxAlgebra Φ Γ)) :
    RefinementTheory (LetCase.ProofRelevant.LocallyNameless.typedSyntax Φ Γ) where
  Rel := Q.Rel
  refl := Q.refl
  trans := Q.trans
  congr := fun {_ _} {x y} _ hc h => by
    cases hc with
    | @op n β f =>
      exact Q.compatible (LetCase.ProofRelevant.LocallyNameless.Models.Operation.op (Γ := Γ) (β := β) f)
        (fun _ => x) (fun _ => y) (fun _ => h)
    | @let₁_left n β A B b =>
      exact Q.compatible (LetCase.ProofRelevant.LocallyNameless.Models.Operation.let₁ (Γ := Γ) (β := β) A B)
        (fun j => j.cases x fun _ => b) (fun j => j.cases y fun _ => b)
        (fun j => j.cases h fun _ => Q.refl b)
    | @let₁_right n β A B a =>
      exact Q.compatible (LetCase.ProofRelevant.LocallyNameless.Models.Operation.let₁ (Γ := Γ) (β := β) A B)
        (fun j => j.cases a fun _ => x) (fun j => j.cases a fun _ => y)
        (fun j => j.cases (Q.refl a) fun _ => h)
    | @pair_left n β A B b =>
      exact Q.compatible (LetCase.ProofRelevant.LocallyNameless.Models.Operation.pair (Γ := Γ) (β := β) A B)
        (fun j => j.cases x fun _ => b) (fun j => j.cases y fun _ => b)
        (fun j => j.cases h fun _ => Q.refl b)
    | @pair_right n β A B a =>
      exact Q.compatible (LetCase.ProofRelevant.LocallyNameless.Models.Operation.pair (Γ := Γ) (β := β) A B)
        (fun j => j.cases a fun _ => x) (fun j => j.cases a fun _ => y)
        (fun j => j.cases (Q.refl a) fun _ => h)
    | @let₂_left n β A B C b =>
      exact Q.compatible (LetCase.ProofRelevant.LocallyNameless.Models.Operation.let₂ (Γ := Γ) (β := β) A B C)
        (fun j => j.cases x fun _ => b) (fun j => j.cases y fun _ => b)
        (fun j => j.cases h fun _ => Q.refl b)
    | @let₂_right n β A B C a =>
      exact Q.compatible (LetCase.ProofRelevant.LocallyNameless.Models.Operation.let₂ (Γ := Γ) (β := β) A B C)
        (fun j => j.cases a fun _ => x) (fun j => j.cases a fun _ => y)
        (fun j => j.cases (Q.refl a) fun _ => h)
    | @inl n β A B =>
      exact Q.compatible (LetCase.ProofRelevant.LocallyNameless.Models.Operation.inl (Γ := Γ) (β := β) A B)
        (fun _ => x) (fun _ => y) (fun _ => h)
    | @inr n β A B =>
      exact Q.compatible (LetCase.ProofRelevant.LocallyNameless.Models.Operation.inr (Γ := Γ) (β := β) A B)
        (fun _ => x) (fun _ => y) (fun _ => h)
    | @case_scrutinee n β A B C l r =>
      exact Q.compatible (LetCase.ProofRelevant.LocallyNameless.Models.Operation.case (Γ := Γ) (β := β) A B C)
        (fun j => j.cases x fun j => j.cases l fun _ => r)
        (fun j => j.cases y fun j => j.cases l fun _ => r)
        (fun j => j.cases h fun j => j.cases (Q.refl l) fun _ => Q.refl r)
    | @case_left n β A B C e r =>
      exact Q.compatible (LetCase.ProofRelevant.LocallyNameless.Models.Operation.case (Γ := Γ) (β := β) A B C)
        (fun j => j.cases e fun j => j.cases x fun _ => r)
        (fun j => j.cases e fun j => j.cases y fun _ => r)
        (fun j => j.cases (Q.refl e) fun j => j.cases h fun _ => Q.refl r)
    | @case_right n β A B C e l =>
      exact Q.compatible (LetCase.ProofRelevant.LocallyNameless.Models.Operation.case (Γ := Γ) (β := β) A B C)
        (fun j => j.cases e fun j => j.cases l fun _ => x)
        (fun j => j.cases e fun j => j.cases l fun _ => y)
        (fun j => j.cases (Q.refl e) fun j => j.cases (Q.refl l) fun _ => h)
    | @abort n β C =>
      exact Q.compatible (LetCase.ProofRelevant.LocallyNameless.Models.Operation.abort (Γ := Γ) (β := β) C)
        (fun _ => x) (fun _ => y) (fun _ => h)
    | @sub n β A B d =>
      exact Q.compatible (LetCase.ProofRelevant.LocallyNameless.Models.Operation.sub (Γ := Γ) (β := β) d)
        (fun _ => x) (fun _ => y) (fun _ => h)

/-- The proof-relevant let-case theory of `R` is the least closed set of sentences containing the
typed equations and the primitive rewrites of `R`. The institutional form of
`LetCase.ProofRelevant.LocallyNameless.refinementTheory_le_iff`, and derived from it. -/
theorem prCaseTheory_subset_iff (pureEff : ε) (Γ : Ctx ν τ)
    (R : LetCase.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ)
    (S : Set (Sentence (prCasePSig Φ Γ))) (hS : (institution.obj (prCasePSig Φ Γ)).IsClosed S) :
    (prCaseTheory pureEff Γ R).sentences ⊆ S ↔
      (∀ {i : TypingIndex τ} (a b : LetCase.ProofRelevant.LocallyNameless.Models.Carrier Φ Γ i),
        LetCase.ProofRelevant.LocallyNameless.TypedEquiv.Related pureEff Γ a.2 b.2 →
          ([⟨i, a, b⟩] : Sentence (prCasePSig Φ Γ)) ∈ S) ∧
      (∀ {n : Nat} {β : BoundCtx τ n} {a b : LetCase.LocallyNameless.Tm ν Φ n} {A : τ}
        {ha : LetCase.ProofRelevant.LocallyNameless.HasType Φ Γ β a A}
        {hb : LetCase.ProofRelevant.LocallyNameless.HasType Φ Γ β b A},
        R.rel ha hb →
          ([⟨⟨n, β, A⟩, ⟨a, ha⟩, ⟨b, hb⟩⟩] : Sentence (prCasePSig Φ Γ)) ∈ S) := by
  let T : Silmaril.Logic.Institution.Theory institution.{u, _, _} := ⟨⟨prCasePSig Φ Γ, S⟩, hS⟩
  let Q := prCaseContextual Γ (preorderOf T)
  have hsub : ∀ s : Sentence (prCasePSig Φ Γ),
      (∀ φ ∈ s, ([φ] : Sentence (prCasePSig Φ Γ)) ∈ S) → s ∈ S := by
    intro s h
    refine mem_of_forall_holds T fun M hM φ hφ => ?_
    exact hM _ (h φ hφ) φ (List.mem_singleton_self _)
  have hle := LetCase.ProofRelevant.LocallyNameless.refinementTheory_le_iff (pureEff := pureEff)
    (Φ := Φ) (Γ := Γ)
  constructor
  · intro h
    obtain ⟨heq, hR⟩ := (hle (LetCase.ProofRelevant.LocallyNameless.refinementTheory pureEff Γ R)
      R).1 (fun h => h)
    let P := LetCase.ProofRelevant.LocallyNameless.Models.refinementPreorder pureEff Γ R
    refine ⟨fun a b hab => h ((singleton_mem_sentencesOf (P := prCasePSig Φ Γ) P a b).2
      (heq hab)), fun hr => h ((singleton_mem_sentencesOf (P := prCasePSig Φ Γ) P _ _).2
        (hR hr))⟩
  · rintro ⟨heq, hR⟩ s hs
    have hQ : LetCase.ProofRelevant.LocallyNameless.refinementTheory pureEff Γ R ≤ Q :=
      (hle Q R).2 ⟨fun {_ a b} hab => heq a b hab, fun hr => hR hr⟩
    refine hsub s fun φ hφ => ?_
    obtain ⟨i, a, b⟩ := φ
    exact hQ (hs ⟨i, a, b⟩ hφ)

end Silmaril.Isotope.Institution.Refinement
