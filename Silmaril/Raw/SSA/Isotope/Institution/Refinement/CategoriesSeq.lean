module

public import Silmaril.Raw.SSA.Isotope.Institution.Refinement.Comorphism
public import Silmaril.Raw.SSA.Isotope.Institution.Refinement.ProofRelevant
public import Silmaril.Raw.SSA.Isotope.LetSeq.ProofRelevant.LocallyNameless.RefinementCategories

@[expose] public section

/-!
# Proof-relevant let-seq refinement categories, institutionally

`LetSeq.ProofRelevant.LocallyNameless.RefinementCategories` organizes the generated contextual
refinement theories of proof-relevant let-seq into categories: primitive extension is monotone
(`refinementTheory_mono`, `refinementTheoryFunctor`), every refinement theory contains the typed
equations (`equations_le_refinement`), the rewrite-free theory is the equational theory
(`empty_refinementTheory`), and the generated theory is least among contextual theories
validating the equations and the primitive rewrites (`refinementTheory_le_iff`).

This file restates each of these in the refinement institution, over the presented signature
`prSeqPSig Φ Γ`, and derives each restatement from its source lemma:

* `prSeqTheoryMono`, `prSeqTheoryFunctor`: from `refinementTheory_mono` and
  `refinementTheoryFunctor`; the morphisms lie over the identity signature morphism.
* `prSeq_toRef_mem`: from `equations_le_refinement`; the comorphism image of a typed equation
  lies in every proof-relevant let-seq theory.
* `prSeqTheory_empty`, `prSeqTheory_empty_sentences`: from `empty_refinementTheory`; the
  rewrite-free theory is the refinement theory of the typed equational congruence, i.e. the
  closure of the comorphism image of the equational theory (`closure_image_toRef`).
* `prSeqTheory_subset_iff`: from `refinementTheory_le_iff`; the theory of `R` is the least
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

/-- Primitive extension `R ≤ S` gives a morphism of proof-relevant let-seq refinement theories
over the identity signature morphism. Soundness is
`LetSeq.ProofRelevant.LocallyNameless.refinementTheory_mono`. -/
def prSeqTheoryMono (pureEff : ε) (Γ : Ctx ν τ)
    {R S : LetSeq.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ} (h : R ≤ S) :
    prSeqTheory pureEff Γ R ⟶ prSeqTheory pureEff Γ S :=
  theoryHom (𝟙 (prSeqPSig Φ Γ)) (fun {_ a b} hab => by
    rw [translate_id_map (prSeqPSig Φ Γ) a, translate_id_map (prSeqPSig Φ Γ) b]
    exact LetSeq.ProofRelevant.LocallyNameless.refinementTheory_mono (pureEff := pureEff) h hab)

/-- The underlying signature morphism of `prSeqTheoryMono` is the identity. -/
theorem prSeqTheoryMono_sig (pureEff : ε) (Γ : Ctx ν τ)
    {R S : LetSeq.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ} (h : R ≤ S) :
    (prSeqTheoryMono pureEff Γ h).hom.sig = 𝟙 (prSeqPSig Φ Γ) :=
  rfl

/-- The institutional form of `LetSeq.ProofRelevant.LocallyNameless.refinementTheoryFunctor`:
primitive rewrite theories, ordered by inclusion, map functorially to theories of the
refinement institution. -/
def prSeqTheoryFunctor (pureEff : ε) (Γ : Ctx ν τ) :
    LetSeq.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ ⥤
      Silmaril.Logic.Institution.Theory institution.{u, _, _} where
  obj R := prSeqTheory pureEff Γ R
  map f := prSeqTheoryMono pureEff Γ (CategoryTheory.leOfHom f)
  map_id _ := Silmaril.Logic.Institution.Theory.hom_ext rfl
  map_comp _ _ := Silmaril.Logic.Institution.Theory.hom_ext (Category.id_comp _).symm

/-- The comorphism image `a ⊑ b ∧ b ⊑ a` of a typed equation lies in every proof-relevant
let-seq refinement theory. From `LetSeq.ProofRelevant.LocallyNameless.equations_le_refinement`. -/
theorem prSeq_toRef_mem (pureEff : ε) (Γ : Ctx ν τ)
    (R : LetSeq.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ) {i : TypingIndex τ}
    (a b : LetSeq.ProofRelevant.LocallyNameless.Models.Carrier Φ Γ i)
    (h : LetSeq.ProofRelevant.LocallyNameless.TypedEquiv.Related pureEff Γ a.2 b.2) :
    Pair.toRef (⟨i, a, b⟩ : Pair (prSeqPSig Φ Γ)) ∈ (prSeqTheory pureEff Γ R).sentences :=
  (toRef_mem_sentencesOf_iff (P := prSeqPSig Φ Γ)
      (LetSeq.ProofRelevant.LocallyNameless.Models.refinementPreorder pureEff Γ R) ⟨i, a, b⟩).2
    ⟨LetSeq.ProofRelevant.LocallyNameless.equations_le_refinement (pureEff := pureEff) R h,
      LetSeq.ProofRelevant.LocallyNameless.equations_le_refinement (pureEff := pureEff) R
        (h.map LetSeq.ProofRelevant.LocallyNameless.TypedEquiv.Deriv.symm)⟩

/-- The rewrite-free proof-relevant let-seq theory is the refinement theory of the typed
equational congruence (read as a symmetric preorder). From
`LetSeq.ProofRelevant.LocallyNameless.empty_refinementTheory`. -/
theorem prSeqTheory_empty (pureEff : ε) (Γ : Ctx ν τ) :
    prSeqTheory pureEff Γ
        (LetSeq.ProofRelevant.LocallyNameless.Refinement.EmptyTheory (Φ := Φ) (Γ := Γ)) =
      theoryOf (P := prSeqPSig Φ Γ)
        (congruencePreorder
          (LetSeq.ProofRelevant.LocallyNameless.Models.equationCongruence pureEff Γ)) := by
  unfold prSeqTheory LetSeq.ProofRelevant.LocallyNameless.Models.refinementPreorder
  rw [LetSeq.ProofRelevant.LocallyNameless.empty_refinementTheory]
  rfl

/-- The rewrite-free proof-relevant let-seq theory is generated by the comorphism image of the
typed equations. From `prSeqTheory_empty` and `closure_image_toRef`. -/
theorem prSeqTheory_empty_sentences (pureEff : ε) (Γ : Ctx ν τ) :
    (prSeqTheory pureEff Γ
        (LetSeq.ProofRelevant.LocallyNameless.Refinement.EmptyTheory (Φ := Φ) (Γ := Γ))).sentences =
      (institution.obj (prSeqPSig Φ Γ)).closure
        (Pair.toRef '' eqSentencesOf (P := prSeqPSig Φ Γ)
          (LetSeq.ProofRelevant.LocallyNameless.Models.equationCongruence pureEff Γ)) := by
  have h := congrArg (fun T : Silmaril.Logic.Institution.Theory institution.{u, _, _} => T.obj)
    (prSeqTheory_empty (Φ := Φ) pureEff Γ)
  rw [closure_image_toRef]
  exact eq_of_heq (Presentation.mk.inj h).2

/-- A closed set of sentences over `prSeqPSig Φ Γ`, as a theory of the refinement institution. -/
private abbrev prSeqClosedInstTheory (Γ : Ctx ν τ) (S : Set (Sentence (prSeqPSig Φ Γ)))
    (hS : (institution.obj (prSeqPSig Φ Γ)).IsClosed S) :
    Silmaril.Logic.Institution.Theory institution.{u, _, _} :=
  ⟨⟨prSeqPSig Φ Γ, S⟩, hS⟩

open LetSeq.ProofRelevant.LocallyNameless.Models (Operation) in
/-- A closed set of sentences over `prSeqPSig Φ Γ` is a contextual refinement theory on the
proof-relevant typed syntax: its preorder `preorderOf` is compatible with every operation, hence
with every typed constructor context. -/
private def prSeqClosedTheory (Γ : Ctx ν τ) (S : Set (Sentence (prSeqPSig Φ Γ)))
    (hS : (institution.obj (prSeqPSig Φ Γ)).IsClosed S) :
    RefinementTheory (LetSeq.ProofRelevant.LocallyNameless.typedSyntax Φ Γ) where
  Rel a b := (preorderOf (prSeqClosedInstTheory Γ S hS)).Rel a b
  refl := (preorderOf (prSeqClosedInstTheory Γ S hS)).refl
  trans := (preorderOf (prSeqClosedInstTheory Γ S hS)).trans
  congr := fun {_ _} {a b} c hc h => by
    generalize preorderOf (prSeqClosedInstTheory Γ S hS) = Q at h ⊢
    cases hc with
    | @op n β f =>
      exact Q.compatible (Operation.op (β := β) f) (fun _ => a) (fun _ => b) (fun _ => h)
    | @let₁_left n β A B t =>
      exact Q.compatible (Operation.let₁ (β := β) A B) (Fin.cases a fun _ => t)
        (Fin.cases b fun _ => t)
        (Fin.cases h fun _ => Q.refl t)
    | @let₁_right n β A B t =>
      exact Q.compatible (Operation.let₁ (β := β) A B) (Fin.cases t fun _ => a)
        (Fin.cases t fun _ => b)
        (Fin.cases (Q.refl t) fun _ => h)
    | @pair_left n β A B t =>
      exact Q.compatible (Operation.pair (β := β) A B) (Fin.cases a fun _ => t)
        (Fin.cases b fun _ => t)
        (Fin.cases h fun _ => Q.refl t)
    | @pair_right n β A B t =>
      exact Q.compatible (Operation.pair (β := β) A B) (Fin.cases t fun _ => a)
        (Fin.cases t fun _ => b)
        (Fin.cases (Q.refl t) fun _ => h)
    | @let₂_left n β A B C t =>
      exact Q.compatible (Operation.let₂ (β := β) A B C) (Fin.cases a fun _ => t)
        (Fin.cases b fun _ => t) (Fin.cases h fun _ => Q.refl t)
    | @let₂_right n β A B C t =>
      exact Q.compatible (Operation.let₂ (β := β) A B C) (Fin.cases t fun _ => a)
        (Fin.cases t fun _ => b) (Fin.cases (Q.refl t) fun _ => h)
    | @sub n β A B d =>
      exact Q.compatible (Operation.sub (β := β) d) (fun _ => a) (fun _ => b) (fun _ => h)

/-- The proof-relevant let-seq theory of `R` is the least closed set of sentences containing the
typed equations and the primitive rewrites of `R`. The institutional form of
`LetSeq.ProofRelevant.LocallyNameless.refinementTheory_le_iff`, and derived from it. -/
theorem prSeqTheory_subset_iff (pureEff : ε) (Γ : Ctx ν τ)
    (R : LetSeq.ProofRelevant.LocallyNameless.Refinement.Theory (Φ := Φ) Γ)
    (S : Set (Sentence (prSeqPSig Φ Γ))) (hS : (institution.obj (prSeqPSig Φ Γ)).IsClosed S) :
    (prSeqTheory pureEff Γ R).sentences ⊆ S ↔
      (∀ {i : TypingIndex τ} (a b : LetSeq.ProofRelevant.LocallyNameless.Models.Carrier Φ Γ i),
        LetSeq.ProofRelevant.LocallyNameless.TypedEquiv.Related pureEff Γ a.2 b.2 →
          ([⟨i, a, b⟩] : Sentence (prSeqPSig Φ Γ)) ∈ S) ∧
      (∀ {n : Nat} {β : BoundCtx τ n} {a b : LetSeq.LocallyNameless.Tm ν Φ n} {A : τ}
        {ha : LetSeq.ProofRelevant.LocallyNameless.HasType Φ Γ β a A}
        {hb : LetSeq.ProofRelevant.LocallyNameless.HasType Φ Γ β b A},
        R.rel ha hb →
          ([⟨⟨n, β, A⟩, ⟨a, ha⟩, ⟨b, hb⟩⟩] : Sentence (prSeqPSig Φ Γ)) ∈ S) := by
  constructor
  · intro hsub
    obtain ⟨heq, hR⟩ := (LetSeq.ProofRelevant.LocallyNameless.refinementTheory_le_iff
      (pureEff := pureEff) (LetSeq.ProofRelevant.LocallyNameless.refinementTheory pureEff Γ R)
      R).1 fun h => h
    exact ⟨fun a b h => hsub ((singleton_mem_sentencesOf (P := prSeqPSig Φ Γ)
        (LetSeq.ProofRelevant.LocallyNameless.Models.refinementPreorder pureEff Γ R) a b).2
          (heq h)),
      fun h => hsub ((singleton_mem_sentencesOf (P := prSeqPSig Φ Γ)
        (LetSeq.ProofRelevant.LocallyNameless.Models.refinementPreorder pureEff Γ R) _ _).2
          (hR h))⟩
  · rintro ⟨h₁, h₂⟩
    have hle : LetSeq.ProofRelevant.LocallyNameless.refinementTheory pureEff Γ R ≤
        prSeqClosedTheory Γ S hS := (LetSeq.ProofRelevant.LocallyNameless.refinementTheory_le_iff
      (pureEff := pureEff) (prSeqClosedTheory Γ S hS) R).2
        ⟨fun {_ a b} h => h₁ a b h, fun h => h₂ h⟩
    intro s hs
    refine mem_of_forall_holds (prSeqClosedInstTheory Γ S hS) fun M hM φ hφ => ?_
    obtain ⟨i, a, b⟩ := φ
    exact hM _ (hle (hs ⟨i, a, b⟩ hφ)) ⟨i, a, b⟩ (List.mem_singleton_self _)

end Silmaril.Isotope.Institution.Refinement
