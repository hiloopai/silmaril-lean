module

public import Silmaril.Raw.SSA.Isotope.Institution.Refinement.Ordered

@[expose] public section

/-!
# Refinement theories as institutional theories

A compatible preorder `R` on the syntax of a presented signature (`TheoryModel.CompatiblePreorder`,
the form in which every Isotope refinement theory reaches its models, e.g.
`LetSeq.LocallyNameless.Models.refinementPreorder`) gives the set `sentencesOf R` of conjunctions
of inequations it derives. That set is *closed* in the refinement institution
(`sentencesOf_isClosed`, from the completeness theorem `TheoryModel.semanticallyRefines_iff`), so
`R` is a theory `theoryOf R` of the institution. Conversely every closed theory determines a
compatible preorder (`preorderOf`), and the two constructions are inverse
(`preorderOf_theoryOf_rel`, `theoryOf_preorderOf`): theories of the refinement institution over
`P` are exactly compatible preorders on the syntax of `P`.

The models of `theoryOf R` are the Isotope ordered models `TheoryModel.OrderedModels P.isInitial R`
(`modelsEquiv`), the initial model is the ordered quotient `TheoryModel.orderedQuotientModel`, and
theory morphisms are refinement-preserving signature morphisms whose reducts are the Isotope
restrictions `TheoryModel.OrderedModels.reindex` (`reduct_comp_toOrderedModels`).

## Main definitions

* `sentencesOf R`, `theoryOf R`, `preorderOf T`.
* `toOrderedModels`, `ofOrderedModels`, `modelsEquiv`; `initialModel`.
* `theoryHom`: a theory morphism from a sound signature morphism.

## Main results

* `mem_modelsOf_sentencesOf`, `sentencesOf_isClosed`.
* `entails_singleton_iff`: consequence of a single inequation is semantic refinement
  (`TheoryModel.SemanticallyRefines`), hence derivability (`entails_singleton_iff_rel`).
* `preorderOf_theoryOf_rel`, `theoryOf_preorderOf`.
* `reduct_comp_toOrderedModels`.
-/

namespace Silmaril.Isotope.Institution.Refinement

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution
open Silmaril.Logic.Metatheory.TheoryModel Silmaril.Logic.Metatheory.TheoryModel
open PSig

universe u v w

variable {P Q : PSig.{u, v, w}}

/-- The conjunctions of inequations derived by a compatible preorder on the syntax. -/
def sentencesOf (R : CompatiblePreorder P.syn) : Set (Sentence P) :=
  {s | ∀ φ ∈ s, R.Rel φ.2.1 φ.2.2}

theorem singleton_mem_sentencesOf (R : CompatiblePreorder P.syn) {i : P.Index}
    (a b : P.syn.Carrier i) : ([⟨i, a, b⟩] : Sentence P) ∈ sentencesOf R ↔ R.Rel a b := by
  constructor
  · intro h
    exact h ⟨i, a, b⟩ (List.mem_singleton_self _)
  · intro h φ hφ
    obtain rfl := List.mem_singleton.1 hφ
    exact h

/-- The models of `sentencesOf R` are exactly the ordered algebras validating `R`, i.e. the
objects of `TheoryModel.OrderedModels P.isInitial R`. -/
theorem mem_modelsOf_sentencesOf (R : CompatiblePreorder P.syn)
    (M : OrderedAlgebra.{u, v, w} P.sig) :
    M ∈ (institution.obj P).modelsOf (sentencesOf R) ↔
      ∀ {i : P.Index} {a b : P.syn.Carrier i}, R.Rel a b →
        P.eval M.toAlgebra a ≤ P.eval M.toAlgebra b := by
  constructor
  · intro hM i a b h
    exact hM ([⟨i, a, b⟩] : Sentence P) ((singleton_mem_sentencesOf R a b).2 h) ⟨i, a, b⟩
      (List.mem_singleton_self _)
  · intro h s hs φ hφ
    exact h (hs φ hφ)

/-- Consequence of a single inequation from `R` is semantic refinement in all ordered models of
`R` (`TheoryModel.SemanticallyRefines`). -/
theorem entails_singleton_iff (R : CompatiblePreorder P.syn) {i : P.Index}
    (a b : P.syn.Carrier i) :
    (institution.obj P).Entails (sentencesOf R) ([⟨i, a, b⟩] : Sentence P) ↔
      SemanticallyRefines P.isInitial R a b := by
  constructor
  · intro h M
    exact h M.algebra ((mem_modelsOf_sentencesOf R M.algebra).2 M.sound) ⟨i, a, b⟩
      (List.mem_singleton_self _)
  · intro h M hM φ hφ
    obtain rfl := List.mem_singleton.1 hφ
    exact h ⟨M, (mem_modelsOf_sentencesOf R M).1 hM⟩

/-- Consequence of a single inequation from `R` is derivability in `R`. A restatement of the
completeness theorem `TheoryModel.semanticallyRefines_iff`, and derived from it. -/
theorem entails_singleton_iff_rel (R : CompatiblePreorder P.syn) {i : P.Index}
    (a b : P.syn.Carrier i) :
    (institution.obj P).Entails (sentencesOf R) ([⟨i, a, b⟩] : Sentence P) ↔ R.Rel a b :=
  (entails_singleton_iff R a b).trans (semanticallyRefines_iff P.isInitial R a b)

/-- Refinement entailment is genuinely directed: an inequation derivable in one direction only is
entailed in that direction only (from `entails_singleton_iff_rel`). Together with the initial
model `initialModel` (whose order is exactly `R`, `initialModel_holds_iff`) this shows the
refinement theories are not vacuous. -/
theorem entails_strict (R : CompatiblePreorder P.syn) {i : P.Index} (a b : P.syn.Carrier i)
    (hab : R.Rel a b) (hba : ¬ R.Rel b a) :
    (institution.obj P).Entails (sentencesOf R) ([⟨i, a, b⟩] : Sentence P) ∧
      ¬ (institution.obj P).Entails (sentencesOf R) ([⟨i, b, a⟩] : Sentence P) :=
  ⟨(entails_singleton_iff_rel R a b).2 hab,
    fun h => hba ((entails_singleton_iff_rel R b a).1 h)⟩

/-- A compatible preorder is a closed set of sentences. Follows from the completeness theorem
`TheoryModel.semanticallyRefines_iff`. -/
theorem sentencesOf_isClosed (R : CompatiblePreorder P.syn) :
    (institution.obj P).IsClosed (sentencesOf R) := by
  refine Set.Subset.antisymm ?_ ((institution.obj P).subset_closure _)
  intro s hs φ hφ
  refine (semanticallyRefines_iff P.isInitial R φ.2.1 φ.2.2).1 (fun M => ?_)
  exact hs M.algebra ((mem_modelsOf_sentencesOf R M.algebra).2 M.sound) φ hφ

/-- The theory of the refinement institution presented by a compatible preorder. -/
def theoryOf (R : CompatiblePreorder P.syn) : Silmaril.Logic.Institution.Theory institution.{u, v, w} :=
  ⟨⟨P, sentencesOf R⟩, sentencesOf_isClosed R⟩

/-- A conjunction valid in every model of a closed theory belongs to it. -/
theorem mem_of_forall_holds (T : Silmaril.Logic.Institution.Theory institution.{u, v, w})
    {s : Sentence T.sig}
    (h : ∀ M : OrderedAlgebra.{u, v, w} T.sig.sig,
      M ∈ (institution.obj T.sig).modelsOf T.sentences → Sentence.Holds M s) :
    s ∈ T.sentences := by
  have hc : (institution.obj T.sig).closure T.sentences = T.sentences := T.isClosed
  rw [← hc]
  intro M hM
  exact h M hM

/-- The compatible preorder of a closed theory: `a ⊑ b` when the single inequation is in the
theory. -/
def preorderOf (T : Silmaril.Logic.Institution.Theory institution.{u, v, w}) :
    CompatiblePreorder T.sig.syn where
  Rel a b := ([⟨_, a, b⟩] : Sentence T.sig) ∈ T.sentences
  refl a := mem_of_forall_holds T fun M _ φ hφ => by
    obtain rfl := List.mem_singleton.1 hφ
    exact le_refl (T.sig.eval M.toAlgebra a)
  trans := fun {i} {a b c} h k => mem_of_forall_holds T fun M hM φ hφ => by
    obtain rfl := List.mem_singleton.1 hφ
    have h₁ : T.sig.eval M.toAlgebra a ≤ T.sig.eval M.toAlgebra b :=
      hM _ h ⟨i, a, b⟩ (List.mem_singleton_self _)
    have h₂ : T.sig.eval M.toAlgebra b ≤ T.sig.eval M.toAlgebra c :=
      hM _ k ⟨i, b, c⟩ (List.mem_singleton_self _)
    exact le_trans h₁ h₂
  compatible := fun {i} o a b h => mem_of_forall_holds T fun M hM φ hφ => by
    obtain rfl := List.mem_singleton.1 hφ
    show (T.sig.isInitial.to M.toAlgebra).map (T.sig.syn.op o a) ≤
      (T.sig.isInitial.to M.toAlgebra).map (T.sig.syn.op o b)
    rw [(T.sig.isInitial.to M.toAlgebra).comm, (T.sig.isInitial.to M.toAlgebra).comm]
    exact M.monotone_op o _ _ fun j =>
      hM _ (h j) ⟨_, a j, b j⟩ (List.mem_singleton_self _)

/-- `preorderOf` inverts `theoryOf` on relations. -/
theorem preorderOf_theoryOf_rel (R : CompatiblePreorder P.syn) {i : P.Index}
    (a b : P.syn.Carrier i) : (preorderOf (theoryOf R)).Rel a b ↔ R.Rel a b :=
  singleton_mem_sentencesOf R a b

/-- Every theory of the refinement institution is presented by its compatible preorder: a
conjunction belongs to a closed theory iff each conjunct does. -/
theorem theoryOf_preorderOf (T : Silmaril.Logic.Institution.Theory institution.{u, v, w}) :
    theoryOf (preorderOf T) = T := by
  obtain ⟨⟨P, S⟩, hS⟩ := T
  have key : sentencesOf (preorderOf ⟨⟨P, S⟩, hS⟩) = S := by
    ext s
    constructor
    · intro h
      refine mem_of_forall_holds ⟨⟨P, S⟩, hS⟩ fun M hM φ hφ => ?_
      obtain ⟨i, a, b⟩ := φ
      exact hM _ (h ⟨i, a, b⟩ hφ) ⟨i, a, b⟩ (List.mem_singleton_self _)
    · intro h φ hφ
      obtain ⟨i, a, b⟩ := φ
      refine mem_of_forall_holds ⟨⟨P, S⟩, hS⟩ fun M hM ψ hψ => ?_
      obtain rfl := List.mem_singleton.1 hψ
      exact hM s h _ hφ
  have hmk : ∀ (S' : Set (Sentence P)) (h' : (institution.obj P).IsClosed S'), S' = S →
      (⟨⟨P, S'⟩, h'⟩ : Silmaril.Logic.Institution.Theory institution.{u, v, w}) = ⟨⟨P, S⟩, hS⟩ := by
    rintro S' h' rfl
    rfl
  exact hmk _ _ key

/-! ### Models of refinement theories -/

/-- Models of the theory of `R`, as Isotope ordered models of `R`. -/
def toOrderedModels (R : CompatiblePreorder P.syn) :
    (theoryOf R).Models ⥤ OrderedModels P.isInitial R where
  obj M := ⟨M.obj, (mem_modelsOf_sentencesOf R M.obj).1 M.property⟩
  map f := f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Isotope ordered models of `R`, as models of the theory of `R`. -/
def ofOrderedModels (R : CompatiblePreorder P.syn) :
    OrderedModels P.isInitial R ⥤ (theoryOf R).Models where
  obj M := ⟨M.algebra, (mem_modelsOf_sentencesOf R M.algebra).2 M.sound⟩
  map f := ObjectProperty.homMk f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The model category of the theory of `R` is the Isotope category of ordered models
`TheoryModel.OrderedModels P.isInitial R`. -/
def modelsEquiv (R : CompatiblePreorder P.syn) :
    (theoryOf R).Models ≌ OrderedModels P.isInitial R :=
  CategoryTheory.Equivalence.mk (toOrderedModels R) (ofOrderedModels R)
    (NatIso.ofComponents (fun _ => Iso.refl _)) (NatIso.ofComponents (fun _ => Iso.refl _))

/-- The initial model of the theory of `R`: syntax quotiented by mutual refinement,
`TheoryModel.orderedQuotientModel`. -/
noncomputable def initialModel (R : CompatiblePreorder P.syn) : (theoryOf R).Models :=
  (ofOrderedModels R).obj (orderedQuotientModel P.isInitial R)

/-- The ordered quotient is initial among models of the theory of `R`. From
`TheoryModel.orderedQuotientModelDesc` and `TheoryModel.orderedQuotientIsInitial`. -/
noncomputable def initialModelIsInitial (R : CompatiblePreorder P.syn) :
    IsInitial (initialModel R) :=
  IsInitial.ofUniqueHom
    (fun M => ObjectProperty.homMk
      (orderedQuotientModelDesc P.isInitial R ((toOrderedModels R).obj M)))
    (fun M _ => ObjectProperty.hom_ext _
      ((orderedQuotientIsInitial P.isInitial R).hom_ext (Y := (toOrderedModels R).obj M) _ _))

/-- In the initial model the order is exactly derivability: a restatement of
`TheoryModel.orderedQuotient_le_iff`, and derived from it. -/
theorem initialModel_holds_iff (R : CompatiblePreorder P.syn) {i : P.Index}
    (a b : P.syn.Carrier i) :
    Pair.Holds (orderedQuotient R) ⟨i, a, b⟩ ↔ R.Rel a b := by
  have hq : P.isInitial.to (orderedQuotient R).toAlgebra = quotientMap R.equationalCore :=
    P.isInitial.hom_ext _ _
  show (P.isInitial.to (orderedQuotient R).toAlgebra).map a ≤
    (P.isInitial.to (orderedQuotient R).toAlgebra).map b ↔ R.Rel a b
  rw [hq]
  exact orderedQuotient_le_iff R a b

/-! ### Theory morphisms -/

/-- A signature morphism whose syntax translation carries `R`-refinements to `R'`-refinements is
a morphism of refinement theories. -/
def theoryHom (f : P ⟶ Q) {R : CompatiblePreorder P.syn} {R' : CompatiblePreorder Q.syn}
    (sound : ∀ {i : P.Index} {a b : P.syn.Carrier i},
      R.Rel a b → R'.Rel ((translate f).map a) ((translate f).map b)) :
    theoryOf R ⟶ theoryOf R' :=
  Silmaril.Logic.Institution.Theory.homMk f (by
    intro s hs φ hφ
    obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.1 hφ
    exact sound (hs ψ hψ))

/-- The reduct along `theoryHom f sound` is the Isotope ordered-model restriction
`TheoryModel.OrderedModels.reindex`. -/
theorem reduct_comp_toOrderedModels (f : P ⟶ Q) {R : CompatiblePreorder P.syn}
    {R' : CompatiblePreorder Q.syn}
    (sound : ∀ {i : P.Index} {a b : P.syn.Carrier i},
      R.Rel a b → R'.Rel ((translate f).map a) ((translate f).map b)) :
    Silmaril.Logic.Institution.Theory.reduct (theoryHom f sound) ⋙ toOrderedModels R =
      toOrderedModels R' ⋙
        OrderedModels.reindex (toSig f) P.isInitial Q.isInitial (translate f) sound :=
  rfl

end Silmaril.Isotope.Institution.Refinement
