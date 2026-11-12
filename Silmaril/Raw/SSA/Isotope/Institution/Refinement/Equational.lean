module

public import Silmaril.Raw.SSA.Isotope.Institution.Refinement.Ordered

@[expose] public section

/-!
# The equational institution of presented signatures

The comparison partner of the refinement institution: over a presented signature `P`, sentences
are typed equations `a = b` between syntax elements (`Pair P`), models are algebras
(`TheoryModel.Algebra`) with all homomorphisms, and `A ⊨ a = b` when the unique folds agree.

This is the equational logic of the Isotope algebra models (`TheoryModel.Models`), whose
theories are congruences on the syntax. It is defined here, over the same signatures as the
refinement institution, so that the comparison `EQ → REF` of `Comorphism.lean` is an ordinary
comorphism with identity signature functor. (A separate Isotope equational track may define an
equational institution of its own; once it lands, the two should be identified.)

## Main definitions

* `Pair.EqHolds`, `eqRoom`, `eqCorridor`, `eqInstitution`, `eqInst`.
* `eqSentencesOf`: the equations of a congruence; `eqTheoryOf`.
* `toModels`, `ofModels`, `eqModelsEquiv`: models of `eqTheoryOf E` are `TheoryModel.Models`.

## Main results

* `Pair.eqHolds_map`: the satisfaction condition.
* `eqSentencesOf_isClosed`: congruences give closed theories, from `TheoryModel.semantic_iff`.
-/

namespace Silmaril.Isotope.Institution.Refinement

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution
open Silmaril.Logic.Metatheory.TheoryModel Silmaril.Logic.Metatheory.TheoryModel
open PSig

universe u v w

variable {P Q R : PSig.{u, v, w}}

namespace Pair

/-- An algebra validates `a = b` when `⟦a⟧ = ⟦b⟧`. -/
def EqHolds (A : Algebra.{u, v, w} P.sig) (e : Pair P) : Prop :=
  P.eval A e.2.1 = P.eval A e.2.2

/-- The satisfaction condition for typed equations. -/
theorem eqHolds_map (f : P ⟶ Q) (A : Algebra.{u, v, w} Q.sig) (e : Pair P) :
    (e.map f).EqHolds A ↔ e.EqHolds ((Algebra.reduct (toSig f)).obj A) := by
  obtain ⟨i, a, b⟩ := e
  show Q.eval A ((translate f).map a) = Q.eval A ((translate f).map b) ↔
    P.eval ((Algebra.reduct (toSig f)).obj A) a = P.eval ((Algebra.reduct (toSig f)).obj A) b
  rw [eval_reduct_obj, eval_reduct_obj]
  exact Iff.rfl

end Pair

/-- The equational room of a presented signature. -/
def eqRoom (P : PSig.{u, v, w}) : Room.{max u w, max u w, max u v (w + 1)} :=
  ⟨Pair P, Cat.of (Algebra.{u, v, w} P.sig), fun (A : Algebra.{u, v, w} P.sig) e => e.EqHolds A⟩

/-- The equational corridor of a signature morphism. -/
def eqCorridor (f : P ⟶ Q) : eqRoom P ⟶ eqRoom Q :=
  ⟨Pair.map f, Algebra.reduct (toSig f),
    fun (A : Algebra.{u, v, w} Q.sig) e => Pair.eqHolds_map f A e⟩

theorem eqCorridor_id (P : PSig.{u, v, w}) : eqCorridor (𝟙 P) = 𝟙 (eqRoom P) :=
  Room.hom_ext (funext Pair.map_id) rfl

theorem eqCorridor_comp (f : P ⟶ Q) (g : Q ⟶ R) :
    eqCorridor (f ≫ g) = eqCorridor f ≫ eqCorridor g :=
  Room.hom_ext (funext (Pair.map_comp f g)) (algebraReduct_comp f g)

/-- The equational institution of presented signatures. -/
def eqInstitution : PSig.{u, v, w} ⥤ Room.{max u w, max u w, max u v (w + 1)} where
  obj := eqRoom
  map := eqCorridor
  map_id := eqCorridor_id
  map_comp := eqCorridor_comp

set_option linter.checkUnivs false in
/-- The equational institution, bundled. (The universes are `max`-expressions in `u`, `v`, `w`
by construction.) -/
def eqInst : Inst.{max (u + 1) (v + 1) (w + 1), max u v, max u w, max u w, max u v (w + 1)} :=
  ⟨PSig.{u, v, w}, eqInstitution⟩

/-! ### Congruences as equational theories -/

/-- The typed equations recorded by a congruence on the syntax. -/
def eqSentencesOf (E : Congruence P.syn) : Set (Pair P) := {e | E.Rel e.2.1 e.2.2}

/-- The models of `eqSentencesOf E` are exactly the algebras validating `E`, i.e. the objects of
`TheoryModel.Models P.isInitial E`. -/
theorem mem_modelsOf_eqSentencesOf (E : Congruence P.syn) (A : Algebra.{u, v, w} P.sig) :
    A ∈ (eqInstitution.obj P).modelsOf (eqSentencesOf E) ↔
      ∀ {i : P.Index} {a b : P.syn.Carrier i}, E.Rel a b → P.eval A a = P.eval A b := by
  constructor
  · intro hA i a b h
    exact hA (⟨i, a, b⟩ : Pair P) h
  · intro h e he
    exact h he

/-- A congruence is a closed set of equations. Follows from `TheoryModel.semantic_iff` (the
quotient model is complete). -/
theorem eqSentencesOf_isClosed (E : Congruence P.syn) :
    (eqInstitution.obj P).IsClosed (eqSentencesOf E) := by
  refine Set.Subset.antisymm ?_ ((eqInstitution.obj P).subset_closure _)
  intro e he
  refine (semantic_iff P.isInitial E e.2.1 e.2.2).2 (fun M => ?_)
  exact he M.algebra ((mem_modelsOf_eqSentencesOf E M.algebra).2 M.sound)

/-- The equational theory of a congruence. -/
def eqTheoryOf (E : Congruence P.syn) : Silmaril.Logic.Institution.Theory eqInstitution.{u, v, w} :=
  ⟨⟨P, eqSentencesOf E⟩, eqSentencesOf_isClosed E⟩

/-- Models of the theory of `E`, as Isotope algebra models of `E`. -/
def toModels (E : Congruence P.syn) : (eqTheoryOf E).Models ⥤ Models P.isInitial E where
  obj M := ⟨M.obj, (mem_modelsOf_eqSentencesOf E M.obj).1 M.property⟩
  map f := f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Isotope algebra models of `E`, as models of the theory of `E`. -/
def ofModels (E : Congruence P.syn) : Models P.isInitial E ⥤ (eqTheoryOf E).Models where
  obj M := ⟨M.algebra, (mem_modelsOf_eqSentencesOf E M.algebra).2 M.sound⟩
  map f := ObjectProperty.homMk f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The model category of the equational theory of `E` is the Isotope category
`TheoryModel.Models P.isInitial E`. -/
def eqModelsEquiv (E : Congruence P.syn) : (eqTheoryOf E).Models ≌ Models P.isInitial E :=
  CategoryTheory.Equivalence.mk (toModels E) (ofModels E)
    (NatIso.ofComponents (fun _ => Iso.refl _))
    (NatIso.ofComponents (fun _ => Iso.refl _))

/-- The initial model of the theory of `E`: the quotient syntax `TheoryModel.quotientModel`. -/
noncomputable def eqInitialModel (E : Congruence P.syn) : (eqTheoryOf E).Models :=
  (ofModels E).obj (quotientModel P.isInitial E)

/-- The quotient model is initial among models of the equational theory of `E`. From
`TheoryModel.quotientModelDesc` and `TheoryModel.quotientIsInitial`. -/
noncomputable def eqInitialModelIsInitial (E : Congruence P.syn) :
    IsInitial (eqInitialModel E) :=
  IsInitial.ofUniqueHom
    (fun M => ObjectProperty.homMk (quotientModelDesc P.isInitial E ((toModels E).obj M)))
    (fun M _ => ObjectProperty.hom_ext _
      ((quotientIsInitial P.isInitial E).hom_ext (Y := (toModels E).obj M) _ _))

end Silmaril.Isotope.Institution.Refinement
