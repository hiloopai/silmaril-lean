module

public import Silmaril.Raw.SSA.Isotope.Logic.Metatheory.Theory.OrderedModelReindex

@[expose] public section

/-!
# Presented signatures

The Isotope model theory (`Silmaril.Logic.Metatheory.TheoryModel`) interprets syntax by the
unique fold out of a chosen *initial* algebra: the exact typed syntax of a calculus in a fixed
context, with free variables and primitive instructions as named generators. A *presented
signature* bundles a many-sorted operation signature with such an initial syntax algebra. These
are the signatures of the equational and refinement institutions of
`Silmaril.Isotope.Institution.Refinement`.

A morphism of presented signatures is a signature morphism (`TheoryModel.Signature.Hom`). By
initiality it determines the syntax translation `translate f`, the unique fold of the source
syntax into the reduct of the target syntax; so the Isotope inclusions
(`Morphism.SeqCase.typedSignatureHom`, `Morphism.CaseIter.typedSignatureHom`) are morphisms here
and their algebra maps (`typedAlgebraHom`) are recovered as `translate`.

## Main definitions

* `PSig`, its category instance, `PSig.toSig`.
* `PSig.eval`: evaluation of syntax in an algebra (the unique fold).
* `PSig.translate`: the syntax translation along a morphism.
* `discrete`: an algebra ordered by equality.
-/

namespace Silmaril.Isotope.Institution.Refinement

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Metatheory.TheoryModel Silmaril.Logic.Metatheory.TheoryModel

universe u v w

/-- A presented signature: many-sorted operations together with a chosen initial algebra of
syntax. -/
structure PSig where
  /-- The sorts. -/
  Index : Type u
  /-- The operation symbols. -/
  sig : Signature.{u, v} Index
  /-- The syntax algebra, e.g. exactly typed terms with their typing evidence. -/
  syn : Algebra.{u, v, w} sig
  /-- The syntax is initial: every algebra receives a unique fold. -/
  isInitial : IsInitial syn

/-- A homomorphism conjugated by `eqToHom`s acts on carriers by transport. -/
theorem algebra_eqToHom_conj_map {I : Type u} {Sig : Signature.{u, v} I}
    {A A' B' B : Algebra.{u, v, w} Sig} (eA : A = A') (eB : B' = B) (k : A' ⟶ B') {i : I}
    (a : A.Carrier i) :
    (eqToHom eA ≫ k ≫ eqToHom eB).map a =
      cast (congrArg (fun X : Algebra.{u, v, w} Sig => X.Carrier i) eB)
        (k.map (cast (congrArg (fun X : Algebra.{u, v, w} Sig => X.Carrier i) eA) a)) := by
  subst eA
  subst eB
  rfl

/-- A monotone homomorphism conjugated by `eqToHom`s acts on carriers by transport. -/
theorem orderedAlgebra_eqToHom_conj_map {I : Type u} {Sig : Signature.{u, v} I}
    {A A' B' B : OrderedAlgebra.{u, v, w} Sig} (eA : A = A') (eB : B' = B) (k : A' ⟶ B')
    {i : I} (a : A.Carrier i) :
    (eqToHom eA ≫ k ≫ eqToHom eB).toHom.map a =
      cast (congrArg (fun X : OrderedAlgebra.{u, v, w} Sig => X.Carrier i) eB)
        (k.toHom.map
          (cast (congrArg (fun X : OrderedAlgebra.{u, v, w} Sig => X.Carrier i) eA) a)) := by
  subst eA
  subst eB
  rfl

/-- Ordered algebras with equal underlying algebras and (heterogeneously) equal orders are
equal. -/
theorem orderedAlgebra_ext {I : Type u} {Sig : Signature.{u, v} I}
    {A B : OrderedAlgebra.{u, v, w} Sig} (e : A.toAlgebra = B.toAlgebra)
    (hord : ∀ i, HEq (A.order i) (B.order i)) : A = B := by
  obtain ⟨A, oA, mA⟩ := A
  obtain ⟨B, oB, mB⟩ := B
  dsimp only at e hord
  subst e
  have : oA = oB := funext fun i => eq_of_heq (hord i)
  subst this
  rfl

namespace PSig

/-- Presented signatures with signature morphisms. Composition is that of
`TheoryModel.Signature.Hom`, which is strictly associative and unital. -/
instance category : Category.{max u v} PSig.{u, v, w} where
  Hom P Q := Signature.Hom P.sig Q.sig
  id P := Signature.Hom.id P.sig
  comp f g := g.comp f
  id_comp f := Signature.Hom.comp_id f
  comp_id f := Signature.Hom.id_comp f
  assoc _ _ _ := rfl

variable {P Q R : PSig.{u, v, w}}

/-- The underlying signature morphism. -/
abbrev toSig (f : P ⟶ Q) : Signature.Hom P.sig Q.sig := f

/-- Evaluation of syntax in an algebra: the unique fold out of the initial syntax. -/
def eval (P : PSig.{u, v, w}) (A : Algebra.{u, v, w} P.sig) {i : P.Index}
    (a : P.syn.Carrier i) : A.Carrier i :=
  (P.isInitial.to A).map a

/-- The syntax translation along a signature morphism: the unique fold of the source syntax into
the reduct of the target syntax. -/
def translate (f : P ⟶ Q) : P.syn ⟶ Algebra.reductObj (toSig f) Q.syn :=
  P.isInitial.to _

/-- Evaluation in a reduct is evaluation of the translated syntax. A restatement of
`TheoryModel.reindex_fold_map`, and derived from it. -/
theorem eval_reduct (f : P ⟶ Q) (X : Algebra.{u, v, w} Q.sig) {i : P.Index}
    (a : P.syn.Carrier i) :
    P.eval (Algebra.reductObj (toSig f) X) a = Q.eval X ((translate f).map a) :=
  reindex_fold_map (toSig f) P.isInitial Q.isInitial (translate f) X a

/-- `eval_reduct`, with the reduct written as the reduct functor. -/
theorem eval_reduct_obj (f : P ⟶ Q) (X : Algebra.{u, v, w} Q.sig) {i : P.Index}
    (a : P.syn.Carrier i) :
    P.eval ((Algebra.reduct (toSig f)).obj X) a = Q.eval X ((translate f).map a) :=
  eval_reduct f X a

/-- `eval_reduct` for the reduct of an ordered algebra. -/
theorem eval_orderedReduct (f : P ⟶ Q) (M : OrderedAlgebra.{u, v, w} Q.sig) {i : P.Index}
    (a : P.syn.Carrier i) :
    P.eval ((OrderedAlgebra.reduct (toSig f)).obj M).toAlgebra a =
      Q.eval M.toAlgebra ((translate f).map a) :=
  eval_reduct f M.toAlgebra a

/-- The identity translation is the identity. -/
theorem translate_id_map (P : PSig.{u, v, w}) {i : P.Index} (a : P.syn.Carrier i) :
    (translate (𝟙 P)).map a = a := by
  have h : translate (𝟙 P) = 𝟙 P.syn := P.isInitial.hom_ext _ _
  rw [h]
  rfl

/-- Translation along a composite is the composite of translations. -/
theorem translate_comp_map (f : P ⟶ Q) (g : Q ⟶ R) {i : P.Index} (a : P.syn.Carrier i) :
    (translate (f ≫ g)).map a = (translate g).map ((translate f).map a) := by
  have h : translate (f ≫ g) =
      Algebra.reindexComp (toSig g) (toSig f) (translate f) (translate g) :=
    P.isInitial.hom_ext _ _
  rw [h]
  rfl

/-- The reduct of algebras is strictly functorial along composites of presented signatures.
(`TheoryModel.Algebra.reductComp` gives the natural isomorphism; equality follows from
`TheoryModel.Algebra.reductObj_comp`.) -/
theorem algebraReduct_comp (f : P ⟶ Q) (g : Q ⟶ R) :
    (Algebra.reduct (toSig (f ≫ g)) : Algebra.{u, v, w} R.sig ⥤ Algebra.{u, v, w} P.sig) =
      Algebra.reduct (toSig g) ⋙ Algebra.reduct (toSig f) := by
  refine CategoryTheory.Functor.ext
    (fun X => Algebra.reductObj_comp (toSig g) (toSig f) X) (fun X Y h => ?_)
  refine Algebra.Hom.ext fun a => ?_
  refine Eq.trans ?_ (algebra_eqToHom_conj_map _ _ _ a).symm
  rfl

/-- Composite ordered reducts agree on objects, from `TheoryModel.Algebra.reductObj_comp`. -/
theorem orderedReductObj_comp (f : P ⟶ Q) (g : Q ⟶ R) (X : OrderedAlgebra.{u, v, w} R.sig) :
    OrderedAlgebra.reductObj (toSig (f ≫ g)) X =
      OrderedAlgebra.reductObj (toSig f) (OrderedAlgebra.reductObj (toSig g) X) :=
  orderedAlgebra_ext (Algebra.reductObj_comp (toSig g) (toSig f) X.toAlgebra)
    (fun _ => HEq.rfl)

/-- The reduct of ordered algebras is strictly functorial along composites of presented
signatures (compare `TheoryModel.OrderedAlgebra.reductComp`). -/
theorem orderedReduct_comp (f : P ⟶ Q) (g : Q ⟶ R) :
    (OrderedAlgebra.reduct (toSig (f ≫ g)) :
        OrderedAlgebra.{u, v, w} R.sig ⥤ OrderedAlgebra.{u, v, w} P.sig) =
      OrderedAlgebra.reduct (toSig g) ⋙ OrderedAlgebra.reduct (toSig f) := by
  refine CategoryTheory.Functor.ext (fun X => orderedReductObj_comp f g X) (fun X Y h => ?_)
  refine OrderedAlgebra.Hom.ext (Algebra.Hom.ext fun a => ?_)
  refine Eq.trans ?_ (orderedAlgebra_eqToHom_conj_map _ _ _ a).symm
  rfl

end PSig

/-- Every algebra, ordered by equality. Every operation is monotone for the discrete order, so
every algebra underlies an ordered algebra. -/
def discrete {I : Type u} {Sig : Signature.{u, v} I} (A : Algebra.{u, v, w} Sig) :
    OrderedAlgebra.{u, v, w} Sig where
  toAlgebra := A
  order _ :=
    { le := Eq
      le_refl := fun _ => rfl
      le_trans := fun _ _ _ => Eq.trans
      le_antisymm := fun _ _ h _ => h }
  monotone_op o a b h := by
    show A.op o a = A.op o b
    exact congrArg (A.op o) (funext h)

@[simp] theorem forget_obj_discrete {I : Type u} {Sig : Signature.{u, v} I}
    (A : Algebra.{u, v, w} Sig) : OrderedAlgebra.forget.obj (discrete A) = A := rfl

end Silmaril.Isotope.Institution.Refinement
