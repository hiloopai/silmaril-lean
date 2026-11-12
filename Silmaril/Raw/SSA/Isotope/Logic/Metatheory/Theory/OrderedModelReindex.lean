module

public import Silmaril.Raw.SSA.Isotope.Logic.Metatheory.Theory.ModelReindex
public import Silmaril.Raw.SSA.Isotope.Logic.Metatheory.Theory.OrderedModel

@[expose] public section

/-!
# Signature reducts of ordered models

Operation and sort translations restrict ordered algebras as well as ordinary
algebras. A syntax homomorphism preserving refinement therefore induces a
contravariant functor on models and a covariant map on their initial quotients.
-/

namespace Silmaril.Logic.Metatheory.TheoryModel
open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel Silmaril.Logic.Metatheory.TheoryModel.Algebra

open CategoryTheory CategoryTheory.Limits

universe u v w u' v' u'' v'' u''' v'''

variable {I : Type u} {J : Type u'} {K : Type u''} {S : Signature.{u, v} I} {T : Signature.{u', v'} J}
  {U : Signature.{u'', v''} K}

namespace OrderedAlgebra

theorem cast_le (X : OrderedAlgebra.{u', v', w} T) {i j : J} (e : i = j)
    {a b : X.Carrier i} (h : a ≤ b) : (e ▸ a) ≤ (e ▸ b) := by
  cases e
  exact h

def reductObj (f : Signature.Hom S T) (X : OrderedAlgebra.{u', v', w} T) :
    OrderedAlgebra.{u, v, w} S where
  toAlgebra := Algebra.reductObj f X.toAlgebra
  order i := X.order (f.sort i)
  monotone_op o _a _b h := X.monotone_op (f.op o) _ _
    (fun j => cast_le X (f.argSort o j) (h (f.arg o j)))

def reductMap (f : Signature.Hom S T) {X Y : OrderedAlgebra.{u', v', w} T} (h : X ⟶ Y) :
    reductObj f X ⟶ reductObj f Y where
  toHom := Algebra.reductMap f h.toHom
  monotone i := h.monotone (f.sort i)

/-- Restrict operations and order along a signature map. -/
def reduct (f : Signature.Hom S T) : OrderedAlgebra.{u', v', w} T ⥤ OrderedAlgebra.{u, v, w} S where
  obj := reductObj f
  map := reductMap f

@[simp] theorem reduct_id : reduct (Signature.Hom.id S) = 𝟭 (OrderedAlgebra.{u, v, w} S) := rfl

def reductCompIso (g : Signature.Hom T U) (f : Signature.Hom S T)
    (X : OrderedAlgebra.{u'', v'', w} U) : reductObj (g.comp f) X ≅ reductObj f (reductObj g X) where
  hom := { toHom := (Algebra.reductCompIso g f X.toAlgebra).hom, monotone := fun _ => monotone_id }
  inv := { toHom := (Algebra.reductCompIso g f X.toAlgebra).inv, monotone := fun _ => monotone_id }
  hom_inv_id := Hom.ext (Algebra.Hom.ext fun _ => rfl)
  inv_hom_id := Hom.ext (Algebra.Hom.ext fun _ => rfl)

def reductComp (g : Signature.Hom T U) (f : Signature.Hom S T) :
    reduct (g.comp f) ≅ reduct g ⋙ reduct f :=
  NatIso.ofComponents (reductCompIso g f) (fun _ => Hom.ext (Algebra.Hom.ext fun _ => rfl))

end OrderedAlgebra

variable {A : Algebra.{u, v, w} S} {B : Algebra.{u', v', w} T} {C : Algebra.{u'', v'', w} U}

namespace OrderedModels

/-- Refinement-preserving syntax translations restrict actual ordered models. -/
def reindex (f : Signature.Hom S T) (hA : IsInitial A) (hB : IsInitial B)
    {R : CompatiblePreorder A} {Q : CompatiblePreorder B} (t : A ⟶ Algebra.reductObj f B)
    (sound : ∀ {i : I} {a b : A.Carrier i}, R.Rel a b → Q.Rel (t.map a) (t.map b)) :
    OrderedModels hB Q ⥤ OrderedModels hA R where
  obj M := {
    algebra := OrderedAlgebra.reductObj f M.algebra
    sound := fun {i a b} h => by
      change @LE.le _ (M.algebra.order (f.sort i)).toLE
        ((hA.to (Algebra.reductObj f M.algebra.toAlgebra)).map a)
        ((hA.to (Algebra.reductObj f M.algebra.toAlgebra)).map b)
      rw [reindex_fold f hA hB t M.algebra.toAlgebra]
      exact M.sound (sound h) }
  map h := OrderedAlgebra.reductMap f h

@[simp] theorem reindex_id (hA : IsInitial A) (R : CompatiblePreorder A) :
    reindex (Signature.Hom.id S) hA hA (R := R) (Q := R) (𝟙 A) (fun h => h) =
      𝟭 (OrderedModels hA R) := rfl

def reindexComp (g : Signature.Hom T U) (f : Signature.Hom S T)
    (hA : IsInitial A) (hB : IsInitial B) (hC : IsInitial C)
    {R : CompatiblePreorder A} {Q : CompatiblePreorder B} {P : CompatiblePreorder C}
    (t : A ⟶ Algebra.reductObj f B) (s : B ⟶ Algebra.reductObj g C)
    (ht : ∀ {i : I} {a b : A.Carrier i}, R.Rel a b → Q.Rel (t.map a) (t.map b))
    (hs : ∀ {j : J} {a b : B.Carrier j}, Q.Rel a b → P.Rel (s.map a) (s.map b)) :
    reindex (g.comp f) hA hC (Algebra.reindexComp g f t s) (fun h => hs (ht h)) ≅
      reindex g hB hC s hs ⋙ reindex f hA hB t ht :=
  NatIso.ofComponents (fun M => {
    hom := (OrderedAlgebra.reductCompIso g f M.algebra).hom
    inv := (OrderedAlgebra.reductCompIso g f M.algebra).inv
    hom_inv_id := OrderedAlgebra.Hom.ext (Algebra.Hom.ext fun _ => rfl)
    inv_hom_id := OrderedAlgebra.Hom.ext (Algebra.Hom.ext fun _ => rfl) })
    (fun _ => OrderedAlgebra.Hom.ext (Algebra.Hom.ext fun _ => rfl))

end OrderedModels

/-- A refinement-preserving syntax map descends to the antisymmetric quotients. -/
noncomputable def orderedQuotientReindex (f : Signature.Hom S T)
    {R : CompatiblePreorder A} {Q : CompatiblePreorder B} (t : A ⟶ Algebra.reductObj f B)
    (sound : ∀ {i : I} {a b : A.Carrier i}, R.Rel a b → Q.Rel (t.map a) (t.map b)) :
    orderedQuotient R ⟶ OrderedAlgebra.reductObj f (orderedQuotient Q) :=
  orderedQuotientDesc R (t ≫ Algebra.reductMap f (quotientMap Q.equationalCore)) sound

@[simp] theorem orderedQuotientReindex_class (f : Signature.Hom S T)
    {R : CompatiblePreorder A} {Q : CompatiblePreorder B} (t : A ⟶ Algebra.reductObj f B)
    (sound : ∀ {i : I} {a b : A.Carrier i}, R.Rel a b → Q.Rel (t.map a) (t.map b))
    {i : I} (a : A.Carrier i) :
    (orderedQuotientReindex f t sound).toHom.map ((quotientMap R.equationalCore).map a) =
      (quotientMap Q.equationalCore).map (t.map a) := rfl

theorem orderedQuotientReindex_isInitialMap (f : Signature.Hom S T)
    (hA : IsInitial A) (hB : IsInitial B)
    {R : CompatiblePreorder A} {Q : CompatiblePreorder B} (t : A ⟶ Algebra.reductObj f B)
    (sound : ∀ {i : I} {a b : A.Carrier i}, R.Rel a b → Q.Rel (t.map a) (t.map b)) :
    (orderedQuotientReindex f t sound : orderedQuotientModel hA R ⟶
      (OrderedModels.reindex f hA hB t sound).obj (orderedQuotientModel hB Q)) =
      (orderedQuotientIsInitial hA R).to
        ((OrderedModels.reindex f hA hB t sound).obj (orderedQuotientModel hB Q)) :=
  (orderedQuotientIsInitial hA R).hom_ext
    (Y := (OrderedModels.reindex f hA hB t sound).obj (orderedQuotientModel hB Q)) _ _

@[simp] theorem orderedQuotientReindex_id (R : CompatiblePreorder A) :
    orderedQuotientReindex (Signature.Hom.id S) (R := R) (Q := R) (𝟙 A) (fun h => h) =
      𝟙 (orderedQuotient R) := by
  apply orderedQuotientDesc_unique R
  exact Algebra.Hom.ext fun _ => rfl

theorem orderedQuotientReindex_comp (g : Signature.Hom T U) (f : Signature.Hom S T)
    {R : CompatiblePreorder A} {Q : CompatiblePreorder B} {P : CompatiblePreorder C}
    (t : A ⟶ Algebra.reductObj f B) (s : B ⟶ Algebra.reductObj g C)
    (ht : ∀ {i : I} {a b : A.Carrier i}, R.Rel a b → Q.Rel (t.map a) (t.map b))
    (hs : ∀ {j : J} {a b : B.Carrier j}, Q.Rel a b → P.Rel (s.map a) (s.map b)) :
    orderedQuotientReindex (g.comp f) (Algebra.reindexComp g f t s) (fun h => hs (ht h)) ≫
        (OrderedAlgebra.reductCompIso g f (orderedQuotient P)).hom =
      orderedQuotientReindex f t ht ≫ OrderedAlgebra.reductMap f (orderedQuotientReindex g s hs) := by
  apply orderedQuotientDesc_unique R
  exact Algebra.Hom.ext fun _ => rfl

end Silmaril.Logic.Metatheory.TheoryModel
