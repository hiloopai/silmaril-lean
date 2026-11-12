module

public import Silmaril.Logic.Metatheory.Theory.Model

@[expose] public section

/-!
# Signature maps and reducts of presentation models

A signature map preserves operation symbols and their argument positions, up
to a specified bijection, while translating sorts. Its reduct functor retains
the target carrier at each translated sort and interprets each source symbol
by its target symbol. Unlike a relation-preserving theory translation, this
operation data suffices to transform arbitrary semantic algebras.
-/

namespace Silmaril.Logic.Metatheory.TheoryModel
open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel Silmaril.Logic.Metatheory.TheoryModel.Algebra

open CategoryTheory CategoryTheory.Limits

universe u v w u' v' u'' v'' u''' v'''

namespace Signature

variable {I : Type u} {J : Type u'} {K : Type u''} {S : Signature.{u, v} I} {T : Signature.{u', v'} J}
  {U : Signature.{u'', v''} K}

/-- A sort and operation translation preserving the full list of arguments. -/
structure Hom (S : Signature.{u, v} I) (T : Signature.{u', v'} J) where
  sort : I → J
  op : {i : I} → S.Op i → T.Op (sort i)
  arg : {i : I} → (o : S.Op i) → Fin (T.arity (op o)) ≃ Fin (S.arity o)
  argSort : ∀ {i : I} (o : S.Op i) (j : Fin (T.arity (op o))),
    sort (S.argSort o (arg o j)) = T.argSort (op o) j

def Hom.id (S : Signature.{u, v} I) : Hom S S where
  sort i := i
  op o := o
  arg _ := Equiv.refl _
  argSort _ _ := rfl

def Hom.comp (g : Hom T U) (f : Hom S T) : Hom S U where
  sort i := g.sort (f.sort i)
  op o := g.op (f.op o)
  arg o := (g.arg (f.op o)).trans (f.arg o)
  argSort o j := (congrArg g.sort (f.argSort o (g.arg (f.op o) j))).trans
    (g.argSort (f.op o) j)

@[simp] theorem Hom.id_comp (f : Hom S T) : (id T).comp f = f := by cases f; rfl

@[simp] theorem Hom.comp_id (f : Hom S T) : f.comp (id S) = f := by cases f; rfl

theorem Hom.comp_assoc {L : Type u'''} {V : Signature.{u''', v'''} L}
    (h : Hom U V) (g : Hom T U) (f : Hom S T) :
    h.comp (g.comp f) = (h.comp g).comp f := rfl

end Signature

namespace Algebra

variable {I : Type u} {J : Type u'} {K : Type u''} {S : Signature.{u, v} I} {T : Signature.{u', v'} J}
  {U : Signature.{u'', v''} K}

/-- Interpret a source operation using its target operation and argument map. -/
def reductObj (f : Signature.Hom S T) (X : Algebra.{u', v', w} T) : Algebra.{u, v, w} S where
  Carrier i := X.Carrier (f.sort i)
  op o args := X.op (f.op o) (fun j =>
    (f.argSort o j) ▸ args (f.arg o j))

theorem Hom.map_cast {X Y : Algebra.{u', v', w} T} (h : X ⟶ Y)
    {i j : J} (e : i = j) (a : X.Carrier i) :
    h.map (e ▸ a) = e ▸ h.map a := by cases e; rfl

/-- Operation homomorphisms remain homomorphisms after taking a reduct. -/
def reductMap (f : Signature.Hom S T) {X Y : Algebra.{u', v', w} T} (h : X ⟶ Y) :
    reductObj f X ⟶ reductObj f Y where
  map a := h.map a
  comm o args := by
    change h.map (X.op (f.op o) _) = Y.op (f.op o) _
    rw [h.comm]
    congr 1
    funext j
    exact Hom.map_cast h (f.argSort o j) (args (f.arg o j))

/-- Signature translations act contravariantly on algebras. -/
def reduct (f : Signature.Hom S T) : Algebra.{u', v', w} T ⥤ Algebra.{u, v, w} S where
  obj := reductObj f
  map := reductMap f

@[simp] theorem reduct_id : reduct (Signature.Hom.id S) = 𝟭 (Algebra.{u, v, w} S) := rfl

private theorem transport_comp (f : J → K) (P : K → Type w) {a b : J}
    (h : a = b) {c : K} (k : f b = c) (x : P (f a)) :
    ((congrArg f h).trans k) ▸ x = k ▸ (h ▸ x) := by
  cases h
  cases k
  rfl

theorem reductObj_comp (g : Signature.Hom T U) (f : Signature.Hom S T)
    (X : Algebra.{u'', v'', w} U) : reductObj (g.comp f) X = reductObj f (reductObj g X) := by
  unfold reductObj
  congr 1
  funext i o args
  dsimp [Signature.Hom.comp]
  congr 1
  funext j
  exact transport_comp g.sort X.Carrier (f.argSort o (g.arg (f.op o) j))
    (g.argSort (f.op o) j) (args (f.arg o (g.arg (f.op o) j)))

/-- Composed reducts are canonically isomorphic by the identity on carriers. -/
def reductCompIso (g : Signature.Hom T U) (f : Signature.Hom S T)
    (X : Algebra.{u'', v'', w} U) : reductObj (g.comp f) X ≅ reductObj f (reductObj g X) where
  hom := {
    map a := a
    comm := fun o args => by
      dsimp [reductObj, Signature.Hom.comp]
      congr 1
      funext j
      exact transport_comp g.sort X.Carrier (f.argSort o (g.arg (f.op o) j))
        (g.argSort (f.op o) j) (args (f.arg o (g.arg (f.op o) j))) }
  inv := {
    map a := a
    comm := fun o args => by
      dsimp [reductObj, Signature.Hom.comp]
      congr 1
      funext j
      exact (transport_comp g.sort X.Carrier (f.argSort o (g.arg (f.op o) j))
        (g.argSort (f.op o) j) (args (f.arg o (g.arg (f.op o) j)))).symm }

/-- The composition comparison is natural in the semantic algebra. -/
def reductComp (g : Signature.Hom T U) (f : Signature.Hom S T) :
    reduct (g.comp f) ≅ reduct g ⋙ reduct f :=
  NatIso.ofComponents (reductCompIso g f) (fun _ => Hom.ext fun _ => rfl)

/-- Compose operation-preserving syntax maps over composed signatures. -/
def reindexComp (g : Signature.Hom T U) (f : Signature.Hom S T)
    {A : Algebra.{u, v, w} S} {B : Algebra.{u', v', w} T} {C : Algebra.{u'', v'', w} U}
    (t : A ⟶ reductObj f B) (s : B ⟶ reductObj g C) : A ⟶ reductObj (g.comp f) C :=
  t ≫ reductMap f s ≫ (reductCompIso g f C).inv

end Algebra

variable {I : Type u} {J : Type u'} {S : Signature.{u, v} I} {T : Signature.{u', v'} J}
  {A : Algebra.{u, v, w} S} {B : Algebra.{u', v', w} T}

/-- A syntactic algebra map commutes with folding into any target algebra. -/
theorem reindex_fold (f : Signature.Hom S T) (hA : IsInitial A) (hB : IsInitial B)
    (t : A ⟶ Algebra.reductObj f B) (X : Algebra.{u', v', w} T) :
    hA.to (Algebra.reductObj f X) = t ≫ Algebra.reductMap f (hB.to X) :=
  hA.hom_ext _ _

/-- Evaluation in a reduct is evaluation of the translated syntax. -/
theorem reindex_fold_map (f : Signature.Hom S T) (hA : IsInitial A) (hB : IsInitial B)
    (t : A ⟶ Algebra.reductObj f B) (X : Algebra.{u', v', w} T) {i : I} (a : A.Carrier i) :
    (hA.to (Algebra.reductObj f X)).map a = (hB.to X).map (t.map a) := by
  rw [reindex_fold f hA hB t X]
  rfl

namespace Models

/-- A signature translation and a sound syntax map induce semantic restriction. -/
def reindex (f : Signature.Hom S T) (hA : IsInitial A) (hB : IsInitial B)
    {E : Congruence A} {F : Congruence B} (t : A ⟶ Algebra.reductObj f B)
    (sound : ∀ {i : I} {a b : A.Carrier i}, E.Rel a b → F.Rel (t.map a) (t.map b)) :
    Models hB F ⥤ Models hA E where
  obj M := {
    algebra := Algebra.reductObj f M.algebra
    sound := fun {i a b} h => by
      rw [reindex_fold f hA hB t M.algebra]
      exact M.sound (sound h) }
  map h := Algebra.reductMap f h

@[simp] theorem reindex_id (hA : IsInitial A) (E : Congruence A) :
    reindex (Signature.Hom.id S) hA hA (E := E) (F := E) (𝟙 A) (fun h => h) =
      𝟭 (Models hA E) := rfl

end Models

namespace Models

variable {K : Type u''} {U : Signature.{u'', v''} K} {C : Algebra.{u'', v'', w} U}

/-- Successive restriction of models agrees naturally with composition of
their signatures and syntax maps. -/
def reindexComp (g : Signature.Hom T U) (f : Signature.Hom S T)
    (hA : IsInitial A) (hB : IsInitial B) (hC : IsInitial C)
    {E : Congruence A} {F : Congruence B} {G : Congruence C}
    (t : A ⟶ Algebra.reductObj f B) (s : B ⟶ Algebra.reductObj g C)
    (ht : ∀ {i : I} {a b : A.Carrier i}, E.Rel a b → F.Rel (t.map a) (t.map b))
    (hs : ∀ {j : J} {a b : B.Carrier j}, F.Rel a b → G.Rel (s.map a) (s.map b)) :
    reindex (g.comp f) hA hC (Algebra.reindexComp g f t s) (fun h => hs (ht h)) ≅
      reindex g hB hC s hs ⋙ reindex f hA hB t ht :=
  NatIso.ofComponents (fun M => {
    hom := (Algebra.reductCompIso g f M.algebra).hom
    inv := (Algebra.reductCompIso g f M.algebra).inv
    hom_inv_id := Algebra.Hom.ext fun _ => rfl
    inv_hom_id := Algebra.Hom.ext fun _ => rfl })
    (fun _ => Algebra.Hom.ext fun _ => rfl)

end Models

/-- The quotient map along a signature translation preserves every source operation. -/
noncomputable def quotientReindex (f : Signature.Hom S T)
    {E : Congruence A} {F : Congruence B} (t : A ⟶ Algebra.reductObj f B)
    (sound : ∀ {i : I} {a b : A.Carrier i}, E.Rel a b → F.Rel (t.map a) (t.map b)) :
    quotient E ⟶ Algebra.reductObj f (quotient F) :=
  quotientDesc E (t ≫ Algebra.reductMap f (quotientMap F))
    (fun h => Quotient.sound (sound h))

@[simp] theorem quotientReindex_class (f : Signature.Hom S T)
    {E : Congruence A} {F : Congruence B} (t : A ⟶ Algebra.reductObj f B)
    (sound : ∀ {i : I} {a b : A.Carrier i}, E.Rel a b → F.Rel (t.map a) (t.map b))
    {i : I} (a : A.Carrier i) :
    (quotientReindex f t sound).map ((quotientMap E).map a) = (quotientMap F).map (t.map a) := rfl

theorem quotientReindex_isInitialMap (f : Signature.Hom S T)
    (hA : IsInitial A) (hB : IsInitial B)
    {E : Congruence A} {F : Congruence B} (t : A ⟶ Algebra.reductObj f B)
    (sound : ∀ {i : I} {a b : A.Carrier i}, E.Rel a b → F.Rel (t.map a) (t.map b)) :
    (quotientReindex f t sound : quotientModel hA E ⟶
      (Models.reindex f hA hB t sound).obj (quotientModel hB F)) =
      (quotientIsInitial hA E).to
        ((Models.reindex f hA hB t sound).obj (quotientModel hB F)) :=
  (quotientIsInitial hA E).hom_ext
    (Y := (Models.reindex f hA hB t sound).obj (quotientModel hB F)) _ _

@[simp] theorem quotientReindex_id (E : Congruence A) :
    quotientReindex (Signature.Hom.id S) (E := E) (F := E) (𝟙 A) (fun h => h) =
      𝟙 (quotient E) := by
  apply quotientDesc_unique E
  exact Algebra.Hom.ext fun _ => rfl

theorem quotientReindex_comp {K : Type u''} {U : Signature.{u'', v''} K}
    {C : Algebra.{u'', v'', w} U} (g : Signature.Hom T U) (f : Signature.Hom S T)
    {E : Congruence A} {F : Congruence B} {G : Congruence C}
    (t : A ⟶ Algebra.reductObj f B) (s : B ⟶ Algebra.reductObj g C)
    (ht : ∀ {i : I} {a b : A.Carrier i}, E.Rel a b → F.Rel (t.map a) (t.map b))
    (hs : ∀ {j : J} {a b : B.Carrier j}, F.Rel a b → G.Rel (s.map a) (s.map b)) :
    quotientReindex (g.comp f) (Algebra.reindexComp g f t s) (fun h => hs (ht h)) ≫
        (Algebra.reductCompIso g f (quotient G)).hom =
      quotientReindex f t ht ≫ Algebra.reductMap f (quotientReindex g s hs) := by
  apply quotientDesc_unique E
  exact Algebra.Hom.ext fun _ => rfl

end Silmaril.Logic.Metatheory.TheoryModel
