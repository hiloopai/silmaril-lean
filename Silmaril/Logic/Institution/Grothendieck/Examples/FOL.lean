module

public import Silmaril.Logic.Institution.Grothendieck.Amalgamation
public import Silmaril.Logic.Institution.Grothendieck.StrictPullback
public import Silmaril.Logic.Institution.Examples.FirstOrder
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

@[expose] public section

/-!
# Semi-exactness of first-order logic

Many-sorted first-order signatures have pushouts, constructed on sorts, operation symbols and
relation symbols (`FOL.hasPushouts`), and many-sorted first-order logic is semi-exact.

The pushout of `Σ₁ ← Σ → Σ₂` (`Examples.FOL.PO.pt`) has as sorts the pushout of the sort sets,
and as operation (relation) symbols the pushout of the sets of *all* operation (relation) symbols
of `Σ₁` and `Σ₂`, each with its arity transported to the new sorts; the symbols of a given arity
are those whose transported arity is that arity. Two structures `M₁`, `M₂` that agree on `Σ`
amalgamate to the structure whose carriers, operations and relations are those of `M₁` on the
image of `Σ₁` and those of `M₂` on the image of `Σ₂` (`Examples.FOL.PO.amalg`); morphisms
amalgamate in the same way.
-/

namespace Silmaril.Logic.Institution.Examples.FOL

open CategoryTheory Limits

namespace PO

/-! ### Arities and the total sets of symbols -/

/-- Operation arities `(n, w, s)` over a set of sorts. -/
abbrev OpAr (S : Type) : Type := Σ n : ℕ, (Fin n → S) × S

/-- Transport of an operation arity along a map of sorts. -/
def OpAr.map {S T : Type} (g : S → T) (a : OpAr S) : OpAr T := ⟨a.1, (g ∘ a.2.1, g a.2.2)⟩

/-- Relation arities `(n, w)` over a set of sorts. -/
abbrev RelAr (S : Type) : Type := Σ n : ℕ, Fin n → S

/-- Transport of a relation arity along a map of sorts. -/
def RelAr.map {S T : Type} (g : S → T) (a : RelAr S) : RelAr T := ⟨a.1, g ∘ a.2⟩

/-- All operation symbols of a signature, with their arities. -/
abbrev OpT (Sg : Signature) : Type := Σ a : OpAr Sg.S, Sg.Op a.1 a.2.1 a.2.2

/-- All relation symbols of a signature, with their arities. -/
abbrev RelT (Sg : Signature) : Type := Σ a : RelAr Sg.S, Sg.Rel a.1 a.2

/-- The action of a signature morphism on all operation symbols. -/
def OpT.map {Sg Sg' : Signature} (σ : Sg ⟶ Sg') (x : OpT Sg) : OpT Sg' :=
  ⟨OpAr.map σ.sorts x.1, σ.ops x.2⟩

/-- The action of a signature morphism on all relation symbols. -/
def RelT.map {Sg Sg' : Signature} (σ : Sg ⟶ Sg') (x : RelT Sg) : RelT Sg' :=
  ⟨RelAr.map σ.sorts x.1, σ.rels x.2⟩

/-- An operation symbol, read at an arity equal to its own. -/
def OpT.cast {Sg : Signature} (y : OpT Sg) {a : OpAr Sg.S} (h : y.1 = a) :
    Sg.Op a.1 a.2.1 a.2.2 :=
  Eq.rec (motive := fun a _ => Sg.Op a.1 a.2.1 a.2.2) y.2 h

/-- A relation symbol, read at an arity equal to its own. -/
def RelT.cast {Sg : Signature} (y : RelT Sg) {a : RelAr Sg.S} (h : y.1 = a) : Sg.Rel a.1 a.2 :=
  Eq.rec (motive := fun a _ => Sg.Rel a.1 a.2) y.2 h

/-! ### Extensionality -/

theorem hom_ext {Sg Sg' : Signature} {f g : Sg ⟶ Sg'} (hs : f.sorts = g.sorts)
    (ho : ∀ {n : ℕ} {w : Fin n → Sg.S} {s : Sg.S} (o : Sg.Op n w s), f.ops o ≍ g.ops o)
    (hr : ∀ {n : ℕ} {w : Fin n → Sg.S} (r : Sg.Rel n w), f.rels r ≍ g.rels r) : f = g := by
  obtain ⟨⟨fs, fo⟩, fr⟩ := f
  obtain ⟨⟨gs, go⟩, gr⟩ := g
  cases hs
  have h₁ : @fo = @go := by
    funext n w s o
    exact eq_of_heq (ho o)
  have h₂ : @fr = @gr := by
    funext n w r
    exact eq_of_heq (hr r)
  subst h₁ h₂
  rfl

theorem structure_ext {Sg : Signature} {A B : Structure Sg} (hc : A.carrier = B.carrier)
    (ho : ∀ {n : ℕ} {w : Fin n → Sg.S} {s : Sg.S} (o : Sg.Op n w s), A.op o ≍ B.op o)
    (hr : ∀ {n : ℕ} {w : Fin n → Sg.S} (r : Sg.Rel n w), A.rel r ≍ B.rel r) : A = B := by
  obtain ⟨⟨Ac, Ao⟩, Ar⟩ := A
  obtain ⟨⟨Bc, Bo⟩, Br⟩ := B
  cases hc
  have h₁ : @Ao = @Bo := by
    funext n w s o
    exact eq_of_heq (ho o)
  have h₂ : @Ar = @Br := by
    funext n w r
    exact eq_of_heq (hr r)
  subst h₁ h₂
  rfl

theorem structureHom_ext {Sg : Signature} {M N : Structure Sg} {m m' : M ⟶ N}
    (h : m.map = m'.map) : m = m' := by
  obtain ⟨map, _, _⟩ := m
  obtain ⟨map', _, _⟩ := m'
  cases h
  rfl

theorem structureHom_map_heq {Sg : Signature} {A B A' B' : Structure Sg} (hA : A = A')
    (hB : B = B') {a : A ⟶ B} {b : A' ⟶ B'} (h : a ≍ b) (s : Sg.S) : a.map s ≍ b.map s := by
  subst hA hB
  obtain rfl := eq_of_heq h
  rfl

/-! ### The pushout of a span of signatures -/

variable {Sg Sg₁ Sg₂ : Signature} (f₁ : Sg ⟶ Sg₁) (f₂ : Sg ⟶ Sg₂)

/-- The relation generating the pushout of sorts. -/
inductive SortRel : Sg₁.S ⊕ Sg₂.S → Sg₁.S ⊕ Sg₂.S → Prop
  | mk (s : Sg.S) : SortRel (.inl (f₁.sorts s)) (.inr (f₂.sorts s))

/-- The relation generating the pushout of operation symbols. -/
inductive OpRel : OpT Sg₁ ⊕ OpT Sg₂ → OpT Sg₁ ⊕ OpT Sg₂ → Prop
  | mk (x : OpT Sg) : OpRel (.inl (OpT.map f₁ x)) (.inr (OpT.map f₂ x))

/-- The relation generating the pushout of relation symbols. -/
inductive RelRel : RelT Sg₁ ⊕ RelT Sg₂ → RelT Sg₁ ⊕ RelT Sg₂ → Prop
  | mk (x : RelT Sg) : RelRel (.inl (RelT.map f₁ x)) (.inr (RelT.map f₂ x))

/-- The sorts of the pushout. -/
abbrev Sorts : Type := Quot (SortRel f₁ f₂)

/-- The left injection of sorts. -/
def inlS (s : Sg₁.S) : Sorts f₁ f₂ := Quot.mk _ (.inl s)

/-- The right injection of sorts. -/
def inrS (s : Sg₂.S) : Sorts f₁ f₂ := Quot.mk _ (.inr s)

theorem inlS_inrS (s : Sg.S) : inlS f₁ f₂ (f₁.sorts s) = inrS f₁ f₂ (f₂.sorts s) :=
  Quot.sound (.mk s)

/-- All operation symbols of the pushout. -/
abbrev OpQ : Type := Quot (OpRel f₁ f₂)

/-- All relation symbols of the pushout. -/
abbrev RelQ : Type := Quot (RelRel f₁ f₂)

/-- The arity of an operation symbol of the pushout. -/
def opAr : OpQ f₁ f₂ → OpAr (Sorts f₁ f₂) :=
  Quot.lift (Sum.elim (fun x => OpAr.map (inlS f₁ f₂) x.1) (fun x => OpAr.map (inrS f₁ f₂) x.1))
    (by
      rintro _ _ ⟨x⟩
      show OpAr.map (inlS f₁ f₂ ∘ f₁.sorts) x.1 = OpAr.map (inrS f₁ f₂ ∘ f₂.sorts) x.1
      exact congrArg (fun k => OpAr.map k x.1) (funext (inlS_inrS f₁ f₂)))

/-- The arity of a relation symbol of the pushout. -/
def relAr : RelQ f₁ f₂ → RelAr (Sorts f₁ f₂) :=
  Quot.lift (Sum.elim (fun x => RelAr.map (inlS f₁ f₂) x.1) (fun x => RelAr.map (inrS f₁ f₂) x.1))
    (by
      rintro _ _ ⟨x⟩
      show RelAr.map (inlS f₁ f₂ ∘ f₁.sorts) x.1 = RelAr.map (inrS f₁ f₂ ∘ f₂.sorts) x.1
      exact congrArg (fun k => RelAr.map k x.1) (funext (inlS_inrS f₁ f₂)))

/-- The pushout signature: pushouts of sorts and of all operation and relation symbols, with
the symbols of an arity being those whose transported arity is that arity.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A2,
Definition 62 (first-order signatures and their morphisms); the colimit is computed componentwise
as for many-sorted signatures, cf. `goguen-rosu-2002-institution-morphisms` in `references.bib`,
§3, Definition 3.10 (PDF page 10: "many sorted logics tend to be exact"). -/
def pt : Signature where
  S := Sorts f₁ f₂
  Op n w s := {x : OpQ f₁ f₂ // opAr f₁ f₂ x = ⟨n, (w, s)⟩}
  Rel n w := {x : RelQ f₁ f₂ // relAr f₁ f₂ x = ⟨n, w⟩}

/-- The left injection into the pushout. -/
def inl : Sg₁ ⟶ pt f₁ f₂ where
  sorts := inlS f₁ f₂
  ops := fun {n w s} o => ⟨Quot.mk _ (.inl ⟨⟨n, (w, s)⟩, o⟩), rfl⟩
  rels := fun {n w} r => ⟨Quot.mk _ (.inl ⟨⟨n, w⟩, r⟩), rfl⟩

/-- The right injection into the pushout. -/
def inr : Sg₂ ⟶ pt f₁ f₂ where
  sorts := inrS f₁ f₂
  ops := fun {n w s} o => ⟨Quot.mk _ (.inr ⟨⟨n, (w, s)⟩, o⟩), rfl⟩
  rels := fun {n w} r => ⟨Quot.mk _ (.inr ⟨⟨n, w⟩, r⟩), rfl⟩

theorem pt_op_heq {n : ℕ} {w w' : Fin n → Sorts f₁ f₂} {s s' : Sorts f₁ f₂} (hw : w = w')
    (hs : s = s') {x : (pt f₁ f₂).Op n w s} {y : (pt f₁ f₂).Op n w' s'} (h : x.1 = y.1) :
    x ≍ y := by
  subst hw hs
  exact heq_of_eq (Subtype.ext h)

theorem pt_rel_heq {n : ℕ} {w w' : Fin n → Sorts f₁ f₂} (hw : w = w')
    {x : (pt f₁ f₂).Rel n w} {y : (pt f₁ f₂).Rel n w'} (h : x.1 = y.1) : x ≍ y := by
  subst hw
  exact heq_of_eq (Subtype.ext h)

theorem condition : f₁ ≫ inl f₁ f₂ = f₂ ≫ inr f₁ f₂ := by
  have hs : (f₁ ≫ inl f₁ f₂).sorts = (f₂ ≫ inr f₁ f₂).sorts := funext (inlS_inrS f₁ f₂)
  refine hom_ext hs (fun {n w s} o => ?_) (fun {n w} r => ?_)
  · exact pt_op_heq f₁ f₂ (congrArg (fun k => k ∘ w) hs) (congrFun hs s)
      (Quot.sound (OpRel.mk ⟨⟨n, (w, s)⟩, o⟩))
  · exact pt_rel_heq f₁ f₂ (congrArg (fun k => k ∘ w) hs) (Quot.sound (RelRel.mk ⟨⟨n, w⟩, r⟩))

section Desc

variable {f₁ f₂} {T : Signature} (h₁ : Sg₁ ⟶ T) (h₂ : Sg₂ ⟶ T) (hc : f₁ ≫ h₁ = f₂ ≫ h₂)

/-- The sort map out of the pushout. -/
def descS : Sorts f₁ f₂ → T.S :=
  Quot.lift (Sum.elim h₁.sorts h₂.sorts) (by
    rintro _ _ ⟨s⟩
    exact congrFun (congrArg (fun k : Sg ⟶ T => k.sorts) hc) s)

/-- The map of operation symbols out of the pushout. -/
def descOpT : OpQ f₁ f₂ → OpT T :=
  Quot.lift (Sum.elim (OpT.map h₁) (OpT.map h₂)) (by
    rintro _ _ ⟨x⟩
    exact congrArg (fun k => OpT.map k x) hc)

/-- The map of relation symbols out of the pushout. -/
def descRelT : RelQ f₁ f₂ → RelT T :=
  Quot.lift (Sum.elim (RelT.map h₁) (RelT.map h₂)) (by
    rintro _ _ ⟨x⟩
    exact congrArg (fun k => RelT.map k x) hc)

theorem descOpT_fst (x : OpQ f₁ f₂) :
    (descOpT h₁ h₂ hc x).1 = OpAr.map (descS h₁ h₂ hc) (opAr f₁ f₂ x) := by
  induction x using Quot.ind with
  | mk x => rcases x with x | x <;> rfl

theorem descRelT_fst (x : RelQ f₁ f₂) :
    (descRelT h₁ h₂ hc x).1 = RelAr.map (descS h₁ h₂ hc) (relAr f₁ f₂ x) := by
  induction x using Quot.ind with
  | mk x => rcases x with x | x <;> rfl

/-- The morphism out of the pushout induced by a cocone. -/
def desc : pt f₁ f₂ ⟶ T where
  sorts := descS h₁ h₂ hc
  ops := fun {_ _ _} o => OpT.cast (descOpT h₁ h₂ hc o.1)
    ((descOpT_fst h₁ h₂ hc o.1).trans (congrArg (OpAr.map (descS h₁ h₂ hc)) o.2))
  rels := fun {_ _} r => RelT.cast (descRelT h₁ h₂ hc r.1)
    ((descRelT_fst h₁ h₂ hc r.1).trans (congrArg (RelAr.map (descS h₁ h₂ hc)) r.2))

theorem inl_desc : inl f₁ f₂ ≫ desc h₁ h₂ hc = h₁ := rfl

theorem inr_desc : inr f₁ f₂ ≫ desc h₁ h₂ hc = h₂ := rfl

theorem desc_uniq (m : pt f₁ f₂ ⟶ T) (e₁ : inl f₁ f₂ ≫ m = h₁) (e₂ : inr f₁ f₂ ≫ m = h₂) :
    m = desc h₁ h₂ hc := by
  have hs : m.sorts = descS h₁ h₂ hc := by
    funext x
    induction x using Quot.ind with
    | mk x =>
      rcases x with s | s
      · exact congrFun (congrArg (fun k : Sg₁ ⟶ T => k.sorts) e₁) s
      · exact congrFun (congrArg (fun k : Sg₂ ⟶ T => k.sorts) e₂) s
  refine hom_ext hs (fun {n w s} o => ?_) (fun {n w} r => ?_)
  · obtain ⟨x, hx⟩ := o
    revert hx
    induction x using Quot.ind with
    | mk x =>
      rcases x with ⟨⟨n', w', s'⟩, o'⟩ | ⟨⟨n', w', s'⟩, o'⟩
      · intro hx
        cases hx
        exact congr_arg_heq (fun k : Sg₁ ⟶ T => k.ops o') e₁
      · intro hx
        cases hx
        exact congr_arg_heq (fun k : Sg₂ ⟶ T => k.ops o') e₂
  · obtain ⟨x, hx⟩ := r
    revert hx
    induction x using Quot.ind with
    | mk x =>
      rcases x with ⟨⟨n', w'⟩, r'⟩ | ⟨⟨n', w'⟩, r'⟩
      · intro hx
        cases hx
        exact congr_arg_heq (fun k : Sg₁ ⟶ T => k.rels r') e₁
      · intro hx
        cases hx
        exact congr_arg_heq (fun k : Sg₂ ⟶ T => k.rels r') e₂

end Desc

/-- The pushout cocone is a colimit. -/
def isColimit : IsColimit (PushoutCocone.mk (inl f₁ f₂) (inr f₁ f₂) (condition f₁ f₂)) :=
  PushoutCocone.IsColimit.mk _ (fun s => desc s.inl s.inr s.condition)
    (fun s => inl_desc s.inl s.inr s.condition) (fun s => inr_desc s.inl s.inr s.condition)
    (fun s m e₁ e₂ => desc_uniq s.inl s.inr s.condition m e₁ e₂)

theorem isPushout : IsPushout f₁ f₂ (inl f₁ f₂) (inr f₁ f₂) :=
  IsPushout.of_isColimit (isColimit f₁ f₂)

/-! ### Amalgamation of structures -/

section Amalgamation

variable {f₁ f₂} (M₁ : Structure Sg₁) (M₂ : Structure Sg₂)
  (h : (Structure.reduct f₁).obj M₁ = (Structure.reduct f₂).obj M₂)

/-- The carriers of the amalgamation. -/
def amCarrier : Sorts f₁ f₂ → Type :=
  Quot.lift (Sum.elim M₁.carrier M₂.carrier) (by
    rintro _ _ ⟨s⟩
    exact congrFun (congrArg (fun A : Structure Sg => A.carrier) h) s)

/-- The operations of the amalgamation, on all operation symbols. -/
def amOp (x : OpQ f₁ f₂) :
    (∀ j, amCarrier M₁ M₂ h ((opAr f₁ f₂ x).2.1 j)) → amCarrier M₁ M₂ h (opAr f₁ f₂ x).2.2 :=
  Quot.hrecOn (motive := fun x => (∀ j, amCarrier M₁ M₂ h ((opAr f₁ f₂ x).2.1 j)) →
      amCarrier M₁ M₂ h (opAr f₁ f₂ x).2.2) x
    (fun t => Sum.rec (motive := fun t => (∀ j, amCarrier M₁ M₂ h ((opAr f₁ f₂ (Quot.mk _ t)).2.1 j)) →
        amCarrier M₁ M₂ h (opAr f₁ f₂ (Quot.mk _ t)).2.2)
      (fun y => M₁.op y.2) (fun y => M₂.op y.2) t)
    (by
      rintro _ _ ⟨y⟩
      exact congr_arg_heq (fun A : Structure Sg => A.op y.2) h)

/-- The relations of the amalgamation, on all relation symbols. -/
def amRel (x : RelQ f₁ f₂) : (∀ j, amCarrier M₁ M₂ h ((relAr f₁ f₂ x).2 j)) → Prop :=
  Quot.hrecOn (motive := fun x => (∀ j, amCarrier M₁ M₂ h ((relAr f₁ f₂ x).2 j)) → Prop) x
    (fun t => Sum.rec (motive := fun t =>
        (∀ j, amCarrier M₁ M₂ h ((relAr f₁ f₂ (Quot.mk _ t)).2 j)) → Prop)
      (fun y => M₁.rel y.2) (fun y => M₂.rel y.2) t)
    (by
      rintro _ _ ⟨y⟩
      exact congr_arg_heq (fun A : Structure Sg => A.rel y.2) h)

/-- The amalgamation of two structures agreeing on the common part.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §3, Definition 3.10
(PDF page 10: semi-exactness, "many sorted logics tend to be exact"). -/
def amalg : Structure (pt f₁ f₂) where
  carrier := amCarrier M₁ M₂ h
  op := fun {_ _ _} o => Eq.rec (motive := fun a _ => (∀ j, amCarrier M₁ M₂ h (a.2.1 j)) →
      amCarrier M₁ M₂ h a.2.2) (amOp M₁ M₂ h o.1) o.2
  rel := fun {_ _} r => Eq.rec (motive := fun a _ => (∀ j, amCarrier M₁ M₂ h (a.2 j)) → Prop)
    (amRel M₁ M₂ h r.1) r.2

theorem reduct_inl_amalg : (Structure.reduct (inl f₁ f₂)).obj (amalg M₁ M₂ h) = M₁ := rfl

theorem reduct_inr_amalg : (Structure.reduct (inr f₁ f₂)).obj (amalg M₁ M₂ h) = M₂ := rfl

end Amalgamation

variable {f₁ f₂}

theorem amalg_uniq (M M' : Structure (pt f₁ f₂))
    (h₁ : (Structure.reduct (inl f₁ f₂)).obj M = (Structure.reduct (inl f₁ f₂)).obj M')
    (h₂ : (Structure.reduct (inr f₁ f₂)).obj M = (Structure.reduct (inr f₁ f₂)).obj M') :
    M = M' := by
  refine structure_ext ?_ (fun {n w s} o => ?_) (fun {n w} r => ?_)
  · funext x
    induction x using Quot.ind with
    | mk x =>
      rcases x with s | s
      · exact congrFun (congrArg (fun A : Structure Sg₁ => A.carrier) h₁) s
      · exact congrFun (congrArg (fun A : Structure Sg₂ => A.carrier) h₂) s
  · obtain ⟨x, hx⟩ := o
    revert hx
    induction x using Quot.ind with
    | mk x =>
      rcases x with ⟨⟨n', w', s'⟩, o'⟩ | ⟨⟨n', w', s'⟩, o'⟩
      · intro hx
        cases hx
        exact congr_arg_heq (fun A : Structure Sg₁ => A.op o') h₁
      · intro hx
        cases hx
        exact congr_arg_heq (fun A : Structure Sg₂ => A.op o') h₂
  · obtain ⟨x, hx⟩ := r
    revert hx
    induction x using Quot.ind with
    | mk x =>
      rcases x with ⟨⟨n', w'⟩, r'⟩ | ⟨⟨n', w'⟩, r'⟩
      · intro hx
        cases hx
        exact congr_arg_heq (fun A : Structure Sg₁ => A.rel r') h₁
      · intro hx
        cases hx
        exact congr_arg_heq (fun A : Structure Sg₂ => A.rel r') h₂

theorem reduct_condition (M : Structure (pt f₁ f₂)) :
    (Structure.reduct f₁).obj ((Structure.reduct (inl f₁ f₂)).obj M) =
      (Structure.reduct f₂).obj ((Structure.reduct (inr f₁ f₂)).obj M) :=
  congrArg (fun k => (Structure.reduct k).obj M) (condition f₁ f₂)

/-! ### Amalgamation of homomorphisms -/

section HomAmalgamation

variable {M N : Structure (pt f₁ f₂)}
  (u : (Structure.reduct (inl f₁ f₂)).obj M ⟶ (Structure.reduct (inl f₁ f₂)).obj N)
  (v : (Structure.reduct (inr f₁ f₂)).obj M ⟶ (Structure.reduct (inr f₁ f₂)).obj N)
  (huv : ∀ s : Sg.S, u.map (f₁.sorts s) ≍ v.map (f₂.sorts s))

/-- The carrier maps of the amalgamation of two homomorphisms. -/
def amMap (x : Sorts f₁ f₂) : M.carrier x → N.carrier x :=
  Quot.hrecOn (motive := fun x => M.carrier x → N.carrier x) x
    (fun t => Sum.rec (motive := fun t => M.carrier (Quot.mk _ t) → N.carrier (Quot.mk _ t))
      (fun s => u.map s) (fun s => v.map s) t)
    (by
      rintro _ _ ⟨s⟩
      exact huv s)

/-- The amalgamation of two homomorphisms agreeing on the common part. -/
def amHom : M ⟶ N where
  map := amMap u v huv
  map_op := by
    intro n w s o args
    obtain ⟨x, hx⟩ := o
    revert hx
    induction x using Quot.ind with
    | mk x =>
      rcases x with ⟨⟨n', w', s'⟩, o'⟩ | ⟨⟨n', w', s'⟩, o'⟩
      · intro hx
        cases hx
        exact u.map_op o' args
      · intro hx
        cases hx
        exact v.map_op o' args
  map_rel := by
    intro n w r args
    obtain ⟨x, hx⟩ := r
    revert hx
    induction x using Quot.ind with
    | mk x =>
      rcases x with ⟨⟨n', w'⟩, r'⟩ | ⟨⟨n', w'⟩, r'⟩
      · intro hx
        cases hx
        exact u.map_rel r' args
      · intro hx
        cases hx
        exact v.map_rel r' args

theorem reduct_inl_amHom : (Structure.reduct (inl f₁ f₂)).map (amHom u v huv) = u := rfl

theorem reduct_inr_amHom : (Structure.reduct (inr f₁ f₂)).map (amHom u v huv) = v := rfl

end HomAmalgamation

theorem amHom_uniq {M N : Structure (pt f₁ f₂)} (m m' : M ⟶ N)
    (h₁ : (Structure.reduct (inl f₁ f₂)).map m = (Structure.reduct (inl f₁ f₂)).map m')
    (h₂ : (Structure.reduct (inr f₁ f₂)).map m = (Structure.reduct (inr f₁ f₂)).map m') :
    m = m' := by
  refine structureHom_ext ?_
  funext x
  induction x using Quot.ind with
  | mk x =>
    rcases x with s | s
    · exact congrArg (fun k => Structure.Hom.map k s) h₁
    · exact congrArg (fun k => Structure.Hom.map k s) h₂

variable (f₁ f₂)

/-- The canonical pushout square of first-order signatures amalgamates. -/
theorem amalgamates : Amalgamates institution f₁ f₂ (inl f₁ f₂) (inr f₁ f₂) := by
  unfold Amalgamates
  refine StrictPullback.isPullback ?_ ?_ ?_ ?_ ?_
  · rw [← StrictPullback.modHom_comp, ← StrictPullback.modHom_comp, condition f₁ f₂]
  · intro M₁ M₂ h
    exact ⟨amalg M₁ M₂ h, reduct_inl_amalg M₁ M₂ h, reduct_inr_amalg M₁ M₂ h⟩
  · intro M M' h₁ h₂
    exact amalg_uniq M M' h₁ h₂
  · intro M N u v huv
    refine ⟨amHom u v (fun s => ?_), reduct_inl_amHom u v _, reduct_inr_amHom u v _⟩
    have key := structureHom_map_heq (reduct_condition M) (reduct_condition N) huv s
    exact key
  · intro M N m m' h₁ h₂
    exact amHom_uniq m m' h₁ h₂

end PO

end Silmaril.Logic.Institution.Examples.FOL

namespace Silmaril.Logic.Institution

open CategoryTheory Limits Examples

/-- The category of many-sorted first-order signatures has pushouts, computed on sorts,
operation symbols and relation symbols.

Source: `goguen-burstall-1992` in `references.bib`, Appendix A2, after
Definition 62 (the category `FoSig`). -/
theorem FOL.hasPushouts : HasPushouts FOL.Signature := by
  have : ∀ {X Y Z : FOL.Signature} {f : X ⟶ Y} {g : X ⟶ Z}, HasColimit (span f g) :=
    fun {_ _ _ f g} => HasColimit.mk ⟨_, FOL.PO.isColimit f g⟩
  exact hasPushouts_of_hasColimit_span _

/-- Many-sorted first-order logic is semi-exact.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §3, Definition 3.10
(PDF page 10: "many sorted logics tend to be exact"). -/
theorem FOL.semiExact : SemiExact FOL.institution := by
  refine StrictPullback.semiExact_of_exists _ ?_
  intro S S₁ S₂ f₁ f₂
  exact ⟨_, _, _, FOL.PO.isPushout f₁ f₂, FOL.PO.amalgamates f₁ f₂⟩

end Silmaril.Logic.Institution
