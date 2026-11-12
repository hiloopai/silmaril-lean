module

public import Silmaril.Raw.SSA.Isotope.Logic.Metatheory.Theory.Syntax
public import Mathlib.CategoryTheory.Category.Preorder

@[expose] public section

namespace Silmaril.Logic.Metatheory

universe u v w x

/-- A contextual preorder: directed refinement does not assume symmetry. -/
structure RefinementTheory (S : IndexedSyntax.{u, v}) where
  Rel : S.Relation
  refl : ∀ {i} (a : S.Term i), Rel a a
  trans : ∀ {i} {a b c : S.Term i}, Rel a b → Rel b c → Rel a c
  congr : ∀ {i j} {a b : S.Term i} (c : S.Term i → S.Term j),
    S.Context c → Rel a b → Rel (c a) (c b)

/-- A contextual equivalence relation. -/
structure EquationalTheory (S : IndexedSyntax.{u, v}) extends RefinementTheory S where
  symm : ∀ {i} {a b : S.Term i}, Rel a b → Rel b a

namespace RefinementTheory

variable {S : IndexedSyntax.{u, v}} {T : IndexedSyntax.{w, x}}

@[ext] theorem ext {R Q : RefinementTheory S}
    (h : ∀ {i} (a b : S.Term i), R.Rel a b ↔ Q.Rel a b) : R = Q := by
  cases R with
  | mk r rr rt rc =>
    cases Q with
    | mk q qr qt qc =>
      have hr : @r = @q := by funext i a b; exact propext (h a b)
      cases hr
      rfl

instance : PartialOrder (RefinementTheory S) where
  le R Q := ∀ {i} {a b : S.Term i}, R.Rel a b → Q.Rel a b
  le_refl _ := fun h => h
  le_trans _ _ _ h k := fun p => k (h p)
  le_antisymm _ _ h k := ext fun _ _ => ⟨h, k⟩

/-- Replace both arguments of a constructor using its designated one-hole contexts. -/
theorem congr₂ (R : RefinementTheory S) {i j k : S.Index}
    (c : S.Term i → S.Term j → S.Term k)
    (left : ∀ b, S.Context (fun a => c a b))
    (right : ∀ a, S.Context (c a))
    {a a' : S.Term i} {b b' : S.Term j} (ha : R.Rel a a') (hb : R.Rel b b') :
    R.Rel (c a b) (c a' b') :=
  R.trans (R.congr (fun x => c x b) (left b) ha) (R.congr (c a') (right a') hb)

/-- Replace all three arguments, including arguments at different binder sorts. -/
theorem congr₃ (R : RefinementTheory S) {i j k l : S.Index}
    (c : S.Term i → S.Term j → S.Term k → S.Term l)
    (first : ∀ b d, S.Context (fun a => c a b d))
    (second : ∀ a d, S.Context (fun b => c a b d))
    (third : ∀ a b, S.Context (c a b))
    {a a' : S.Term i} {b b' : S.Term j} {d d' : S.Term k}
    (ha : R.Rel a a') (hb : R.Rel b b') (hd : R.Rel d d') :
    R.Rel (c a b d) (c a' b' d') :=
  R.trans (R.congr (fun x => c x b d) (first b d) ha)
    (R.congr₂ (c a') (second a') (third a') hb hd)

/-- Mutual refinement is the equational core of a directed theory. -/
def equationalCore (R : RefinementTheory S) : EquationalTheory S where
  Rel a b := R.Rel a b ∧ R.Rel b a
  refl a := ⟨R.refl a, R.refl a⟩
  trans h k := ⟨R.trans h.1 k.1, R.trans k.2 h.2⟩
  congr c hc h := ⟨R.congr c hc h.1, R.congr c hc h.2⟩
  symm h := h.symm

/-- Pull a theory back along a contextual translation. For typed syntax this
restricts a raw theory to the fibers of typing judgments. -/
def pullback (R : RefinementTheory T) (f : S.Translation T) (hf : f.Contextual) :
    RefinementTheory S where
  Rel a b := R.Rel (f.term a) (f.term b)
  refl a := R.refl (f.term a)
  trans h k := R.trans h k
  congr c hc h := by
    obtain ⟨d, hd, hfd⟩ := hf c hc
    rw [hfd, hfd]
    exact R.congr d hd h

end RefinementTheory

namespace EquationalTheory

variable {S : IndexedSyntax.{u, v}} {T : IndexedSyntax.{w, x}}

@[ext] theorem ext {R Q : EquationalTheory S}
    (h : ∀ {i} (a b : S.Term i), R.Rel a b ↔ Q.Rel a b) : R = Q := by
  cases R
  cases Q
  have hr := RefinementTheory.ext h
  cases hr
  rfl

instance : PartialOrder (EquationalTheory S) where
  le R Q := ∀ {i} {a b : S.Term i}, R.Rel a b → Q.Rel a b
  le_refl _ := fun h => h
  le_trans _ _ _ h k := fun p => k (h p)
  le_antisymm _ _ h k := ext fun _ _ => ⟨h, k⟩

/-- Binary constructor congruence for equations. -/
theorem congr₂ (R : EquationalTheory S) {i j k : S.Index}
    (c : S.Term i → S.Term j → S.Term k)
    (left : ∀ b, S.Context (fun a => c a b))
    (right : ∀ a, S.Context (c a))
    {a a' : S.Term i} {b b' : S.Term j} (ha : R.Rel a a') (hb : R.Rel b b') :
    R.Rel (c a b) (c a' b') := R.toRefinementTheory.congr₂ c left right ha hb

/-- Ternary constructor congruence for equations. -/
theorem congr₃ (R : EquationalTheory S) {i j k l : S.Index}
    (c : S.Term i → S.Term j → S.Term k → S.Term l)
    (first : ∀ b d, S.Context (fun a => c a b d))
    (second : ∀ a d, S.Context (fun b => c a b d))
    (third : ∀ a b, S.Context (c a b))
    {a a' : S.Term i} {b b' : S.Term j} {d d' : S.Term k}
    (ha : R.Rel a a') (hb : R.Rel b b') (hd : R.Rel d d') :
    R.Rel (c a b d) (c a' b' d') :=
  R.toRefinementTheory.congr₃ c first second third ha hb hd

def pullback (R : EquationalTheory T) (f : S.Translation T) (hf : f.Contextual) :
    EquationalTheory S where
  toRefinementTheory := R.toRefinementTheory.pullback f hf
  symm h := R.symm h

@[simp] theorem equationalCore_toRefinementTheory (R : EquationalTheory S) :
    R.toRefinementTheory.equationalCore = R :=
  ext fun _ _ => ⟨And.left, fun h => ⟨h, R.symm h⟩⟩

end EquationalTheory

end Silmaril.Logic.Metatheory
