module

public import Silmaril.Automata.Ops.Defs
public import Silmaril.Automata.Machine.Thms

@[expose] public section

/-!
# Products and coproducts of machines: theorems

PROVED (standard axioms; the proofs are short and inline):

* `prodIsLimit`: `RelMach.prod A B` with `fst`, `snd` is a **categorical product** in `RelMach`
  (`lift_fst`, `lift_snd`, and uniqueness of the pairing);
* `coprodIsColimit`: `RelMach.coprod A B` with `inl`, `inr` is a **categorical coproduct**
  (`inl_desc`, `inr_desc`, uniqueness of the copairing);
* `sync_eq_prod_diag`: the synchronous product of deterministic machines (language
  intersection, `Marked.accepts_prod_iff`) has a transition `(s,t) —l→ (s',t')` iff the
  categorical product has `(s,t) —(l,l)→ (s',t')`: it is the product restricted to diagonal labels.
-/

namespace Silmaril.Automata

open CategoryTheory CategoryTheory.Limits

namespace RelMach

variable {X A B : RelMach}

@[simp] theorem lift_fst (h : X ⟶ A) (k : X ⟶ B) : lift h k ≫ fst A B = h := rfl
@[simp] theorem lift_snd (h : X ⟶ A) (k : X ⟶ B) : lift h k ≫ snd A B = k := rfl

theorem lift_unique {h : X ⟶ A} {k : X ⟶ B} (m : X ⟶ prod A B) (h₁ : m ≫ fst A B = h)
    (h₂ : m ≫ snd A B = k) : m = lift h k := by
  subst h₁ h₂; rfl

/-- **The product of relational machines.** -/
def prodIsLimit (A B : RelMach) : IsLimit (BinaryFan.mk (fst A B) (snd A B)) :=
  BinaryFan.IsLimit.mk _ (fun h k => lift h k) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ m h₁ h₂ => lift_unique m h₁ h₂)

@[simp] theorem inl_desc (h : A ⟶ X) (k : B ⟶ X) : inl A B ≫ desc h k = h := rfl
@[simp] theorem inr_desc (h : A ⟶ X) (k : B ⟶ X) : inr A B ≫ desc h k = k := rfl

theorem desc_unique {h : A ⟶ X} {k : B ⟶ X} (m : coprod A B ⟶ X) (h₁ : inl A B ≫ m = h)
    (h₂ : inr A B ≫ m = k) : m = desc h k := by
  subst h₁ h₂
  apply RelMach.hom_ext
  · funext p; cases p <;> rfl
  · funext l; cases l <;> rfl

/-- **The coproduct of relational machines.** -/
def coprodIsColimit (A B : RelMach) : IsColimit (BinaryCofan.mk (inl A B) (inr A B)) :=
  BinaryCofan.IsColimit.mk _ (fun h k => desc h k) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ m h₁ h₂ => desc_unique m h₁ h₂)

end RelMach

theorem sync_eq_prod_diag {S T L : Type} (M : DMachine S L) (N : DMachine T L) (s s' : S)
    (t t' : T) (l : L) :
    (M.prod N).toLTS.Tr (s, t) l (s', t') ↔
      (RelMach.prod ⟨S, L, M.toLTS⟩ ⟨T, L, N.toLTS⟩).tr.Tr (s, t) (l, l) (s', t') :=
  DMachine.prod_step_iff M N s t l s' t'

end Silmaril.Automata
