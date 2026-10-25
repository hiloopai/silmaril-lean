module

public import Silmaril.Logic.HOLLight.Theory
public import Mathlib.Data.Finset.Image

@[expose] public section

/-!
# HOL Light's primitive inference rules

Hypotheses are finite sets of locally nameless formulas. Alpha equivalence of
bound names is already represented by syntactic equality. The ten inference
constructors retain HOL Light's union, discharge, and freshness conditions;
`axiom` is the explicit theory interface. Structural and derived logical rules
are proved from these constructors.
-/

namespace Silmaril.Logic.HOLLight

abbrev Hyps := Finset Tm

def TypedHyps (sig : Signature) (Γ : List Ty) (H : Hyps) : Prop :=
  ∀ p ∈ H, HasType sig Γ p .bool

inductive Derives (sig : Signature) (theory : Theory) : Hyps → Tm → Prop where
  | axiom {p : Tm} (member : p ∈ theory) (typing : HasType sig [] p .bool) :
      Derives sig theory ∅ p
  | refl {t : Tm} {A : Ty} (typing : HasType sig [] t A) :
      Derives sig theory ∅ (Tm.equal A t t)
  | trans {H K : Hyps} {A : Ty} {s t r : Tm} :
      Derives sig theory H (Tm.equal A s t) →
      Derives sig theory K (Tm.equal A t r) →
      Derives sig theory (H ∪ K) (Tm.equal A s r)
  | mkComb {H K : Hyps} {A B : Ty} {f g x y : Tm} :
      Derives sig theory H (Tm.equal (.arr A B) f g) →
      Derives sig theory K (Tm.equal A x y) →
      Derives sig theory (H ∪ K) (Tm.equal B (.app f x) (.app g y))
  | abs {H : Hyps} {A B : Ty} {s t : Tm} (name : Nat)
      (domain : A.WellFormed sig.tyOps) (fresh : ∀ p ∈ H, p.Fresh (name, A)) :
      Derives sig theory H (Tm.equal B s t) →
      Derives sig theory H (Tm.equal (.arr A B)
        (.lam A (s.replaceFree (name, A) (.bvar 0)))
        (.lam A (t.replaceFree (name, A) (.bvar 0))))
  | beta {A B : Ty} {body : Tm} (name : Nat)
      (domain : A.WellFormed sig.tyOps) (typing : HasType sig [A] body B)
      (fresh : body.Fresh (name, A)) :
      Derives sig theory ∅
        (Tm.equal B (.app (.lam A body) (.fvar name A)) (body.open (.fvar name A)))
  | assume {p : Tm} (typing : HasType sig [] p .bool) :
      Derives sig theory {p} p
  | eqMp {H K : Hyps} {p q : Tm} :
      Derives sig theory H (Tm.equal .bool p q) → Derives sig theory K p →
      Derives sig theory (H ∪ K) q
  | deductAntisym {H K : Hyps} {p q : Tm} :
      Derives sig theory H p → Derives sig theory K q →
      Derives sig theory (H.erase q ∪ K.erase p) (Tm.equal .bool p q)
  | inst {H : Hyps} {p : Tm} (σ : Nat → Ty → Tm)
      (typing : ∀ n A, A.WellFormed sig.tyOps → HasType sig [] (σ n A) A) :
      Derives sig theory H p →
      Derives sig theory (H.image (Tm.freeSubst σ)) (p.freeSubst σ)
  | instType {H : Hyps} {p : Tm} (σ : Nat → Ty)
      (typing : ∀ n, (σ n).WellFormed sig.tyOps) :
      Derives sig theory H p →
      Derives sig theory (H.image (Tm.tySubst σ)) (p.tySubst σ)

end Silmaril.Logic.HOLLight
