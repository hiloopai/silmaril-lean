module

public import Silmaril.Logic.HOLLight.Consilience.Semantics
public import Silmaril.Logic.HOLLight.Consistency
public import Silmaril.Logic.HOLLight.Classical.ExcludedMiddle

@[expose] public section

/-! # Defined logical vocabulary and matching classical theories -/
namespace Silmaril.Logic.HOLLight.Consilience

namespace Term

def identity (A : Ty) : Term := .lam A (.bound 0)
def truth : Term := equal (.arr .bool .bool) (identity .bool) (identity .bool)
def all (A : Ty) (P : Term) : Term := equal (.arr A .bool) P (.lam A truth)
def falsity : Term := all .bool (identity .bool)
def conj (p q : Term) : Term :=
  equal (.arr (.arr .bool (.arr .bool .bool)) .bool)
    (.lam (.arr .bool (.arr .bool .bool)) (.app (.app (.bound 0) p.weaken) q.weaken))
    (.lam (.arr .bool (.arr .bool .bool)) (.app (.app (.bound 0) truth) truth))
def imp (p q : Term) : Term := equal .bool (conj p q) p
def neg (p : Term) : Term := imp p falsity
def disj (p q : Term) : Term :=
  all .bool (.lam .bool
    (imp (imp p.weaken (.bound 0)) (imp (imp q.weaken (.bound 0)) (.bound 0))))
def ex (A : Ty) (P : Term) : Term :=
  all .bool (.lam .bool
    (imp (all A (.lam A (imp (.app P.weaken.weaken (.bound 0)) (.bound 1)))) (.bound 0)))
def injective (A B : Ty) (f : Term) : Term :=
  all A (.lam A (all A (.lam A
    (imp (equal B (.app f.weaken.weaken (.bound 1)) (.app f.weaken.weaken (.bound 0)))
      (equal A (.bound 1) (.bound 0))))))
def surjective (A B : Ty) (f : Term) : Term :=
  all B (.lam B (ex A (.lam A (equal B (.app f.weaken.weaken (.bound 0)) (.bound 1)))))
def infinity : Term :=
  ex (.arr .ind .ind) (.lam (.arr .ind .ind)
    (conj (injective .ind .ind (.bound 0)) (neg (surjective .ind .ind (.bound 0)))))
def eta (A B : Ty) (f : Term) : Term := equal (.arr A B) (.lam A (.app f.weaken (.bound 0))) f
def selection (A : Ty) (P x : Term) : Term := imp (.app P x) (.app P (.app (.choice A) P))

@[simp] theorem encode_identity (A : Ty) : (identity A).encode = Tm.identity A := rfl
@[simp] theorem encode_truth : truth.encode = Tm.truth := rfl
@[simp] theorem encode_all (A : Ty) (P : Term) : (all A P).encode = Tm.all A P.encode := rfl
@[simp] theorem encode_falsity : falsity.encode = Tm.falsity := rfl
@[simp] theorem encode_conj (p q : Term) : (conj p q).encode = Tm.conj p.encode q.encode := by
  simp [conj, Tm.conj, encode]
@[simp] theorem encode_imp (p q : Term) : (imp p q).encode = Tm.imp p.encode q.encode := by
  simp [imp, Tm.imp]
@[simp] theorem encode_neg (p : Term) : (neg p).encode = Tm.neg p.encode := by simp [neg, Tm.neg]
@[simp] theorem encode_disj (p q : Term) : (disj p q).encode = Tm.disj p.encode q.encode := by
  simp [disj, Tm.disj, encode]
@[simp] theorem encode_ex (A : Ty) (P : Term) : (ex A P).encode = Tm.ex A P.encode := by
  simp [ex, Tm.ex, encode]
@[simp] theorem encode_injectivity (A B : Ty) (f : Term) :
    (injective A B f).encode = Tm.injective A B f.encode := by
  simp [injective, Tm.injective, encode]
@[simp] theorem encode_surjective (A B : Ty) (f : Term) :
    (surjective A B f).encode = Tm.surjective A B f.encode := by
  simp [surjective, Tm.surjective, encode]
@[simp] theorem encode_infinity : infinity.encode = Tm.infinity := by
  simp [infinity, Tm.infinity, encode]
@[simp] theorem encode_eta (A B : Ty) (f : Term) : (eta A B f).encode = Tm.eta A B f.encode := by
  simp [eta, Tm.eta, encode]
@[simp] theorem encode_selection (A : Ty) (P x : Term) :
    (selection A P x).encode = Tm.selection A P.encode x.encode := by
  simp [selection, Tm.selection, Tm.select, encode]
end Term

namespace Typed

theorem equal {sig Γ A s t} (hA : A.WellFormed sig.tyOps)
    (hs : Typed sig Γ s A) (ht : Typed sig Γ t A) : Typed sig Γ (Term.equal A s t) .bool :=
  .app (.app (.equality hA) hs) ht

theorem neg {sig Γ p} (hp : Typed sig Γ p .bool) : Typed sig Γ (Term.neg p) .bool := by
  apply Typed.encode_iff.mp
  simpa using hp.encode.neg

theorem imp {sig Γ p q} (hp : Typed sig Γ p .bool) (hq : Typed sig Γ q .bool) :
    Typed sig Γ (Term.imp p q) .bool := by
  apply Typed.encode_iff.mp
  simpa using hp.encode.imp hq.encode

theorem ex {sig Γ A P} (hA : A.WellFormed sig.tyOps) (hp : Typed sig Γ P (.arr A .bool)) :
    Typed sig Γ (Term.ex A P) .bool := by
  apply Typed.encode_iff.mp
  simpa using HasType.ex hA hp.encode

end Typed

/-- The second presentation includes exactly eta, selection and infinity. -/
def classicalTheory : Theory :=
  [Term.eta (.var 0) (.var 1) (.free 0 (.arr (.var 0) (.var 1))),
   Term.selection (.var 0) (.free 0 (.arr (.var 0) .bool)) (.free 1 (.var 0)),
   Term.infinity]

@[simp] theorem encode_classicalTheory : encodeTheory classicalTheory = HOLLight.classicalTheory := by
  simp [encodeTheory, classicalTheory, HOLLight.classicalTheory, Term.encode]

/-- Actual object-level excluded middle transported from the choice development. -/
theorem excludedMiddle {sig p} (typing : Typed sig [] p .bool) :
    Nonempty (Proof sig classicalTheory ∅ (Term.disj p (Term.neg p))) := by
  apply Proof.encode_iff.mp
  simpa using Derives.excludedMiddle typing.encode

/-- Eta requires the explicit classical theory and well-formed source types. -/
theorem eta {sig A B f} (hA : A.WellFormed sig.tyOps) (hB : B.WellFormed sig.tyOps)
    (typing : Typed sig [] f (.arr A B)) :
    Nonempty (Proof sig classicalTheory ∅ (Term.eta A B f)) := by
  apply Proof.encode_iff.mp
  simpa using Derives.eta hA hB typing.encode

theorem selection {sig A P x} (hA : A.WellFormed sig.tyOps)
    (hP : Typed sig [] P (.arr A .bool)) (hx : Typed sig [] x A) :
    Nonempty (Proof sig classicalTheory ∅ (Term.selection A P x)) := by
  apply Proof.encode_iff.mp
  simpa using Derives.selection hA hP.encode hx.encode

/-- Infinity is an object axiom in both presentations, not an extra Lean axiom. -/
def infinityProof (sig : Signature) : Proof sig classicalTheory ∅ Term.infinity :=
  .ax (by simp [classicalTheory]) (by
    apply Typed.encode_iff.mp
    simpa using (HasType.infinity (sig := sig)))

/-- Consistency follows from the shared standard model and actual proof translation. -/
theorem classical_consistent : ¬ Nonempty (Proof initialSignature classicalTheory ∅ Term.falsity) := by
  intro ⟨h⟩
  apply HOLLight.classical_consistent
  simpa using h.encode

end Silmaril.Logic.HOLLight.Consilience
