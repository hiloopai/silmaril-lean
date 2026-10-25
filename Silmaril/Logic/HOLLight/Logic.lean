module

public import Silmaril.Logic.HOLLight.Substitution
public import Silmaril.Logic.HOLLight.Typing

@[expose] public section

/-!
# Defined logical vocabulary

The only primitive logical constants are equality and selection. All the
following terms are abbreviations in that language, following HOL Light's
definitions in `bool.ml`. Quantifiers take a predicate function, so a binder
`∀ x : A, b` is represented by `all A (lam A b)`.

No additional logical inference rule or semantic truth test is hidden in these
definitions. In particular, disjunction and existence use their constructive
Church encodings; classical reasoning is derived using selection separately.
-/

namespace Silmaril.Logic.HOLLight
namespace Tm

/-- The polymorphic identity function, with an explicit domain. -/
def identity (A : Ty) : Tm := .lam A (.bvar 0)

/-- Truth is reflexivity of the Boolean identity function. -/
def truth : Tm := equal (.arr .bool .bool) (identity .bool) (identity .bool)

/-- Universal quantification says that the predicate is constantly true. -/
def all (A : Ty) (P : Tm) : Tm :=
  equal (.arr A .bool) P (.lam A truth)

/-- Falsity is the assertion that every Boolean is true. -/
def falsity : Tm := all .bool (identity .bool)

/-- Conjunction is equality of the two Boolean-pair eliminators. -/
def conj (p q : Tm) : Tm :=
  equal (.arr (.arr .bool (.arr .bool .bool)) .bool)
    (.lam (.arr .bool (.arr .bool .bool)) (.app (.app (.bvar 0) p.weaken) q.weaken))
    (.lam (.arr .bool (.arr .bool .bool)) (.app (.app (.bvar 0) truth) truth))

/-- Implication is the order on Booleans induced by conjunction. -/
def imp (p q : Tm) : Tm := equal .bool (conj p q) p

def neg (p : Tm) : Tm := imp p falsity

/-- Constructive disjunction: every common consequence is a consequence. -/
def disj (p q : Tm) : Tm :=
  all .bool (.lam .bool
    (imp (imp p.weaken (.bvar 0)) (imp (imp q.weaken (.bvar 0)) (.bvar 0))))

/-- Constructive existential quantification. -/
def ex (A : Ty) (P : Tm) : Tm :=
  all .bool (.lam .bool
    (imp (all A (.lam A (imp (.app P.weaken.weaken (.bvar 0)) (.bvar 1))))
      (.bvar 0)))

/-- The usual injectivity formula. -/
def injective (A B : Ty) (f : Tm) : Tm :=
  all A (.lam A (all A (.lam A
    (imp (equal B (.app f.weaken.weaken (.bvar 1)) (.app f.weaken.weaken (.bvar 0)))
      (equal A (.bvar 1) (.bvar 0))))))

/-- The usual surjectivity formula. -/
def surjective (A B : Ty) (f : Tm) : Tm :=
  all B (.lam B (ex A (.lam A
    (equal B (.app f.weaken.weaken (.bvar 0)) (.bvar 1)))))

/-- The standard infinity assertion: an injective, non-surjective endomap. -/
def infinity : Tm :=
  ex (.arr .ind .ind) (.lam (.arr .ind .ind)
    (conj (injective .ind .ind (.bvar 0)) (neg (surjective .ind .ind (.bvar 0)))))

/-- A standard eta axiom instance. -/
def eta (A B : Ty) (f : Tm) : Tm :=
  equal (.arr A B) (.lam A (.app f.weaken (.bvar 0))) f

/-- A standard selection axiom instance. -/
def selection (A : Ty) (P x : Tm) : Tm :=
  imp (.app P x) (.app P (select A P))

/-- Ordered finite conjunction, with truth as the empty conjunction. -/
def andList : List Tm → Tm
  | [] => truth
  | p :: ps => conj p (andList ps)

@[simp] theorem andList_nil : andList [] = truth := rfl

@[simp] theorem andList_cons (p : Tm) (ps : List Tm) :
    andList (p :: ps) = conj p (andList ps) := rfl

/-- Ordered finite disjunction, with falsity as the empty disjunction. -/
def orList : List Tm → Tm
  | [] => falsity
  | p :: ps => disj p (orList ps)

@[simp] theorem orList_nil : orList [] = falsity := rfl

@[simp] theorem orList_cons (p : Tm) (ps : List Tm) :
    orList (p :: ps) = disj p (orList ps) := rfl

@[simp] theorem freeVars_truth : truth.freeVars = [] := rfl

@[simp] theorem freeVars_falsity : falsity.freeVars = [] := rfl

@[simp] theorem freeVars_all (A : Ty) (P : Tm) : (all A P).freeVars = P.freeVars := by
  simp [all, equal, freeVars]

@[simp] theorem freeVars_conj (p q : Tm) : (conj p q).freeVars = p.freeVars ++ q.freeVars := by
  simp [conj, equal, freeVars]

@[simp] theorem freeVars_infinity : infinity.freeVars = [] := by
  simp [infinity, injective, surjective, ex, neg, imp, equal, freeVars]

@[simp] theorem rename_equal (ρ : Nat → Nat) (A : Ty) (p q : Tm) :
    (equal A p q).rename ρ = equal A (p.rename ρ) (q.rename ρ) := rfl

@[simp] theorem rename_truth (ρ : Nat → Nat) : truth.rename ρ = truth := rfl

@[simp] theorem rename_falsity (ρ : Nat → Nat) : falsity.rename ρ = falsity := rfl

@[simp] theorem rename_all (ρ : Nat → Nat) (A : Ty) (P : Tm) :
    (all A P).rename ρ = all A (P.rename ρ) := by
  simp only [all, rename_equal, rename, rename_truth]

/-- A renaming under a fresh binder agrees with weakening after renaming. -/
theorem rename_weaken (ρ : Nat → Nat) (t : Tm) :
    t.weaken.rename (DeBruijn.lift ρ) = (t.rename ρ).weaken := by
  simp only [weaken, rename_comp]
  rfl

@[simp] theorem rename_conj (ρ : Nat → Nat) (p q : Tm) :
    (conj p q).rename ρ = conj (p.rename ρ) (q.rename ρ) := by
  simp only [conj, rename_equal, rename, DeBruijn.lift, rename_weaken, rename_truth]

@[simp] theorem rename_imp (ρ : Nat → Nat) (p q : Tm) :
    (imp p q).rename ρ = imp (p.rename ρ) (q.rename ρ) := by
  simp only [imp, rename_equal, rename_conj]

@[simp] theorem rename_neg (ρ : Nat → Nat) (p : Tm) :
    (neg p).rename ρ = neg (p.rename ρ) := by
  simp only [neg, rename_imp, rename_falsity]

@[simp] theorem rename_disj (ρ : Nat → Nat) (p q : Tm) :
    (disj p q).rename ρ = disj (p.rename ρ) (q.rename ρ) := by
  simp only [disj, rename_all, rename, rename_imp, DeBruijn.lift, rename_weaken]

@[simp] theorem rename_ex (ρ : Nat → Nat) (A : Ty) (P : Tm) :
    (ex A P).rename ρ = ex A (P.rename ρ) := by
  simp only [ex, rename_all, rename, rename_imp, DeBruijn.lift, rename_weaken]

@[simp] theorem subst_equal (σ : Nat → Tm) (A : Ty) (p q : Tm) :
    (equal A p q).subst σ = equal A (p.subst σ) (q.subst σ) := rfl

@[simp] theorem subst_truth (σ : Nat → Tm) : truth.subst σ = truth := rfl

@[simp] theorem subst_falsity (σ : Nat → Tm) : falsity.subst σ = falsity := rfl

@[simp] theorem subst_all (σ : Nat → Tm) (A : Ty) (P : Tm) :
    (all A P).subst σ = all A (P.subst σ) := by
  simp only [all, subst_equal, subst, subst_truth]

theorem subst_weaken (σ : Nat → Tm) (t : Tm) :
    t.weaken.subst (liftSub σ) = (t.subst σ).weaken := by
  simp only [weaken, subst_rename, rename_subst]
  rfl

@[simp] theorem subst_conj (σ : Nat → Tm) (p q : Tm) :
    (conj p q).subst σ = conj (p.subst σ) (q.subst σ) := by
  simp only [conj, subst_equal, subst, liftSub, subst_weaken, subst_truth]

@[simp] theorem subst_imp (σ : Nat → Tm) (p q : Tm) :
    (imp p q).subst σ = imp (p.subst σ) (q.subst σ) := by
  simp only [imp, subst_equal, subst_conj]

@[simp] theorem subst_neg (σ : Nat → Tm) (p : Tm) :
    (neg p).subst σ = neg (p.subst σ) := by
  simp only [neg, subst_imp, subst_falsity]

@[simp] theorem subst_disj (σ : Nat → Tm) (p q : Tm) :
    (disj p q).subst σ = disj (p.subst σ) (q.subst σ) := by
  simp only [disj, subst_all, subst, subst_imp, liftSub, subst_weaken]

@[simp] theorem subst_ex (σ : Nat → Tm) (A : Ty) (P : Tm) :
    (ex A P).subst σ = ex A (P.subst σ) := by
  simp only [ex, subst_all, subst, subst_imp, liftSub, subst_weaken]
  rfl

@[simp] theorem freeSubst_equal (σ : Nat → Ty → Tm) (A : Ty) (p q : Tm) :
    (equal A p q).freeSubst σ = equal A (p.freeSubst σ) (q.freeSubst σ) := rfl

@[simp] theorem freeSubst_truth (σ : Nat → Ty → Tm) : truth.freeSubst σ = truth := rfl

@[simp] theorem freeSubst_falsity (σ : Nat → Ty → Tm) : falsity.freeSubst σ = falsity := rfl

@[simp] theorem freeSubst_all (σ : Nat → Ty → Tm) (A : Ty) (P : Tm) :
    (all A P).freeSubst σ = all A (P.freeSubst σ) := by
  simp only [all, freeSubst_equal, freeSubst, freeSubst_truth]

theorem freeSubst_weaken (σ : Nat → Ty → Tm) (t : Tm) :
    t.weaken.freeSubst (fun n A => (σ n A).weaken) = (t.freeSubst σ).weaken :=
  (rename_freeSubst Nat.succ σ t).symm

@[simp] theorem freeSubst_conj (σ : Nat → Ty → Tm) (p q : Tm) :
    (conj p q).freeSubst σ = conj (p.freeSubst σ) (q.freeSubst σ) := by
  simp only [conj, freeSubst_equal, freeSubst, freeSubst_weaken, freeSubst_truth]

@[simp] theorem freeSubst_imp (σ : Nat → Ty → Tm) (p q : Tm) :
    (imp p q).freeSubst σ = imp (p.freeSubst σ) (q.freeSubst σ) := by
  simp only [imp, freeSubst_equal, freeSubst_conj]

@[simp] theorem freeSubst_neg (σ : Nat → Ty → Tm) (p : Tm) :
    (neg p).freeSubst σ = neg (p.freeSubst σ) := by
  simp only [neg, freeSubst_imp, freeSubst_falsity]

@[simp] theorem freeSubst_disj (σ : Nat → Ty → Tm) (p q : Tm) :
    (disj p q).freeSubst σ = disj (p.freeSubst σ) (q.freeSubst σ) := by
  simp only [disj, freeSubst_all, freeSubst, freeSubst_imp, freeSubst_weaken]

@[simp] theorem freeSubst_ex (σ : Nat → Ty → Tm) (A : Ty) (P : Tm) :
    (ex A P).freeSubst σ = ex A (P.freeSubst σ) := by
  simp only [ex, freeSubst_all, freeSubst, freeSubst_imp, freeSubst_weaken]

@[simp] theorem tySubst_equal (σ : Nat → Ty) (A : Ty) (p q : Tm) :
    (equal A p q).tySubst σ = equal (A.subst σ) (p.tySubst σ) (q.tySubst σ) := rfl

@[simp] theorem tySubst_truth (σ : Nat → Ty) : truth.tySubst σ = truth := by
  simp [truth, identity, tySubst_equal, tySubst]

@[simp] theorem tySubst_falsity (σ : Nat → Ty) : falsity.tySubst σ = falsity := by
  simp [falsity, all, identity, tySubst_equal, tySubst]

@[simp] theorem tySubst_all (σ : Nat → Ty) (A : Ty) (P : Tm) :
    (all A P).tySubst σ = all (A.subst σ) (P.tySubst σ) := by
  simp [all, tySubst_equal, tySubst]

@[simp] theorem tySubst_weaken (σ : Nat → Ty) (t : Tm) :
    t.weaken.tySubst σ = (t.tySubst σ).weaken := tySubst_rename σ Nat.succ t

@[simp] theorem tySubst_conj (σ : Nat → Ty) (p q : Tm) :
    (conj p q).tySubst σ = conj (p.tySubst σ) (q.tySubst σ) := by
  simp only [conj, tySubst_equal, tySubst, Ty.subst, tySubst_weaken, tySubst_truth]

@[simp] theorem tySubst_imp (σ : Nat → Ty) (p q : Tm) :
    (imp p q).tySubst σ = imp (p.tySubst σ) (q.tySubst σ) := by
  simp only [imp, tySubst_equal, Ty.subst, tySubst_conj]

@[simp] theorem tySubst_neg (σ : Nat → Ty) (p : Tm) :
    (neg p).tySubst σ = neg (p.tySubst σ) := by
  simp only [neg, tySubst_imp, tySubst_falsity]

@[simp] theorem tySubst_disj (σ : Nat → Ty) (p q : Tm) :
    (disj p q).tySubst σ = disj (p.tySubst σ) (q.tySubst σ) := by
  simp only [disj, tySubst_all, tySubst, Ty.subst, tySubst_imp, tySubst_weaken]

@[simp] theorem tySubst_ex (σ : Nat → Ty) (A : Ty) (P : Tm) :
    (ex A P).tySubst σ = ex (A.subst σ) (P.tySubst σ) := by
  simp only [ex, tySubst_all, tySubst, Ty.subst, tySubst_imp, tySubst_weaken]

@[simp] theorem tySubst_select (σ : Nat → Ty) (A : Ty) (P : Tm) :
    (select A P).tySubst σ = select (A.subst σ) (P.tySubst σ) := rfl

@[simp] theorem freeSubst_select (σ : Nat → Ty → Tm) (A : Ty) (P : Tm) :
    (select A P).freeSubst σ = select A (P.freeSubst σ) := rfl

@[simp] theorem tySubst_selection (σ : Nat → Ty) (A : Ty) (P x : Tm) :
    (selection A P x).tySubst σ =
      selection (A.subst σ) (P.tySubst σ) (x.tySubst σ) := by
  simp only [selection, tySubst_imp, tySubst, tySubst_select]

@[simp] theorem freeSubst_selection (σ : Nat → Ty → Tm) (A : Ty) (P x : Tm) :
    (selection A P x).freeSubst σ = selection A (P.freeSubst σ) (x.freeSubst σ) := by
  simp only [selection, freeSubst_imp, freeSubst, freeSubst_select]

@[simp] theorem tySubst_eta (σ : Nat → Ty) (A B : Ty) (f : Tm) :
    (eta A B f).tySubst σ = eta (A.subst σ) (B.subst σ) (f.tySubst σ) := by
  simp only [eta, tySubst_equal, tySubst, Ty.subst_arr, tySubst_weaken]

@[simp] theorem freeSubst_eta (σ : Nat → Ty → Tm) (A B : Ty) (f : Tm) :
    (eta A B f).freeSubst σ = eta A B (f.freeSubst σ) := by
  simp only [eta, freeSubst_equal, freeSubst, freeSubst_weaken]

end Tm

namespace HasType

private theorem wfBool (ops : List Nat) : Ty.bool.WellFormed ops := by simp [Ty.WellFormed]
private theorem wfInd (ops : List Nat) : Ty.ind.WellFormed ops := by simp [Ty.WellFormed]
private theorem wfArr {ops : List Nat} {A B : Ty}
    (hA : A.WellFormed ops) (hB : B.WellFormed ops) : (Ty.arr A B).WellFormed ops := by
  simpa only [Ty.WellFormed] using And.intro hA hB

variable {sig : Signature} {Γ : List Ty} {A B : Ty} {p q P f x : Tm}

theorem identity (hA : A.WellFormed sig.tyOps) :
    HasType sig Γ (Tm.identity A) (.arr A A) :=
  .lam hA (.bvar rfl hA)

theorem truth : HasType sig Γ Tm.truth .bool :=
  .equal (wfArr (wfBool _) (wfBool _)) (identity (wfBool _)) (identity (wfBool _))

theorem all (hA : A.WellFormed sig.tyOps) (hP : HasType sig Γ P (.arr A .bool)) :
    HasType sig Γ (Tm.all A P) .bool :=
  .equal (wfArr hA (wfBool _)) hP (.lam hA truth)

theorem falsity : HasType sig Γ Tm.falsity .bool :=
  all (wfBool _) (identity (wfBool _))

theorem conj (hp : HasType sig Γ p .bool) (hq : HasType sig Γ q .bool) :
    HasType sig Γ (Tm.conj p q) .bool := by
  have wf : (Ty.arr .bool (.arr .bool .bool)).WellFormed sig.tyOps :=
    wfArr (wfBool _) (wfArr (wfBool _) (wfBool _))
  exact .equal (wfArr wf (wfBool _))
    (.lam wf (.app (.app (.bvar rfl wf) (hp.weaken _)) (hq.weaken _)))
    (.lam wf (.app (.app (.bvar rfl wf) truth) truth))

theorem imp (hp : HasType sig Γ p .bool) (hq : HasType sig Γ q .bool) :
    HasType sig Γ (Tm.imp p q) .bool :=
  .equal (wfBool _) (hp.conj hq) hp

theorem neg (hp : HasType sig Γ p .bool) : HasType sig Γ (Tm.neg p) .bool :=
  hp.imp falsity

theorem disj (hp : HasType sig Γ p .bool) (hq : HasType sig Γ q .bool) :
    HasType sig Γ (Tm.disj p q) .bool :=
  all (wfBool _) (.lam (wfBool _)
    (((hp.weaken .bool).imp (.bvar rfl (wfBool _))).imp
      (((hq.weaken .bool).imp (.bvar rfl (wfBool _))).imp (.bvar rfl (wfBool _)))))

theorem ex (hA : A.WellFormed sig.tyOps) (hP : HasType sig Γ P (.arr A .bool)) :
    HasType sig Γ (Tm.ex A P) .bool :=
  all (wfBool _) (.lam (wfBool _)
    ((all hA (.lam hA
      ((HasType.app ((hP.weaken .bool).weaken A) (.bvar rfl hA)).imp
        (.bvar rfl (wfBool _))))).imp (.bvar rfl (wfBool _))))

theorem injective (hA : A.WellFormed sig.tyOps) (hB : B.WellFormed sig.tyOps)
    (hf : HasType sig Γ f (.arr A B)) : HasType sig Γ (Tm.injective A B f) .bool :=
  all hA (.lam hA (all hA (.lam hA
    ((equal hB (.app ((hf.weaken A).weaken A) (.bvar rfl hA))
      (.app ((hf.weaken A).weaken A) (.bvar rfl hA))).imp
      (equal hA (.bvar rfl hA) (.bvar rfl hA))))))

theorem surjective (hA : A.WellFormed sig.tyOps) (hB : B.WellFormed sig.tyOps)
    (hf : HasType sig Γ f (.arr A B)) : HasType sig Γ (Tm.surjective A B f) .bool :=
  all hB (.lam hB (ex hA (.lam hA
    (equal hB (.app ((hf.weaken B).weaken A) (.bvar rfl hA)) (.bvar rfl hB)))))

theorem infinity : HasType sig Γ Tm.infinity .bool :=
  ex (wfArr (wfInd _) (wfInd _)) (.lam (wfArr (wfInd _) (wfInd _))
    ((injective (wfInd _) (wfInd _) (.bvar rfl (wfArr (wfInd _) (wfInd _)))).conj
      (surjective (wfInd _) (wfInd _) (.bvar rfl (wfArr (wfInd _) (wfInd _)))).neg))

theorem select (hA : A.WellFormed sig.tyOps) (hP : HasType sig Γ P (.arr A .bool)) :
    HasType sig Γ (Tm.select A P) A :=
  .app (.const (.select hA)) hP

theorem eta (hA : A.WellFormed sig.tyOps) (hB : B.WellFormed sig.tyOps)
    (hf : HasType sig Γ f (.arr A B)) : HasType sig Γ (Tm.eta A B f) .bool :=
  equal (wfArr hA hB) (.lam hA (.app (hf.weaken A) (.bvar rfl hA))) hf

theorem selection (hA : A.WellFormed sig.tyOps) (hP : HasType sig Γ P (.arr A .bool))
    (hx : HasType sig Γ x A) : HasType sig Γ (Tm.selection A P x) .bool :=
  (HasType.app hP hx).imp (.app hP (select hA hP))

theorem andList {ps : List Tm} (typed : ∀ p ∈ ps, HasType sig Γ p .bool) :
    HasType sig Γ (Tm.andList ps) .bool := by
  induction ps with
  | nil => exact truth
  | cons p ps ih =>
    exact (typed p (List.mem_cons_self ..)).conj
      (ih (fun q hq => typed q (List.mem_cons_of_mem p hq)))

theorem orList {ps : List Tm} (typed : ∀ p ∈ ps, HasType sig Γ p .bool) :
    HasType sig Γ (Tm.orList ps) .bool := by
  induction ps with
  | nil => exact falsity
  | cons p ps ih =>
    exact (typed p (List.mem_cons_self ..)).disj
      (ih (fun q hq => typed q (List.mem_cons_of_mem p hq)))

end HasType
end Silmaril.Logic.HOLLight
