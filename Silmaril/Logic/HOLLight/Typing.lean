module

public import Silmaril.Logic.HOLLight.Term
public import Silmaril.Logic.HOLLight.Substitution
public import Mathlib.Tactic.Cases

@[expose] public section

/-!
# Declarative typing for HOL Light

Typing is independent of a checking algorithm. Constant instances carry all
their type arguments, and their finite schemes are checked for hidden variables.
-/

namespace Silmaril.Logic.HOLLight

inductive Const.HasType (sig : Signature) : Const → Ty → Prop where
  | eq {A : Ty} (wf : A.WellFormed sig.tyOps) :
      HasType sig (.eq A) (.arr A (.arr A .bool))
  | select {A : Ty} (wf : A.WellFormed sig.tyOps) :
      HasType sig (.select A) (.arr (.arr A .bool) A)
  | user {c : Nat} {s : Scheme} {As : List Ty}
      (lookup : sig.consts[c]? = some s) (scheme : s.WellFormed sig.tyOps)
      (arity : As.length = s.arity) (args : ∀ A ∈ As, A.WellFormed sig.tyOps) :
      HasType sig (.user c As) (Ty.instantiate As s.body)

inductive HasType (sig : Signature) : List Ty → Tm → Ty → Prop where
  | bvar {Γ : List Ty} {i : Nat} {A : Ty}
      (lookup : Γ[i]? = some A) (wf : A.WellFormed sig.tyOps) :
      HasType sig Γ (.bvar i) A
  | fvar {Γ : List Ty} (name : Nat) {A : Ty} (wf : A.WellFormed sig.tyOps) :
      HasType sig Γ (.fvar name A) A
  | const {Γ : List Ty} {c : Const} {A : Ty} (typing : c.HasType sig A) :
      HasType sig Γ (.const c) A
  | app {Γ : List Ty} {f x : Tm} {A B : Ty} :
      HasType sig Γ f (.arr A B) → HasType sig Γ x A → HasType sig Γ (.app f x) B
  | lam {Γ : List Ty} {A B : Ty} {body : Tm} (wf : A.WellFormed sig.tyOps) :
      HasType sig (A :: Γ) body B → HasType sig Γ (.lam A body) (.arr A B)

theorem Const.HasType.unique {sig : Signature} {c : Const} {A B : Ty}
    (left : c.HasType sig A) (right : c.HasType sig B) : A = B := by
  cases left with
  | eq wf => cases right; rfl
  | select wf => cases right; rfl
  | user lookup scheme arity args =>
      cases right with
      | user lookup' scheme' arity' args' =>
          have same := Option.some.inj (lookup.symm.trans lookup')
          cases same
          rfl

theorem Const.HasType.wf {sig : Signature} {c : Const} {A : Ty}
    (typing : c.HasType sig A) : A.WellFormed sig.tyOps := by
  cases typing with
  | eq hA => simpa only [Ty.WellFormed, and_true] using And.intro hA hA
  | select hA => simpa only [Ty.WellFormed, and_true] using And.intro hA hA
  | user lookup scheme arity args => exact scheme.1.instantiate args

theorem Const.HasType.tySubst {sig : Signature} {c : Const} {A : Ty}
    (typing : c.HasType sig A) (σ : Nat → Ty)
    (hσ : ∀ i, (σ i).WellFormed sig.tyOps) :
    (c.tySubst σ).HasType sig (A.subst σ) := by
  cases typing with
  | eq hA => simpa only [Const.tySubst, Ty.subst_arr, Ty.subst_bool] using
      (Const.HasType.eq (hA.subst hσ))
  | select hA => simpa only [Const.tySubst, Ty.subst_arr, Ty.subst_bool] using
      (Const.HasType.select (hA.subst hσ))
  | @user c s As lookup scheme arity args =>
      rw [Ty.subst_instantiate scheme.2 arity]
      apply HasType.user lookup scheme
      · simpa only [List.length_map] using arity
      · intro A hA
        obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hA
        exact (args B hB).subst hσ

namespace HasType

theorem wf {sig : Signature} {Γ : List Ty} {t : Tm} {A : Ty}
    (typing : HasType sig Γ t A) : A.WellFormed sig.tyOps := by
  induction typing with
  | bvar _ hA | fvar _ hA => exact hA
  | const h => exact h.wf
  | app _ _ ihf _ => exact (show _ ∧ _ from (by simpa only [Ty.WellFormed] using ihf)).2
  | lam hA _ ih => simpa only [Ty.WellFormed] using And.intro hA ih

theorem tySubst {sig : Signature} {Γ : List Ty} {t : Tm} {A : Ty}
    (typing : HasType sig Γ t A) (σ : Nat → Ty)
    (hσ : ∀ i, (σ i).WellFormed sig.tyOps) :
    HasType sig (Γ.map (Ty.subst σ)) (t.tySubst σ) (A.subst σ) := by
  induction typing with
  | bvar lookup hA =>
      exact .bvar (by simp only [List.getElem?_map, lookup, Option.map_some]) (hA.subst hσ)
  | fvar n hA => exact .fvar n (hA.subst hσ)
  | const h => exact .const (h.tySubst σ hσ)
  | app _ _ ihf ihx => exact .app (by simpa only [Ty.subst_arr] using ihf) ihx
  | lam hA _ ih => simpa only [Tm.tySubst, Ty.subst_arr] using
      (HasType.lam (hA.subst hσ) ih)

theorem unique {sig : Signature} {Γ : List Ty} {t : Tm} {A B : Ty}
    (left : HasType sig Γ t A) (right : HasType sig Γ t B) : A = B := by
  induction left generalizing B with
  | bvar lookup wf =>
      cases right with
      | bvar lookup' wf' => exact Option.some.inj (lookup.symm.trans lookup')
  | fvar n wf => cases right; rfl
  | const hc => cases right with | const hc' => exact hc.unique hc'
  | app hf hx ihf ihx =>
      cases right with
      | app hf' hx' => exact (Ty.arr.inj (ihf hf')).2
  | lam wf hb ih =>
      cases right with
      | lam wf' hb' => exact congrArg _ (ih hb')

theorem rename {sig : Signature} {Γ Δ : List Ty} {t : Tm} {A : Ty}
    (typing : HasType sig Γ t A) (ρ : Nat → Nat)
    (compatible : ∀ i B, Γ[i]? = some B → Δ[ρ i]? = some B) :
    HasType sig Δ (t.rename ρ) A := by
  induction typing generalizing Δ ρ with
  | bvar lookup wf => exact .bvar (compatible _ _ lookup) wf
  | fvar n wf => exact .fvar n wf
  | const hc => exact .const hc
  | app _ _ ihf ihx => exact .app (ihf ρ compatible) (ihx ρ compatible)
  | @lam Γ A B body wf hb ih =>
      apply HasType.lam wf
      apply ih (DeBruijn.lift ρ)
      intro i C hi
      cases i with
      | zero => simpa only [List.getElem?_cons_zero, DeBruijn.lift] using hi
      | succ i => exact compatible i C hi

theorem weaken {sig : Signature} {Γ : List Ty} {t : Tm} {A : Ty}
    (typing : HasType sig Γ t A) (B : Ty) : HasType sig (B :: Γ) t.weaken A :=
  typing.rename Nat.succ (fun _ _ h => h)

theorem subst {sig : Signature} {Γ Δ : List Ty} {t : Tm} {A : Ty}
    (typing : HasType sig Γ t A) (σ : Nat → Tm)
    (compatible : ∀ i B, Γ[i]? = some B → B.WellFormed sig.tyOps →
      HasType sig Δ (σ i) B) : HasType sig Δ (t.subst σ) A := by
  induction typing generalizing Δ σ with
  | bvar lookup wf => exact compatible _ _ lookup wf
  | fvar n wf => exact .fvar n wf
  | const hc => exact .const hc
  | app _ _ ihf ihx => exact .app (ihf σ compatible) (ihx σ compatible)
  | @lam Γ A B body wf hb ih =>
      apply HasType.lam wf
      apply ih (Tm.liftSub σ)
      intro i C hi hC
      cases i with
      | zero => exact .bvar hi hC
      | succ i => exact (compatible i C hi hC).weaken A

theorem «open» {sig : Signature} {Γ : List Ty} {body value : Tm} {A B : Ty}
    (bodyTyping : HasType sig (A :: Γ) body B) (valueTyping : HasType sig Γ value A) :
    HasType sig Γ (body.open value) B := by
  apply bodyTyping.subst (Tm.openSub value)
  intro i C hi hC
  cases i with
  | zero =>
      have eq : A = C := Option.some.inj hi
      cases eq
      exact valueTyping
  | succ i => exact .bvar hi hC

theorem freeSubst {sig : Signature} {Γ : List Ty} {t : Tm} {A : Ty}
    (typing : HasType sig Γ t A) (σ : Nat → Ty → Tm)
    (compatible : ∀ n B, B.WellFormed sig.tyOps → HasType sig Γ (σ n B) B) :
    HasType sig Γ (t.freeSubst σ) A := by
  induction typing generalizing σ with
  | bvar lookup wf => exact .bvar lookup wf
  | fvar n wf => exact compatible n _ wf
  | const hc => exact .const hc
  | app _ _ ihf ihx => exact .app (ihf σ compatible) (ihx σ compatible)
  | @lam Γ A B body wf hb ih =>
      exact .lam wf (ih _ (fun n C hC => (compatible n C hC).weaken A))

theorem equal {sig : Signature} {Γ : List Ty} {A : Ty} {left right : Tm}
    (wf : A.WellFormed sig.tyOps) (hl : HasType sig Γ left A) (hr : HasType sig Γ right A) :
    HasType sig Γ (Tm.equal A left right) .bool :=
  .app (.app (.const (.eq wf)) hl) hr

theorem scope {sig : Signature} {Γ : List Ty} {t : Tm} {A : Ty}
    (typing : HasType sig Γ t A) : t.Scope Γ.length := by
  induction typing with
  | bvar lookup _ =>
      exact List.getElem?_eq_some_iff.mp lookup |>.1
  | fvar | const => trivial
  | app _ _ ihf ihx => exact ⟨ihf, ihx⟩
  | lam _ _ ih => exact ih

end HasType

/-- A checked view uses the same syntax and independent typing judgment. -/
structure Checked (sig : Signature) (Γ : List Ty) (A : Ty) where
  term : Tm
  typing : HasType sig Γ term A

end Silmaril.Logic.HOLLight
