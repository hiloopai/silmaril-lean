module

public import Silmaril.Logic.HOLLight.Term
public import Silmaril.Prelude.DeBruijn

@[expose] public section

namespace Silmaril.Logic.HOLLight.Tm

/-- Capture-avoiding renaming of ambient bound variables. -/
def rename (ρ : Nat → Nat) : Tm → Tm
  | .bvar i => .bvar (ρ i)
  | .fvar n A => .fvar n A
  | .const c => .const c
  | .app f x => .app (f.rename ρ) (x.rename ρ)
  | .lam A b => .lam A (b.rename (DeBruijn.lift ρ))

/-- Add one ambient binder. -/
def weaken (t : Tm) : Tm := t.rename Nat.succ

/-- Extend a substitution underneath one binder. -/
def liftSub (σ : Nat → Tm) : Nat → Tm
  | 0 => .bvar 0
  | i + 1 => (σ i).weaken

/-- Capture-avoiding simultaneous substitution of ambient bound variables. -/
def subst (σ : Nat → Tm) : Tm → Tm
  | .bvar i => σ i
  | .fvar n A => .fvar n A
  | .const c => .const c
  | .app f x => .app (f.subst σ) (x.subst σ)
  | .lam A b => .lam A (b.subst (liftSub σ))

/-- Substitute the outermost binder and remove it from the ambient context. -/
def openSub (value : Tm) : Nat → Tm
  | 0 => value
  | i + 1 => .bvar i

def «open» (body value : Tm) : Tm := body.subst (openSub value)

/-- Substitution of named variables; inserted terms are weakened under binders. -/
def freeSubst (σ : Nat → Ty → Tm) : Tm → Tm
  | .bvar i => .bvar i
  | .fvar n A => σ n A
  | .const c => .const c
  | .app f x => .app (f.freeSubst σ) (x.freeSubst σ)
  | .lam A b => .lam A (b.freeSubst (fun n B => (σ n B).weaken))

@[simp] theorem rename_id (t : Tm) : t.rename id = t := by
  induction t with
  | bvar | fvar | const => rfl
  | app f x ihf ihx => simp only [rename, ihf, ihx]
  | lam A b ih => simp only [rename, DeBruijn.lift_id, ih]

theorem rename_comp (ρ τ : Nat → Nat) (t : Tm) :
    (t.rename ρ).rename τ = t.rename (τ ∘ ρ) := by
  induction t generalizing ρ τ with
  | bvar | fvar | const => rfl
  | app f x ihf ihx => simp only [rename, ihf, ihx]
  | lam A b ih => simp only [rename, ih, DeBruijn.lift_comp]

@[simp] theorem liftSub_bvar : liftSub bvar = bvar := by
  funext i
  cases i <;> rfl

@[simp] theorem subst_id (t : Tm) : t.subst bvar = t := by
  induction t with
  | bvar | fvar | const => rfl
  | app f x ihf ihx => simp only [subst, ihf, ihx]
  | lam A b ih => simp only [subst, liftSub_bvar, ih]

theorem liftSub_rename (ρ : Nat → Nat) (σ : Nat → Tm) :
    (fun i => (liftSub σ i).rename (DeBruijn.lift ρ)) =
      liftSub (fun i => (σ i).rename ρ) := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    simp only [liftSub, weaken, rename_comp]
    rfl

theorem rename_subst (ρ : Nat → Nat) (σ : Nat → Tm) (t : Tm) :
    (t.subst σ).rename ρ = t.subst (fun i => (σ i).rename ρ) := by
  induction t generalizing ρ σ with
  | bvar | fvar | const => rfl
  | app f x ihf ihx => simp only [subst, rename, ihf, ihx]
  | lam A b ih => simp only [subst, rename, ih, liftSub_rename]

theorem subst_rename (σ : Nat → Tm) (ρ : Nat → Nat) (t : Tm) :
    (t.rename ρ).subst σ = t.subst (σ ∘ ρ) := by
  induction t generalizing ρ σ with
  | bvar | fvar | const => rfl
  | app f x ihf ihx => simp only [subst, rename, ihf, ihx]
  | lam A b ih =>
    simp only [rename, subst, ih]
    congr 2
    funext i
    cases i <;> rfl

theorem liftSub_comp (σ τ : Nat → Tm) :
    (fun i => (liftSub σ i).subst (liftSub τ)) =
      liftSub (fun i => (σ i).subst τ) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => simp only [liftSub, weaken, subst_rename, rename_subst]; rfl

theorem subst_comp (σ τ : Nat → Tm) (t : Tm) :
    (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ) := by
  induction t generalizing σ τ with
  | bvar | fvar | const => rfl
  | app f x ihf ihx => simp only [subst, ihf, ihx]
  | lam A b ih => simp only [subst, ih, liftSub_comp]

theorem rename_eq_subst (ρ : Nat → Nat) (t : Tm) :
    t.rename ρ = t.subst (fun i => .bvar (ρ i)) := by
  induction t generalizing ρ with
  | bvar | fvar | const => rfl
  | app f x ihf ihx => simp only [rename, subst, ihf, ihx]
  | lam A b ih =>
    simp only [rename, subst, ih]
    congr 2
    funext i
    cases i <;> rfl

/-- Opening cancels a weakening: the inserted term has no occurrence to replace. -/
@[simp] theorem open_weaken (t value : Tm) : t.weaken.open value = t := by
  simp only [«open», weaken, subst_rename]
  exact subst_id t

@[simp] theorem freeVars_rename (ρ : Nat → Nat) (t : Tm) :
    (t.rename ρ).freeVars = t.freeVars := by
  induction t generalizing ρ with
  | bvar | fvar | const => rfl
  | app f x ihf ihx => simp only [rename, freeVars, ihf, ihx]
  | lam A b ih => exact ih _

@[simp] theorem freeVars_weaken (t : Tm) : t.weaken.freeVars = t.freeVars :=
  freeVars_rename _ _

theorem Scope.rename {d e : Nat} {t : Tm} (h : Scope d t)
    (ρ : Nat → Nat) (hρ : ∀ i, i < d → ρ i < e) : Scope e (t.rename ρ) := by
  induction t generalizing d e ρ with
  | bvar i => exact hρ i h
  | fvar | const => trivial
  | app f x ihf ihx => exact ⟨ihf h.1 ρ hρ, ihx h.2 ρ hρ⟩
  | lam A b ih =>
    apply ih h (DeBruijn.lift ρ)
    intro i hi
    cases i with
    | zero => exact Nat.zero_lt_succ e
    | succ i => exact Nat.succ_lt_succ (hρ i (Nat.lt_of_succ_lt_succ hi))

theorem Scope.weaken {d : Nat} {t : Tm} (h : Scope d t) : Scope (d + 1) t.weaken :=
  h.rename Nat.succ (fun _ hi => Nat.succ_lt_succ hi)

theorem Scope.subst {d e : Nat} {t : Tm} (h : Scope d t)
    (σ : Nat → Tm) (hσ : ∀ i, i < d → Scope e (σ i)) : Scope e (t.subst σ) := by
  induction t generalizing d e σ with
  | bvar i => exact hσ i h
  | fvar | const => trivial
  | app f x ihf ihx => exact ⟨ihf h.1 σ hσ, ihx h.2 σ hσ⟩
  | lam A b ih =>
    apply ih h (liftSub σ)
    intro i hi
    cases i with
    | zero => exact Nat.zero_lt_succ e
    | succ i => exact (hσ i (Nat.lt_of_succ_lt_succ hi)).weaken

theorem Scope.open {d : Nat} {body value : Tm} (hb : Scope (d + 1) body)
    (hv : Scope d value) : Scope d (body.open value) := by
  apply hb.subst (openSub value)
  intro i hi
  cases i with
  | zero => exact hv
  | succ i => exact Nat.lt_of_succ_lt_succ hi

theorem tySubst_rename (σ : Nat → Ty) (ρ : Nat → Nat) (t : Tm) :
    (t.rename ρ).tySubst σ = (t.tySubst σ).rename ρ := by
  induction t generalizing ρ with
  | bvar | fvar | const => rfl
  | app f x ihf ihx => simp only [rename, tySubst, ihf, ihx]
  | lam A b ih => simp only [rename, tySubst, ih]

theorem tySubst_liftSub (σ : Nat → Ty) (τ : Nat → Tm) :
    (fun i => (liftSub τ i).tySubst σ) = liftSub (fun i => (τ i).tySubst σ) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => exact tySubst_rename _ _ _

theorem tySubst_subst (σ : Nat → Ty) (τ : Nat → Tm) (t : Tm) :
    (t.subst τ).tySubst σ = (t.tySubst σ).subst (fun i => (τ i).tySubst σ) := by
  induction t generalizing τ with
  | bvar | fvar | const => rfl
  | app f x ihf ihx => simp only [subst, tySubst, ihf, ihx]
  | lam A b ih => simp only [subst, tySubst, ih, tySubst_liftSub]

theorem tySubst_open (σ : Nat → Ty) (body value : Tm) :
    (body.open value).tySubst σ = (body.tySubst σ).open (value.tySubst σ) := by
  simp only [«open», tySubst_subst]
  congr 1
  funext i
  cases i <;> rfl

/-- Renamings agreeing on the ambient context act identically on scoped terms. -/
theorem rename_congr {d : Nat} {t : Tm} (h : Scope d t)
    (ρ τ : Nat → Nat) (hρτ : ∀ i, i < d → ρ i = τ i) :
    t.rename ρ = t.rename τ := by
  induction t generalizing d ρ τ with
  | bvar i => exact congrArg bvar (hρτ i h)
  | fvar | const => rfl
  | app f x ihf ihx => simp only [rename, ihf h.1 _ _ hρτ, ihx h.2 _ _ hρτ]
  | lam A b ih =>
    apply congrArg (lam A)
    apply ih h
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact congrArg Nat.succ (hρτ i (Nat.lt_of_succ_lt_succ hi))

theorem Closed.rename_eq {t : Tm} (h : Closed t) (ρ : Nat → Nat) : t.rename ρ = t := by
  rw [rename_congr h ρ id (fun i hi => False.elim (Nat.not_lt_zero i hi)), rename_id]

theorem Closed.weaken_eq {t : Tm} (h : Closed t) : t.weaken = t := h.rename_eq _

theorem subst_congr {d : Nat} {t : Tm} (h : Scope d t)
    (σ τ : Nat → Tm) (hστ : ∀ i, i < d → σ i = τ i) :
    t.subst σ = t.subst τ := by
  induction t generalizing d σ τ with
  | bvar i => exact hστ i h
  | fvar | const => rfl
  | app f x ihf ihx => simp only [subst, ihf h.1 _ _ hστ, ihx h.2 _ _ hστ]
  | lam A b ih =>
    apply congrArg (lam A)
    apply ih h
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact congrArg weaken (hστ i (Nat.lt_of_succ_lt_succ hi))

theorem Closed.subst_eq {t : Tm} (h : Closed t) (σ : Nat → Tm) : t.subst σ = t := by
  rw [subst_congr h σ bvar (fun i hi => False.elim (Nat.not_lt_zero i hi)), subst_id]

theorem rename_freeSubst (ρ : Nat → Nat) (σ : Nat → Ty → Tm) (t : Tm) :
    (t.freeSubst σ).rename ρ =
      (t.rename ρ).freeSubst (fun n A => (σ n A).rename ρ) := by
  induction t generalizing ρ σ with
  | bvar | fvar | const => rfl
  | app f x ihf ihx => simp only [rename, freeSubst, ihf, ihx]
  | lam A b ih =>
    simp only [rename, freeSubst, ih]
    congr 2
    funext n B
    simp only [weaken, rename_comp]
    rfl

@[simp] theorem freeSubst_id (t : Tm) : t.freeSubst fvar = t := by
  induction t with
  | bvar | fvar | const => rfl
  | app f x ihf ihx => simp only [freeSubst, ihf, ihx]
  | lam A b ih => exact congrArg (lam A) ih

theorem freeSubst_comp (σ τ : Nat → Ty → Tm) (t : Tm) :
    (t.freeSubst σ).freeSubst τ = t.freeSubst (fun n A => (σ n A).freeSubst τ) := by
  induction t generalizing σ τ with
  | bvar | fvar | const => rfl
  | app f x ihf ihx => simp only [freeSubst, ihf, ihx]
  | lam A b ih =>
    simp only [freeSubst, ih]
    congr 2
    funext n B
    exact (rename_freeSubst Nat.succ τ (σ n B)).symm

theorem Scope.freeSubst {d : Nat} {t : Tm} (h : Scope d t)
    (σ : Nat → Ty → Tm) (hσ : ∀ n A, Scope d (σ n A)) : Scope d (t.freeSubst σ) := by
  induction t generalizing d σ with
  | bvar i => exact h
  | fvar n A => exact hσ n A
  | const => trivial
  | app f x ihf ihx => exact ⟨ihf h.1 _ hσ, ihx h.2 _ hσ⟩
  | lam A b ih => exact ih h _ (fun n B => (hσ n B).weaken)

/-- Substitutions agreeing on finite free support act identically. -/
theorem freeSubst_congr (t : Tm) (σ τ : Nat → Ty → Tm)
    (h : ∀ n A, (n, A) ∈ t.freeVars → σ n A = τ n A) :
    t.freeSubst σ = t.freeSubst τ := by
  induction t generalizing σ τ with
  | bvar | const => rfl
  | fvar n A => exact h n A (by simp [freeVars])
  | app f x ihf ihx =>
    simp only [freeSubst]
    rw [ihf _ _ (fun n A hn => h n A (List.mem_append_left _ hn)),
      ihx _ _ (fun n A hn => h n A (List.mem_append_right _ hn))]
  | lam A b ih =>
    apply congrArg (lam A)
    exact ih _ _ (fun n B hn => congrArg weaken (h n B hn))

/-- Replace one typed free name. -/
def replaceFree (t : Tm) (v : Nat × Ty) (value : Tm) : Tm :=
  t.freeSubst (fun n A => if (n, A) = v then value else .fvar n A)

theorem replaceFree_of_fresh {v : Nat × Ty} {t : Tm} (h : Fresh v t) (value : Tm) :
    t.replaceFree v value = t := by
  rw [replaceFree, freeSubst_congr t _ fvar, freeSubst_id]
  intro n A hn
  have hne : (n, A) ≠ v := by
    intro heq
    exact h (heq ▸ hn)
  simp only [hne, ↓reduceIte]

/-- Closed replacements commute with bound renaming without changing the substitution. -/
theorem rename_freeSubst_closed (ρ : Nat → Nat) (σ : Nat → Ty → Tm)
    (hσ : ∀ n A, Closed (σ n A)) (t : Tm) :
    (t.freeSubst σ).rename ρ = (t.rename ρ).freeSubst σ := by
  rw [rename_freeSubst]
  congr 1
  funext n A
  exact (hσ n A).rename_eq ρ

theorem freeSubst_lam_closed (σ : Nat → Ty → Tm) (hσ : ∀ n A, Closed (σ n A))
    (A : Ty) (body : Tm) :
    (lam A body).freeSubst σ = lam A (body.freeSubst σ) := by
  simp only [freeSubst]
  congr 2
  funext n B
  exact (hσ n B).weaken_eq

/-- Closed free replacements commute with substitution of ambient bound variables. -/
theorem freeSubst_subst (σ : Nat → Tm) (τ : Nat → Ty → Tm)
    (hτ : ∀ n A, Closed (τ n A)) (t : Tm) :
    (t.subst σ).freeSubst τ = (t.freeSubst τ).subst (fun i => (σ i).freeSubst τ) := by
  induction t generalizing σ with
  | bvar => rfl
  | fvar n A => exact ((hτ n A).subst_eq _).symm
  | const => rfl
  | app f x ihf ihx => simp only [subst, freeSubst, ihf, ihx]
  | lam A b ih =>
    simp only [subst, freeSubst_lam_closed τ hτ, ih]
    congr 2
    funext i
    cases i with
    | zero => rfl
    | succ i => exact (rename_freeSubst_closed Nat.succ τ hτ (σ i)).symm

/-- When the original free names are fixed, only bound replacements are affected. -/
theorem freeSubst_subst_of_fixed (σ : Nat → Tm) (τ : Nat → Ty → Tm) (t : Tm)
    (hτ : ∀ n A, (n, A) ∈ t.freeVars → τ n A = .fvar n A) :
    (t.subst σ).freeSubst τ = t.subst (fun i => (σ i).freeSubst τ) := by
  induction t generalizing σ τ with
  | bvar => rfl
  | fvar n A => exact hτ n A (by simp [freeVars])
  | const => rfl
  | app f x ihf ihx =>
    simp only [subst, freeSubst]
    rw [ihf _ _ (fun n A hn => hτ n A (List.mem_append_left _ hn)),
      ihx _ _ (fun n A hn => hτ n A (List.mem_append_right _ hn))]
  | lam A b ih =>
    simp only [subst, freeSubst]
    rw [ih _ _ (fun n B hn => congrArg weaken (hτ n B hn))]
    congr 2
    funext i
    cases i with
    | zero => rfl
    | succ i => exact (rename_freeSubst Nat.succ τ (σ i)).symm

/-- Closing a fresh variable after opening recovers a one-binder body. -/
theorem replaceFree_open_close {body : Tm} {n : Nat} {A : Ty}
    (hfresh : Fresh (n, A) body) (hbody : Scope 1 body) :
    (body.open (.fvar n A)).replaceFree (n, A) (.bvar 0) = body := by
  unfold replaceFree «open»
  rw [freeSubst_subst_of_fixed]
  · rw [subst_congr hbody _ bvar, subst_id]
    intro i hi
    have hi0 : i = 0 := Nat.le_zero.mp (Nat.le_of_lt_succ hi)
    subst i
    simp [openSub, freeSubst]
  · intro m B hm
    have hne : (m, B) ≠ (n, A) := fun heq => hfresh (heq ▸ hm)
    simp only [hne, ↓reduceIte]

theorem freeSubst_open (τ : Nat → Ty → Tm) (hτ : ∀ n A, Closed (τ n A))
    (body value : Tm) :
    (body.open value).freeSubst τ = (body.freeSubst τ).open (value.freeSubst τ) := by
  simp only [«open», freeSubst_subst _ τ hτ]
  congr 1
  funext i
  cases i <;> rfl

@[simp] theorem replaceFree_self (n : Nat) (A : Ty) (value : Tm) :
    (fvar n A).replaceFree (n, A) value = value := by
  simp [replaceFree, freeSubst]

theorem replaceFree_open {value : Tm} (hv : Closed value)
    (v : Nat × Ty) (body argument : Tm) :
    (body.open argument).replaceFree v value =
      (body.replaceFree v value).open (argument.replaceFree v value) := by
  apply freeSubst_open
  intro n A
  split
  · exact hv
  · trivial

/-- General beta substitution follows by instantiating a fresh-variable opening. -/
theorem replaceFree_open_fvar {body value : Tm} {n : Nat} {A : Ty}
    (hfresh : Fresh (n, A) body) (hv : Closed value) :
    (body.open (.fvar n A)).replaceFree (n, A) value = body.open value := by
  rw [replaceFree_open hv, replaceFree_of_fresh hfresh, replaceFree_self]

@[simp] theorem freeVars_freeSubst (σ : Nat → Ty → Tm) (t : Tm) :
    (t.freeSubst σ).freeVars =
      t.freeVars.flatMap (fun v => (σ v.1 v.2).freeVars) := by
  induction t generalizing σ with
  | bvar | fvar | const => simp [freeSubst, freeVars]
  | app f x ihf ihx => simp only [freeSubst, freeVars, ihf, ihx, List.flatMap_append]
  | lam A b ih => simp only [freeSubst, freeVars, ih, freeVars_weaken]

/-- A strict upper bound on every name in a finite free support. -/
def freshBound (vs : List (Nat × Ty)) : Nat :=
  vs.foldr (fun v bound => max (v.1 + 1) bound) 0

private theorem lt_freshBound {vs : List (Nat × Ty)} {v : Nat × Ty} (h : v ∈ vs) :
    v.1 < freshBound vs := by
  induction vs with
  | nil => exact False.elim (List.not_mem_nil h)
  | cons w vs ih =>
    rcases List.mem_cons.mp h with h | h
    · subst v
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (ih h) (Nat.le_max_right _ _)

/-- Choose a name absent at every type from a finite collection of terms. -/
def freshName (terms : List Tm) : Nat := freshBound (terms.flatMap freeVars)

theorem freshName_fresh (terms : List Tm) {t : Tm} (ht : t ∈ terms) (A : Ty) :
    Fresh (freshName terms, A) t := by
  intro hv
  have h := lt_freshBound (List.mem_flatMap.mpr ⟨t, ht, hv⟩)
  exact Nat.lt_irrefl _ h

theorem exists_freshName (terms : List Tm) :
    ∃ n, ∀ t ∈ terms, ∀ A, Fresh (n, A) t :=
  ⟨freshName terms, fun _ ht A => freshName_fresh terms ht A⟩

/-- Type instantiation commutes with a compatible substitution of typed free names.
The compatibility premise is essential when type instantiation merges names. -/
theorem tySubst_freeSubst (θ : Nat → Ty) (σ τ : Nat → Ty → Tm)
    (h : ∀ n A, (σ n A).tySubst θ = τ n (A.subst θ)) (t : Tm) :
    (t.freeSubst σ).tySubst θ = (t.tySubst θ).freeSubst τ := by
  induction t generalizing σ τ with
  | bvar | const => rfl
  | fvar n A => exact h n A
  | app f x ihf ihx => simp only [freeSubst, tySubst, ihf _ _ h, ihx _ _ h]
  | lam A b ih =>
    apply congrArg (lam (A.subst θ))
    apply ih
    intro n B
    exact (tySubst_rename θ Nat.succ (σ n B)).trans (congrArg weaken (h n B))

end Silmaril.Logic.HOLLight.Tm
