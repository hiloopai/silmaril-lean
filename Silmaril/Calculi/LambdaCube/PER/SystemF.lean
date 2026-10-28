module

public import Silmaril.Calculi.LambdaCube.PER.Basic

@[expose] public section

set_option autoImplicit true

/-! # System F (λ2) and its PER model

Church-style System F with de Bruijn type and term variables kept in separate
scopes, as in Reynolds 1984 (type variables are global; a term context lists
only term variables). Type abstraction shifts the term context
(`Typed.tlam`), which is Reynolds' `π − τ` side condition for a fresh `τ`.

The PER model over any total combinatory algebra `M`:

* `Ty.interp`: type variables by an environment `η : ℕ → PER M.D`, `→` by the
  extensional arrow PER, `∀` by intersection over *all* PERs on `M.D`;
* terms by their type erasure (`Tm.erase`), compiled by bracket abstraction;
* `Typed.sound`: a typed term is related to itself under related environments
  (the fundamental lemma);
* `TmEq.sound`: βη-equal terms (including type β and η) are related.

`bool_distinct` shows the model is not degenerate as soon as `K ≠ S`.
The relation to the cube's PTS syntax is in `PER/Cube.lean`.
-/

namespace Silmaril.Calculi.LambdaCube.PERModel.SystemF

/-- Types of System F. -/
inductive Ty where
  | var (n : ℕ)
  | arr (A B : Ty)
  | all (A : Ty)
  deriving DecidableEq

namespace Ty

/-- Renaming of type variables. -/
def rename (ρ : ℕ → ℕ) : Ty → Ty
  | var n => var (ρ n)
  | arr A B => arr (rename ρ A) (rename ρ B)
  | all A => all (rename (scons 0 (Nat.succ ∘ ρ)) A)

/-- Lift a type substitution under a type binder. -/
def liftSub (σ : ℕ → Ty) : ℕ → Ty := scons (var 0) (fun n => rename Nat.succ (σ n))

/-- Simultaneous substitution of type variables. -/
def subst (σ : ℕ → Ty) : Ty → Ty
  | var n => σ n
  | arr A B => arr (subst σ A) (subst σ B)
  | all A => all (subst (liftSub σ) A)

/-- Instantiate type variable `0` and lower the others. -/
def substOne (A B : Ty) : Ty := subst (scons B var) A

/-- Type variable `n` occurs free. -/
def FreeIn : ℕ → Ty → Prop
  | n, var m => n = m
  | n, arr A B => FreeIn n A ∨ FreeIn n B
  | n, all A => FreeIn (n + 1) A

end Ty

/-- Church-style terms of System F. -/
inductive Tm where
  | var (n : ℕ)
  | app (t u : Tm)
  | lam (A : Ty) (t : Tm)
  | tapp (t : Tm) (A : Ty)
  | tlam (t : Tm)
  deriving DecidableEq

namespace Tm

/-- Rename the type variables in annotations. -/
def tyRename (ρ : ℕ → ℕ) : Tm → Tm
  | var n => var n
  | app t u => app (tyRename ρ t) (tyRename ρ u)
  | lam A t => lam (A.rename ρ) (tyRename ρ t)
  | tapp t A => tapp (tyRename ρ t) (A.rename ρ)
  | tlam t => tlam (tyRename (scons 0 (Nat.succ ∘ ρ)) t)

/-- Substitute types for the type variables in annotations. -/
def tySubst (σ : ℕ → Ty) : Tm → Tm
  | var n => var n
  | app t u => app (tySubst σ t) (tySubst σ u)
  | lam A t => lam (A.subst σ) (tySubst σ t)
  | tapp t A => tapp (tySubst σ t) (A.subst σ)
  | tlam t => tlam (tySubst (Ty.liftSub σ) t)

/-- Instantiate type variable `0` in annotations. -/
def tySubstOne (t : Tm) (B : Ty) : Tm := tySubst (scons B Ty.var) t

/-- Rename term variables; type binders do not bind term variables. -/
def rename (ρ : ℕ → ℕ) : Tm → Tm
  | var n => var (ρ n)
  | app t u => app (rename ρ t) (rename ρ u)
  | lam A t => lam A (rename (scons 0 (Nat.succ ∘ ρ)) t)
  | tapp t A => tapp (rename ρ t) A
  | tlam t => tlam (rename ρ t)

/-- Lift a term substitution under a term binder. -/
def liftSub (σ : ℕ → Tm) : ℕ → Tm := scons (var 0) (fun n => rename Nat.succ (σ n))

/-- Simultaneous substitution of term variables. Under a type binder the
substituted terms have their type variables shifted. -/
def subst (σ : ℕ → Tm) : Tm → Tm
  | var n => σ n
  | app t u => app (subst σ t) (subst σ u)
  | lam A t => lam A (subst (liftSub σ) t)
  | tapp t A => tapp (subst σ t) A
  | tlam t => tlam (subst (fun n => tyRename Nat.succ (σ n)) t)

/-- Substitute for term variable `0` and lower the others. -/
def substOne (t u : Tm) : Tm := subst (scons u var) t

/-- Type variable `n` occurs free in an annotation. -/
def TyFreeIn : ℕ → Tm → Prop
  | _, var _ => False
  | n, app t u => TyFreeIn n t ∨ TyFreeIn n u
  | n, lam A t => A.FreeIn n ∨ TyFreeIn n t
  | n, tapp t A => TyFreeIn n t ∨ A.FreeIn n
  | n, tlam t => TyFreeIn (n + 1) t

/-- Curry-style type erasure. -/
def erase : Tm → ULam
  | var n => .var n
  | app t u => .app (erase t) (erase u)
  | lam _ t => .lam (erase t)
  | tapp t _ => erase t
  | tlam t => erase t

end Tm

/-- Term contexts; the newest variable is first. -/
abbrev Ctx := List Ty

/-- The typing judgment of System F. Free type variables are global. -/
inductive Typed : Ctx → Tm → Ty → Prop where
  | var : Γ[n]? = some A → Typed Γ (.var n) A
  | app : Typed Γ t (.arr A B) → Typed Γ u A → Typed Γ (.app t u) B
  | lam : Typed (A :: Γ) t B → Typed Γ (.lam A t) (.arr A B)
  | tlam : Typed (Γ.map (Ty.rename Nat.succ)) t A → Typed Γ (.tlam t) (.all A)
  | tapp : Typed Γ t (.all A) → Typed Γ (.tapp t B) (A.substOne B)

/-- Typed βη-equality, with type β and type η. -/
inductive TmEq : Ctx → Tm → Tm → Ty → Prop where
  | refl : Typed Γ t A → TmEq Γ t t A
  | symm : TmEq Γ t u A → TmEq Γ u t A
  | trans : TmEq Γ t u A → TmEq Γ u v A → TmEq Γ t v A
  | beta : Typed (A :: Γ) t B → Typed Γ u A →
      TmEq Γ (.app (.lam A t) u) (t.substOne u) B
  | eta : Typed Γ t (.arr A B) →
      TmEq Γ (.lam A (.app (t.rename Nat.succ) (.var 0))) t (.arr A B)
  | tbeta : Typed (Γ.map (Ty.rename Nat.succ)) t A →
      TmEq Γ (.tapp (.tlam t) B) (t.tySubstOne B) (A.substOne B)
  | teta : Typed Γ t (.all A) →
      TmEq Γ (.tlam (.tapp (t.tyRename Nat.succ) (.var 0))) t (.all A)
  | app : TmEq Γ t t' (.arr A B) → TmEq Γ u u' A → TmEq Γ (.app t u) (.app t' u') B
  | lam : TmEq (A :: Γ) t t' B → TmEq Γ (.lam A t) (.lam A t') (.arr A B)
  | tapp : TmEq Γ t t' (.all A) → TmEq Γ (.tapp t B) (.tapp t' B) (A.substOne B)
  | tlam : TmEq (Γ.map (Ty.rename Nat.succ)) t t' A → TmEq Γ (.tlam t) (.tlam t') (.all A)

/-! ## Syntactic metatheory (renaming and substitution) -/

namespace Ty

theorem liftSub_var_comp (r : ℕ → ℕ) :
    liftSub (var ∘ r) = var ∘ scons 0 (Nat.succ ∘ r) := by
  funext n; cases n <;> rfl

theorem rename_eq_subst (r : ℕ → ℕ) (A : Ty) : A.rename r = A.subst (var ∘ r) := by
  induction A generalizing r with
  | var n => rfl
  | arr A B ihA ihB => simp only [rename, subst, ihA, ihB]
  | all A ih => simp only [rename, subst, ih, liftSub_var_comp]

theorem rename_rename (r r' : ℕ → ℕ) (A : Ty) :
    (A.rename r).rename r' = A.rename (r' ∘ r) := by
  induction A generalizing r r' with
  | var n => rfl
  | arr A B ihA ihB => simp only [rename, ihA, ihB]
  | all A ih =>
    simp only [rename, ih]
    congr 2; funext n; cases n <;> rfl

theorem subst_rename (r : ℕ → ℕ) (σ : ℕ → Ty) (A : Ty) :
    (A.rename r).subst σ = A.subst (σ ∘ r) := by
  induction A generalizing r σ with
  | var n => rfl
  | arr A B ihA ihB => simp only [rename, subst, ihA, ihB]
  | all A ih =>
    simp only [rename, subst, ih]
    congr 2; funext n; cases n <;> rfl

theorem rename_subst (r : ℕ → ℕ) (σ : ℕ → Ty) (A : Ty) :
    (A.subst σ).rename r = A.subst (rename r ∘ σ) := by
  induction A generalizing r σ with
  | var n => rfl
  | arr A B ihA ihB => simp only [rename, subst, ihA, ihB]
  | all A ih =>
    simp only [rename, subst, ih]
    congr 2; funext n
    cases n with
    | zero => rfl
    | succ n =>
      show rename _ (rename _ _) = rename _ (rename _ _)
      rw [rename_rename, rename_rename]; rfl

theorem subst_var (A : Ty) : A.subst var = A := by
  induction A with
  | var n => rfl
  | arr A B ihA ihB => simp only [subst, ihA, ihB]
  | all A ih =>
    have : liftSub var = var := by funext n; cases n <;> rfl
    simp only [subst, this, ih]

theorem subst_subst (σ τ : ℕ → Ty) (A : Ty) :
    (A.subst σ).subst τ = A.subst (fun n => (σ n).subst τ) := by
  induction A generalizing σ τ with
  | var n => rfl
  | arr A B ihA ihB => simp only [subst, ihA, ihB]
  | all A ih =>
    simp only [subst, ih]
    congr 2; funext n
    cases n with
    | zero => rfl
    | succ n =>
      show (rename _ _).subst _ = rename _ (subst _ _)
      rw [subst_rename, rename_subst]; rfl

theorem subst_rename_succ_scons (B : Ty) (σ : ℕ → Ty) (C : Ty) :
    (C.rename Nat.succ).subst (scons B σ) = C.subst σ := by
  rw [subst_rename]; rfl

theorem substOne_subst (A B : Ty) (σ : ℕ → Ty) :
    (A.substOne B).subst σ = (A.subst (liftSub σ)).substOne (B.subst σ) := by
  unfold substOne
  rw [subst_subst, subst_subst]
  congr 1; funext n
  cases n with
  | zero => rfl
  | succ n =>
    show subst σ (var n) = (rename Nat.succ (σ n)).subst _
    rw [subst_rename_succ_scons, subst_var]; rfl

end Ty

namespace Tm

theorem tyRename_eq_tySubst (r : ℕ → ℕ) (t : Tm) : t.tyRename r = t.tySubst (Ty.var ∘ r) := by
  induction t generalizing r with
  | var n => rfl
  | app t u iht ihu => simp only [tyRename, tySubst, iht, ihu]
  | lam A t ih => simp only [tyRename, tySubst, ih, Ty.rename_eq_subst]
  | tapp t A ih => simp only [tyRename, tySubst, ih, Ty.rename_eq_subst]
  | tlam t ih => simp only [tyRename, tySubst, ih, Ty.liftSub_var_comp]

end Tm

theorem getElem?_map_eq_some {Γ : Ctx} {f : Ty → Ty} {n : ℕ} {B : Ty}
    (h : (Γ.map f)[n]? = some B) : ∃ C, Γ[n]? = some C ∧ B = f C := by
  rw [List.getElem?_map] at h
  cases hC : Γ[n]? with
  | none => simp [hC] at h
  | some C => simp only [hC, Option.map_some, Option.some.injEq] at h; exact ⟨C, rfl, h.symm⟩

theorem map_subst_liftSub_rename (σ : ℕ → Ty) (Γ : Ctx) :
    (Γ.map (Ty.rename Nat.succ)).map (Ty.subst (Ty.liftSub σ)) =
      (Γ.map (Ty.subst σ)).map (Ty.rename Nat.succ) := by
  induction Γ with
  | nil => rfl
  | cons C Γ ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, ih]
    exact congrArg (· :: _) (by rw [Ty.subst_rename, Ty.rename_subst]; rfl)

theorem map_subst_scons_rename (B : Ty) (Γ : Ctx) :
    (Γ.map (Ty.rename Nat.succ)).map (Ty.subst (scons B Ty.var)) = Γ := by
  induction Γ with
  | nil => rfl
  | cons C Γ ih =>
    simp only [List.map_cons, ih, Ty.subst_rename_succ_scons, Ty.subst_var]

theorem Typed.tySubst (h : Typed Γ t A) (σ : ℕ → Ty) :
    Typed (Γ.map (Ty.subst σ)) (t.tySubst σ) (A.subst σ) := by
  induction h generalizing σ with
  | var h => exact .var (by simp [List.getElem?_map, h])
  | app _ _ iht ihu => exact .app (iht σ) (ihu σ)
  | lam _ ih => exact .lam (ih σ)
  | tlam _ ih =>
    refine .tlam ?_
    rw [← map_subst_liftSub_rename]; exact ih _
  | tapp _ ih =>
    rw [Ty.substOne_subst]; exact .tapp (ih σ)

theorem Typed.tyRename (h : Typed Γ t A) (r : ℕ → ℕ) :
    Typed (Γ.map (Ty.rename r)) (t.tyRename r) (A.rename r) := by
  have e : Ty.rename r = Ty.subst (Ty.var ∘ r) := funext (Ty.rename_eq_subst r)
  rw [e, Tm.tyRename_eq_tySubst]; exact h.tySubst _

theorem Typed.rename (h : Typed Γ t A) {Δ : Ctx} {r : ℕ → ℕ}
    (hr : ∀ n B, Γ[n]? = some B → Δ[r n]? = some B) : Typed Δ (t.rename r) A := by
  induction h generalizing Δ r with
  | var h => exact .var (hr _ _ h)
  | app _ _ iht ihu => exact .app (iht hr) (ihu hr)
  | lam _ ih =>
    refine .lam (ih ?_)
    intro n B h
    cases n with
    | zero => simpa using h
    | succ n => simpa using hr n B (by simpa using h)
  | tlam _ ih =>
    refine .tlam (ih ?_)
    intro n B h
    obtain ⟨C, hC, rfl⟩ := getElem?_map_eq_some h
    simp [List.getElem?_map, hr n C hC]
  | tapp _ ih => exact .tapp (ih hr)

theorem Typed.subst (h : Typed Γ t A) {Δ : Ctx} {σ : ℕ → Tm}
    (hσ : ∀ n B, Γ[n]? = some B → Typed Δ (σ n) B) : Typed Δ (t.subst σ) A := by
  induction h generalizing Δ σ with
  | var h => exact hσ _ _ h
  | app _ _ iht ihu => exact .app (iht hσ) (ihu hσ)
  | lam _ ih =>
    refine .lam (ih ?_)
    intro n B h
    cases n with
    | zero => exact .var (by simpa using h)
    | succ n =>
      exact (hσ n B (by simpa using h)).rename (fun m C hm => by simpa using hm)
  | tlam _ ih =>
    refine .tlam (ih ?_)
    intro n B h
    obtain ⟨C, hC, rfl⟩ := getElem?_map_eq_some h
    exact (hσ n C hC).tyRename _
  | tapp _ ih => exact .tapp (ih hσ)

theorem Typed.tySubstOne_shift {Γ : Ctx} {t : Tm} {A : Ty}
    (ht : Typed (Γ.map (Ty.rename Nat.succ)) t A) (B : Ty) :
    Typed Γ (t.tySubstOne B) (A.substOne B) := by
  have h2 := ht.tySubst (scons B Ty.var)
  rw [map_subst_scons_rename] at h2
  exact h2

theorem TmEq.typed (h : TmEq Γ t u A) : Typed Γ t A ∧ Typed Γ u A := by
  induction h with
  | refl h => exact ⟨h, h⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih1 ih2 => exact ⟨ih1.1, ih2.2⟩
  | beta ht hu =>
    refine ⟨.app (.lam ht) hu, ht.subst ?_⟩
    intro n B h
    cases n with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; exact hu
    | succ n => exact .var (by simpa using h)
  | eta ht =>
    refine ⟨.lam (.app (ht.rename (fun m C hm => by simpa using hm)) (.var rfl)), ht⟩
  | tbeta ht => exact ⟨.tapp (.tlam ht), ht.tySubstOne_shift _⟩
  | @teta Γ t A ht =>
    refine ⟨.tlam ?_, ht⟩
    have h2 := Typed.tapp (B := Ty.var 0) (ht.tyRename Nat.succ)
    have e2 : (A.rename (scons 0 (Nat.succ ∘ Nat.succ))).substOne (Ty.var 0) = A := by
      unfold Ty.substOne
      rw [Ty.subst_rename]
      have : (scons (Ty.var 0) Ty.var ∘ scons 0 (Nat.succ ∘ Nat.succ)) = Ty.var := by
        funext n; cases n <;> rfl
      rw [this, Ty.subst_var]
    rw [e2] at h2; exact h2
  | app _ _ ih1 ih2 => exact ⟨.app ih1.1 ih2.1, .app ih1.2 ih2.2⟩
  | lam _ ih => exact ⟨.lam ih.1, .lam ih.2⟩
  | tapp _ ih => exact ⟨.tapp ih.1, .tapp ih.2⟩
  | tlam _ ih => exact ⟨.tlam ih.1, .tlam ih.2⟩

theorem TmEq.typed_left (h : TmEq Γ t u A) : Typed Γ t A := h.typed.1

theorem TmEq.typed_right (h : TmEq Γ t u A) : Typed Γ u A := h.typed.2

/-! ## The PER interpretation -/

variable (M : CombAlg.{u})

/-- Types as PERs: `∀` is the intersection over all PERs on the realizers. -/
def Ty.interp : Ty → (ℕ → PER M.D) → PER M.D
  | .var n, η => η n
  | .arr A B, η => PER.arrow M (Ty.interp A η) (Ty.interp B η)
  | .all A, η => PER.iInf fun X : PER M.D => Ty.interp A (scons X η)

/-- Related realizer environments for a term context. -/
def EnvRel (Γ : Ctx) (η : ℕ → PER M.D) (ρ ρ' : ℕ → M.D) : Prop :=
  ∀ n (A : Ty), Γ[n]? = some A → (A.interp M η).rel (ρ n) (ρ' n)

/-- Semantic typing: the erasure is self-related at the type. -/
def Valid (Γ : Ctx) (t : Tm) (A : Ty) : Prop :=
  ∀ η ρ ρ', EnvRel M Γ η ρ ρ' → (A.interp M η).rel (t.erase.eval M ρ) (t.erase.eval M ρ')

/-- Semantic equality: the two erasures are related at the type. -/
def ValidEq (Γ : Ctx) (t u : Tm) (A : Ty) : Prop :=
  ∀ η ρ ρ', EnvRel M Γ η ρ ρ' → (A.interp M η).rel (t.erase.eval M ρ) (u.erase.eval M ρ')

variable {M}

theorem Ty.interp_rename (r : ℕ → ℕ) (A : Ty) (η : ℕ → PER M.D) :
    (A.rename r).interp M η = A.interp M (η ∘ r) := by
  induction A generalizing r η with
  | var n => rfl
  | arr A B ihA ihB => simp only [Ty.rename, Ty.interp, ihA, ihB]
  | all A ih =>
    simp only [Ty.rename, Ty.interp, ih]
    congr 1; funext X; congr 1; funext n; cases n <;> rfl

theorem Ty.interp_subst (σ : ℕ → Ty) (A : Ty) (η : ℕ → PER M.D) :
    (A.subst σ).interp M η = A.interp M (fun n => (σ n).interp M η) := by
  induction A generalizing σ η with
  | var n => rfl
  | arr A B ihA ihB => simp only [Ty.subst, Ty.interp, ihA, ihB]
  | all A ih =>
    simp only [Ty.subst, Ty.interp, ih]
    congr 1; funext X; congr 1; funext n
    cases n with
    | zero => rfl
    | succ n =>
      show (Ty.rename Nat.succ (σ n)).interp M _ = _
      rw [Ty.interp_rename]; rfl

theorem Ty.interp_substOne (A B : Ty) (η : ℕ → PER M.D) :
    (A.substOne B).interp M η = A.interp M (scons (B.interp M η) η) := by
  unfold Ty.substOne
  rw [Ty.interp_subst]
  congr 1; funext n; cases n <;> rfl

/-- Only free type variables matter. -/
theorem Ty.interp_congr (A : Ty) {η η' : ℕ → PER M.D}
    (h : ∀ n, A.FreeIn n → η n = η' n) : A.interp M η = A.interp M η' := by
  induction A generalizing η η' with
  | var n => exact h n rfl
  | arr A B ihA ihB =>
    simp only [Ty.interp]
    rw [ihA (fun n hn => h n (Or.inl hn)), ihB (fun n hn => h n (Or.inr hn))]
  | all A ih =>
    simp only [Ty.interp]
    congr 1; funext X
    refine ih (fun n hn => ?_)
    cases n with
    | zero => rfl
    | succ n => exact h n hn

theorem Tm.erase_tyRename (r : ℕ → ℕ) (t : Tm) : (t.tyRename r).erase = t.erase := by
  induction t generalizing r with
  | var n => rfl
  | app t u iht ihu => simp only [Tm.tyRename, Tm.erase, iht, ihu]
  | lam A t ih => simp only [Tm.tyRename, Tm.erase, ih]
  | tapp t A ih => simp only [Tm.tyRename, Tm.erase, ih]
  | tlam t ih => simp only [Tm.tyRename, Tm.erase, ih]

theorem Tm.erase_tySubst (σ : ℕ → Ty) (t : Tm) : (t.tySubst σ).erase = t.erase := by
  induction t generalizing σ with
  | var n => rfl
  | app t u iht ihu => simp only [Tm.tySubst, Tm.erase, iht, ihu]
  | lam A t ih => simp only [Tm.tySubst, Tm.erase, ih]
  | tapp t A ih => simp only [Tm.tySubst, Tm.erase, ih]
  | tlam t ih => simp only [Tm.tySubst, Tm.erase, ih]

theorem Tm.erase_rename (r : ℕ → ℕ) (t : Tm) : (t.rename r).erase = t.erase.rename r := by
  induction t generalizing r with
  | var n => rfl
  | app t u iht ihu => simp only [Tm.rename, Tm.erase, ULam.rename, iht, ihu]
  | lam A t ih => simp only [Tm.rename, Tm.erase, ULam.rename, ih]
  | tapp t A ih => simp only [Tm.rename, Tm.erase, ih]
  | tlam t ih => simp only [Tm.rename, Tm.erase, ih]

theorem Tm.erase_subst (σ : ℕ → Tm) (t : Tm) :
    (t.subst σ).erase = t.erase.subst (fun n => (σ n).erase) := by
  induction t generalizing σ with
  | var n => rfl
  | app t u iht ihu => simp only [Tm.subst, Tm.erase, ULam.subst, iht, ihu]
  | lam A t ih =>
    simp only [Tm.subst, Tm.erase, ULam.subst, ih]
    congr 2; funext n
    cases n with
    | zero => rfl
    | succ n => exact Tm.erase_rename _ _
  | tapp t A ih => simp only [Tm.subst, Tm.erase, ih]
  | tlam t ih => simp only [Tm.subst, Tm.erase, ih, Tm.erase_tyRename]

theorem Tm.erase_substOne (t u : Tm) : (t.substOne u).erase = t.erase.substOne u.erase := by
  unfold Tm.substOne ULam.substOne
  rw [Tm.erase_subst]
  congr 1; funext n; cases n <;> rfl

/-! ### Related environments -/

theorem EnvRel.cons {Γ : Ctx} {η : ℕ → PER M.D} {ρ ρ' : ℕ → M.D} (hρ : EnvRel M Γ η ρ ρ')
    {A : Ty} {a a' : M.D} (ha : (A.interp M η).rel a a') :
    EnvRel M (A :: Γ) η (scons a ρ) (scons a' ρ') := by
  intro n B h
  cases n with
  | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; exact ha
  | succ n => exact hρ n B (by simpa using h)

theorem EnvRel.shift {Γ : Ctx} {η : ℕ → PER M.D} {ρ ρ' : ℕ → M.D} (hρ : EnvRel M Γ η ρ ρ')
    (X : PER M.D) : EnvRel M (Γ.map (Ty.rename Nat.succ)) (scons X η) ρ ρ' := by
  intro n B h
  obtain ⟨C, hC, rfl⟩ := getElem?_map_eq_some h
  rw [Ty.interp_rename]
  exact hρ n C hC

theorem EnvRel.symm {Γ : Ctx} {η : ℕ → PER M.D} {ρ ρ' : ℕ → M.D} (hρ : EnvRel M Γ η ρ ρ') :
    EnvRel M Γ η ρ' ρ := fun n B h => PER.symm _ (hρ n B h)

theorem EnvRel.right {Γ : Ctx} {η : ℕ → PER M.D} {ρ ρ' : ℕ → M.D} (hρ : EnvRel M Γ η ρ ρ') :
    EnvRel M Γ η ρ' ρ' := fun n B h => PER.trans _ (PER.symm _ (hρ n B h)) (hρ n B h)

/-- The fundamental lemma: typing is sound in every PER model. -/
theorem Typed.sound (h : Typed Γ t A) : Valid M Γ t A := by
  induction h with
  | var h => intro η ρ ρ' hρ; exact hρ _ _ h
  | app _ _ iht ihu =>
    intro η ρ ρ' hρ
    exact iht η ρ ρ' hρ _ _ (ihu η ρ ρ' hρ)
  | lam _ ih =>
    intro η ρ ρ' hρ a a' ha
    show (Ty.interp M _ η).rel (M.app (ULam.eval M ρ (.lam _)) a)
      (M.app (ULam.eval M ρ' (.lam _)) a')
    rw [ULam.eval_lam, ULam.eval_lam]
    exact ih η _ _ (hρ.cons ha)
  | tlam _ ih =>
    intro η ρ ρ' hρ X
    exact ih (scons X η) ρ ρ' (hρ.shift X)
  | @tapp Γ t A B _ ih =>
    intro η ρ ρ' hρ
    rw [Ty.interp_substOne]
    exact ih η ρ ρ' hρ (B.interp M η)

/-- Generalized substitution up to the PER: the left side evaluates in an
environment `ρ₁`, the right side substitutes `σ` and evaluates in `ρ'`. -/
theorem Typed.subst_sound_gen {Δ : Ctx} {t : Tm} {B : Ty} (h : Typed Δ t B)
    {η : ℕ → PER M.D} {ρ₁ ρ' : ℕ → M.D} {σ : ℕ → Tm}
    (hσ : ∀ (n : ℕ) (C : Ty), Δ[n]? = some C → (C.interp M η).rel (ρ₁ n) ((σ n).erase.eval M ρ')) :
    (B.interp M η).rel (t.erase.eval M ρ₁) ((t.subst σ).erase.eval M ρ') := by
  induction h generalizing η ρ₁ ρ' σ with
  | var h => exact hσ _ _ h
  | app _ _ iht ihu => exact iht hσ _ _ (ihu hσ)
  | lam _ ih =>
    intro a a' ha
    show (Ty.interp M _ η).rel (M.app (ULam.eval M ρ₁ (.lam _)) a)
      (M.app (ULam.eval M ρ' (.lam _)) a')
    rw [ULam.eval_lam, ULam.eval_lam]
    refine ih (σ := Tm.liftSub σ) (fun n C hC => ?_)
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hC; subst hC; exact ha
    | succ n =>
      show (C.interp M η).rel (ρ₁ n) ((Tm.rename Nat.succ (σ n)).erase.eval M (scons a' ρ'))
      rw [Tm.erase_rename, ULam.eval_rename]
      exact hσ n C (by simpa using hC)
  | tlam _ ih =>
    intro X
    refine ih (η := scons X η) (σ := fun n => Tm.tyRename Nat.succ (σ n)) (fun n C hC => ?_)
    obtain ⟨C', hC', rfl⟩ := getElem?_map_eq_some hC
    rw [Ty.interp_rename, Tm.erase_tyRename]
    exact hσ n C' hC'
  | @tapp Γ t A B _ ih =>
    rw [Ty.interp_substOne]
    exact ih hσ (B.interp M η)

/-- Substitution up to the PER: evaluating the body with the argument's value
is related to evaluating the substituted body. Equality fails in general
combinatory algebras (see `PER/Combinatory.lean`). -/
theorem Typed.subst_sound (ht : Typed (A :: Γ) t B) (hu : Typed Γ u A)
    {η : ℕ → PER M.D} {ρ ρ' : ℕ → M.D} (hρ : EnvRel M Γ η ρ ρ') :
    (B.interp M η).rel (t.erase.eval M (scons (u.erase.eval M ρ) ρ))
      ((t.substOne u).erase.eval M ρ') := by
  refine ht.subst_sound_gen (fun n C hC => ?_)
  cases n with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hC; subst hC
    exact hu.sound η ρ ρ' hρ
  | succ n => exact hρ n C (by simpa using hC)

/-- βη-equality (with type β/η) is sound in every PER model. -/
theorem TmEq.sound (h : TmEq Γ t u A) : ValidEq M Γ t u A := by
  induction h with
  | refl h => exact h.sound
  | symm _ ih => intro η ρ ρ' hρ; exact PER.symm _ (ih η ρ' ρ hρ.symm)
  | trans _ _ ih1 ih2 =>
    intro η ρ ρ' hρ; exact PER.trans _ (ih1 η ρ ρ' hρ) (ih2 η ρ' ρ' hρ.right)
  | beta ht hu =>
    intro η ρ ρ' hρ
    show (Ty.interp M _ η).rel (M.app (ULam.eval M ρ (.lam _)) _) _
    rw [ULam.eval_lam]
    exact ht.subst_sound hu hρ
  | eta ht =>
    intro η ρ ρ' hρ a a' ha
    show (Ty.interp M _ η).rel (M.app (ULam.eval M ρ (.lam _)) a) _
    rw [ULam.eval_lam]
    simp only [Tm.erase, ULam.eval_app, ULam.eval_var, scons_zero, Tm.erase_rename,
      ULam.eval_rename]
    exact ht.sound η ρ ρ' hρ a a' ha
  | tbeta ht =>
    intro η ρ ρ' hρ
    simp only [Tm.erase, Tm.tySubstOne, Tm.erase_tySubst, Ty.interp_substOne]
    exact ht.sound _ ρ ρ' (hρ.shift _)
  | teta ht =>
    intro η ρ ρ' hρ X
    show (Ty.interp M _ _).rel ((Tm.tyRename Nat.succ _).erase.eval M ρ) _
    rw [Tm.erase_tyRename]
    exact ht.sound η ρ ρ' hρ X
  | app _ _ ih1 ih2 =>
    intro η ρ ρ' hρ
    exact ih1 η ρ ρ' hρ _ _ (ih2 η ρ ρ' hρ)
  | lam _ ih =>
    intro η ρ ρ' hρ a a' ha
    show (Ty.interp M _ η).rel (M.app (ULam.eval M ρ (.lam _)) a)
      (M.app (ULam.eval M ρ' (.lam _)) a')
    rw [ULam.eval_lam, ULam.eval_lam]
    exact ih η _ _ (hρ.cons ha)
  | @tapp Γ t t' A B _ ih =>
    intro η ρ ρ' hρ
    rw [Ty.interp_substOne]
    exact ih η ρ ρ' hρ (B.interp M η)
  | tlam _ ih =>
    intro η ρ ρ' hρ X
    exact ih (scons X η) ρ ρ' (hρ.shift X)

/-! ## Nondegeneracy -/

/-- Church booleans `∀X. X → X → X`. -/
def boolTy : Ty := .all (.arr (.var 0) (.arr (.var 0) (.var 0)))

/-- `ΛX. λx:X. λy:X. x`. -/
def tru : Tm := .tlam (.lam (.var 0) (.lam (.var 0) (.var 1)))

/-- `ΛX. λx:X. λy:X. y`. -/
def fls : Tm := .tlam (.lam (.var 0) (.lam (.var 0) (.var 0)))

theorem tru_typed : Typed [] tru boolTy :=
  .tlam (.lam (.lam (.var rfl)))

theorem fls_typed : Typed [] fls boolTy :=
  .tlam (.lam (.lam (.var rfl)))

/-- In any combinatory algebra with `K ≠ S` the two Church booleans are
inequivalent realizers of `∀X. X → X → X`. -/
theorem bool_distinct (h : M.k ≠ M.s) (η : ℕ → PER M.D) (ρ ρ' : ℕ → M.D) :
    ¬ (boolTy.interp M η).rel (tru.erase.eval M ρ) (fls.erase.eval M ρ') := by
  intro hr
  let E : PER M.D := ⟨Eq, fun _ _ h => h.symm, fun _ _ _ h k => h.trans k⟩
  have := hr E M.k M.k rfl M.s M.s rfl
  change M.app (M.app (ULam.eval M ρ (.lam (.lam (.var 1)))) M.k) M.s =
    M.app (M.app (ULam.eval M ρ' (.lam (.lam (.var 0)))) M.k) M.s at this
  rw [ULam.eval_lam, ULam.eval_lam, ULam.eval_lam, ULam.eval_lam] at this
  exact h this

end Silmaril.Calculi.LambdaCube.PERModel.SystemF
