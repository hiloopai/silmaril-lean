module

public import Silmaril.Calculi.LambdaCube.PER.Parametricity.Defs

@[expose] public section

set_option autoImplicit true

namespace Silmaril.Proofs.Calculi.LambdaCube.PER.Parametricity

open Silmaril.Calculi.LambdaCube.PERModel Silmaril.Calculi.LambdaCube.PERModel.SystemF

variable {M : CombAlg.{u}}

/-- **Reynolds' abstraction theorem** for System F in the PER model: a typed
term's erasure, evaluated in related environments, gives related realizers. -/
theorem abstraction (h : Typed Γ t A) (E : RelEnv M) {ρ₁ ρ₂ : ℕ → M.D}
    (hρ : RelCtx Γ E ρ₁ ρ₂) : A.relR E (t.erase.eval M ρ₁) (t.erase.eval M ρ₂) := by
  induction h generalizing E ρ₁ ρ₂ with
  | var h => exact hρ _ _ h
  | app _ _ iht ihu =>
    simp only [Tm.erase, ULam.eval_app]
    exact (iht E hρ).2.2 _ _ (ihu E hρ)
  | @lam A Γ t B ht ih =>
    refine ⟨(Typed.lam ht).sound E.η₁ ρ₁ ρ₁ hρ.envRel₁,
      (Typed.lam ht).sound E.η₂ ρ₂ ρ₂ hρ.envRel₂, fun a b hab => ?_⟩
    show B.relR E (M.app (ULam.eval M ρ₁ (.lam _)) a) (M.app (ULam.eval M ρ₂ (.lam _)) b)
    rw [ULam.eval_lam, ULam.eval_lam]
    refine ih E (fun n C hC => ?_)
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hC; subst hC; exact hab
    | succ n => exact hρ n C (by simpa using hC)
  | @tlam Γ t A ht ih =>
    refine ⟨(Typed.tlam ht).sound E.η₁ ρ₁ ρ₁ hρ.envRel₁,
      (Typed.tlam ht).sound E.η₂ ρ₂ ρ₂ hρ.envRel₂, fun X Y S hS => ?_⟩
    refine ih (E.cons X Y S hS) (fun n C hC => ?_)
    obtain ⟨C', hC', rfl⟩ := getElem?_map_eq_some hC
    rw [Ty.relR_rename_succ]
    exact hρ n C' hC'
  | @tapp Γ t A B _ ih =>
    rw [Ty.relR_substOne]
    exact (ih E hρ).2.2 _ _ _ _

/-- The abstraction theorem for closed terms. -/
theorem abstraction_closed (h : Typed [] t A) (E : RelEnv M) (ρ₁ ρ₂ : ℕ → M.D) :
    A.relR E (t.erase.eval M ρ₁) (t.erase.eval M ρ₂) :=
  abstraction h E (fun n B hB => by simp at hB)

/-! ## Free theorems -/

/-- In the plain PER model every element of `∀X. X → X` is the identity:
instantiate at the singleton PER. -/
theorem interp_polyId_rel (η : ℕ → PER M.D) {e e' : M.D}
    (h : (idTy.interp M η).rel e e') (a : M.D) : M.app e a = a ∧ M.app e' a = a := by
  have := h (PER.single a) a a ⟨rfl, rfl⟩
  exact this

/-- Free theorem for `I : ∀X. X → X` (Wadler 1989, Figure 1): every closed
inhabitant realizes the identity. -/
theorem free_id (h : Typed [] t idTy) (ρ : ℕ → M.D) (a : M.D) :
    M.app (t.erase.eval M ρ) a = a :=
  (abstraction_closed h RelEnv.empty ρ ρ).2.2 PER.eq PER.eq (fun x _ => x = a)
    (PER.isSatRel_eq _) |>.2.2 a a rfl

/-- Free theorem for `K : ∀X. ∀Y. X → Y → X` (Wadler 1989, Figure 1). -/
theorem free_K (h : Typed [] t kTy) (ρ : ℕ → M.D) (a b : M.D) :
    M.app (M.app (t.erase.eval M ρ) a) b = a := by
  have h1 := (abstraction_closed h RelEnv.empty ρ ρ).2.2 PER.eq PER.eq (fun x _ => x = a)
    (PER.isSatRel_eq _)
  have h2 := h1.2.2 PER.eq PER.eq (fun y _ => y = b) (PER.isSatRel_eq _)
  exact (h2.2.2 a a rfl).2.2 b b rfl

/-- Free theorem for the Church booleans: an inhabitant of `∀X. X → X → X`
selects the same argument position at every pair of arguments, via the
relation `{(a, c), (b, d)}` between discrete PERs, which need not itself be a PER. -/
theorem free_bool (h : Typed [] t boolTy) (ρ : ℕ → M.D) (a b c d : M.D) :
    (M.app (M.app (t.erase.eval M ρ) a) b = a ∧ M.app (M.app (t.erase.eval M ρ) c) d = c) ∨
      (M.app (M.app (t.erase.eval M ρ) a) b = b ∧
        M.app (M.app (t.erase.eval M ρ) c) d = d) := by
  have h1 := (abstraction_closed h RelEnv.empty ρ ρ).2.2 PER.eq PER.eq
    (fun x y => (x = a ∧ y = c) ∨ (x = b ∧ y = d)) (PER.isSatRel_eq _)
  exact (h1.2.2 a c (Or.inl ⟨rfl, rfl⟩)).2.2 b d (Or.inr ⟨rfl, rfl⟩)

/-- The Church booleans `tru` and `fls` realize the two projections; with
`free_bool` every closed boolean behaves like one of them. -/
theorem tru_app (ρ : ℕ → M.D) (a b : M.D) :
    M.app (M.app (tru.erase.eval M ρ) a) b = a := by
  change M.app (M.app (ULam.eval M ρ (.lam (.lam (.var 1)))) a) b = a
  rw [ULam.eval_lam, ULam.eval_lam]; rfl

theorem fls_app (ρ : ℕ → M.D) (a b : M.D) :
    M.app (M.app (fls.erase.eval M ρ) a) b = b := by
  change M.app (M.app (ULam.eval M ρ (.lam (.lam (.var 0)))) a) b = b
  rw [ULam.eval_lam, ULam.eval_lam]; rfl

/-- A closed Church boolean chooses one argument position for all inputs. -/
theorem free_bool_uniform (h : Typed [] t boolTy) (ρ : ℕ → M.D) :
    (∀ a b, M.app (M.app (t.erase.eval M ρ) a) b = a) ∨
      (∀ a b, M.app (M.app (t.erase.eval M ρ) a) b = b) := by
  classical
  by_cases hfirst : ∀ a b, M.app (M.app (t.erase.eval M ρ) a) b = a
  · exact Or.inl hfirst
  · right
    push Not at hfirst
    obtain ⟨c, d, hcd⟩ := hfirst
    intro a b
    rcases free_bool h ρ c d a b with hp | hp
    · exact (hcd hp.1).elim
    · exact hp.2

end Silmaril.Proofs.Calculi.LambdaCube.PER.Parametricity
