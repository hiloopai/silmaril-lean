module

public import Silmaril.Calculi.LambdaCube.PER.ParametricityOmega.Defs

@[expose] public section

set_option autoImplicit true

namespace Silmaril.Proofs.Calculi.LambdaCube.PER.ParametricityOmega

open Silmaril.Calculi.LambdaCube.PERModel

namespace Omega

open Silmaril.Calculi.LambdaCube.PERModel.SystemFOmega

variable {M : CombAlg.{u}}

/-- Fω abstraction for the relation-transformer model: typed terms map related
environments to related realizers. See Atkey 2012, Theorem 3, for the
reflexive-graph formulation. -/
theorem abstraction (h : Typed Δ Γ t A) (hΓ : ∀ B ∈ Γ, Kinded Δ B .star)
    {ξ : ℕ → REntry M.D} (hξ : RFits M Δ ξ) {ρ₁ ρ₂ : ℕ → M.D} (hρ : RelCtx M Γ ξ ρ₁ ρ₂) :
    A.rinterp M ξ .star (t.erase.eval M ρ₁) (t.erase.eval M ρ₂) := by
  induction h generalizing ξ ρ₁ ρ₂ with
  | var hn => exact hρ _ _ hn
  | app _ _ ih1 ih2 =>
    have h1 := ih1 hΓ hξ hρ
    rw [Con.rinterp_arr_star] at h1
    exact h1 _ _ (ih2 hΓ hξ hρ)
  | lam hA _ ih =>
    rw [Con.rinterp_arr_star]
    intro a b hab
    simp only [Tm.erase]
    rw [ULam.eval_lam, ULam.eval_lam]
    exact ih (ctx_cons_kinded hA hΓ) hξ (hρ.cons hab)
  | tlam _ ih =>
    rw [Con.rinterp_all_star]
    intro X
    exact ih (ctx_shift_kinded hΓ) (hξ.cons X) (hρ.shift X)
  | tapp ht hC ih =>
    cases ht.kinded hΓ with
    | all hA =>
      rw [Con.rinterp_substOne hA hC hξ]
      have h1 := ih hΓ hξ hρ
      rw [Con.rinterp_all_star] at h1
      exact h1 _
  | conv _ hAB ih =>
    rw [← ConEq.rsound hAB hξ]
    exact ih hΓ hξ hρ

/-- The abstraction theorem for closed terms. -/
theorem abstraction_closed (h : Typed [] [] t A) (ξ : ℕ → REntry M.D)
    (ρ₁ ρ₂ : ℕ → M.D) : A.rinterp M ξ .star (t.erase.eval M ρ₁) (t.erase.eval M ρ₂) := by
  have hξ : RFits M [] ξ := fun n k h => by simp at h
  exact abstraction h (by simp) hξ (fun n A h => by simp at h)

/-! ## Free theorems -/

/-- Every closed inhabitant of `∀X. X → X` realizes the identity. -/
theorem free_id (h : Typed [] [] t idTy) (ρ : ℕ → M.D) (a : M.D) :
    M.app (t.erase.eval M ρ) a = a := by
  have h1 := abstraction_closed h (fun _ => ⟨.star, Kind.rdefault .star⟩) ρ ρ
  rw [idTy, Con.rinterp_all_star] at h1
  have h2 := h1 (fun x y => x = a ∧ y = a)
  rw [Con.rinterp_arr_star,
    rinterp_var_of_eq (ξ := scons ⟨.star, fun x y => x = a ∧ y = a⟩ _) (n := 0) rfl] at h2
  exact (h2 a a ⟨rfl, rfl⟩).1

/-- Higher-kinded free theorem: every closed inhabitant of
`∀ F : * → *. ∀ X. F X → F X` realizes the identity (instantiate `F` at the
constant relation transformer with value `{(a, a)}`). -/
theorem free_hkId (h : Typed [] [] t hkIdTy) (ρ : ℕ → M.D) (a : M.D) :
    M.app (t.erase.eval M ρ) a = a := by
  have h1 := abstraction_closed h (fun _ => ⟨.star, Kind.rdefault .star⟩) ρ ρ
  rw [hkIdTy, Con.rinterp_all_star] at h1
  have h2 := h1 (fun _ => fun x y => x = a ∧ y = a)
  rw [Con.rinterp_all_star] at h2
  have h3 := h2 (Kind.rdefault .star)
  rw [Con.rinterp_arr_star] at h3
  have e : (Con.app (.var 1) (.var 0)).rinterp M
      (scons ⟨.star, Kind.rdefault .star⟩
        (scons ⟨.arr .star .star, fun _ => fun x y => x = a ∧ y = a⟩
          (fun _ => ⟨.star, Kind.rdefault .star⟩))) .star = fun x y => x = a ∧ y = a := by
    rw [rinterp_app_of_infer (k := .star) rfl, rinterp_var_of_eq (n := 1) rfl]
  rw [e] at h3
  exact (h3 a a ⟨rfl, rfl⟩).1

end Omega

open Silmaril.Calculi.LambdaCube.PERModel.SystemF

variable {M : CombAlg.{u}}

/-- Reynolds' abstraction theorem for System F in the purely relational model:
the kind-`*` instance of `SystemFOmega.Typed.abstraction`. -/
theorem abstraction_rel (h : Typed Γ t A) (R : ℕ → M.D → M.D → Prop)
    {ρ₁ ρ₂ : ℕ → M.D} (hρ : ∀ n (B : Ty), Γ[n]? = some B → B.rinterp M R (ρ₁ n) (ρ₂ n)) :
    A.rinterp M R (t.erase.eval M ρ₁) (t.erase.eval M ρ₂) := by
  obtain ⟨n₁, hΓn⟩ := ctx_exists_freeIn_bound Γ
  obtain ⟨n₂, htn⟩ := Tm.exists_tyFreeIn_bound t
  have hω := SystemFOmega.typed_ofF h (max n₁ n₂)
    (fun B hB m hm => lt_max_of_lt_left (hΓn B hB m hm))
    (fun m hm => lt_max_of_lt_right (htn m hm))
  have hΓω : ∀ B ∈ Γ.map SystemFOmega.ofF,
      SystemFOmega.Kinded (List.replicate (max n₁ n₂) .star) B .star := by
    intro B hB
    obtain ⟨B0, hB0, rfl⟩ := List.mem_map.mp hB
    exact SystemFOmega.kinded_ofF B0 _ fun m hm => lt_max_of_lt_left (hΓn B0 hB0 m hm)
  have hξ : SystemFOmega.RFits M (List.replicate (max n₁ n₂) .star)
      (fun n => ⟨.star, R n⟩) := by
    intro m k hm
    exact (List.eq_of_mem_replicate (List.mem_of_getElem? hm)).symm
  have hρω : SystemFOmega.RelCtx M (Γ.map SystemFOmega.ofF) (fun n => ⟨.star, R n⟩) ρ₁ ρ₂ := by
    intro m B hm
    rw [List.getElem?_map] at hm
    cases hB0 : Γ[m]? with
    | none => simp [hB0] at hm
    | some B0 =>
      simp only [hB0, Option.map_some, Option.some.injEq] at hm
      subst hm
      rw [rinterp_ofF]
      exact hρ m B0 hB0
  have := Omega.abstraction hω hΓω hξ hρω
  rwa [rinterp_ofF, SystemFOmega.erase_ofFTm] at this


end Silmaril.Proofs.Calculi.LambdaCube.PER.ParametricityOmega
