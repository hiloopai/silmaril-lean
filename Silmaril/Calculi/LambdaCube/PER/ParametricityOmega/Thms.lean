module

public import Silmaril.Calculi.LambdaCube.PER.ParametricityOmega.Defs
import Silmaril.Proofs.Calculi.LambdaCube.PER.ParametricityOmega

@[expose] public section

set_option autoImplicit true

/-! Abstraction and free theorems for the purely relational Fω model. -/

namespace Silmaril.Calculi.LambdaCube.PERModel

namespace SystemFOmega

variable {M : CombAlg.{u}}

/-- Fω abstraction for the relation-transformer model: typed terms map related
environments to related realizers. See Atkey 2012, Theorem 3, for the
reflexive-graph formulation. -/
theorem Typed.abstraction (h : Typed Δ Γ t A) (hΓ : ∀ B ∈ Γ, Kinded Δ B .star)
    {ξ : ℕ → REntry M.D} (hξ : RFits M Δ ξ) {ρ₁ ρ₂ : ℕ → M.D} (hρ : RelCtx M Γ ξ ρ₁ ρ₂) :
    A.rinterp M ξ .star (t.erase.eval M ρ₁) (t.erase.eval M ρ₂) :=
  Silmaril.Proofs.Calculi.LambdaCube.PER.ParametricityOmega.Omega.abstraction h hΓ hξ hρ

/-- The abstraction theorem for closed terms. -/
theorem Typed.abstraction_closed (h : Typed [] [] t A) (ξ : ℕ → REntry M.D)
    (ρ₁ ρ₂ : ℕ → M.D) : A.rinterp M ξ .star (t.erase.eval M ρ₁) (t.erase.eval M ρ₂) :=
  Silmaril.Proofs.Calculi.LambdaCube.PER.ParametricityOmega.Omega.abstraction_closed h ξ ρ₁ ρ₂

/-- Every closed inhabitant of `∀X. X → X` realizes the identity. -/
theorem free_id (h : Typed [] [] t idTy) (ρ : ℕ → M.D) (a : M.D) :
    M.app (t.erase.eval M ρ) a = a :=
  Silmaril.Proofs.Calculi.LambdaCube.PER.ParametricityOmega.Omega.free_id h ρ a

/-- Higher-kinded free theorem: every closed inhabitant of
`∀ F : * → *. ∀ X. F X → F X` realizes the identity (instantiate `F` at the
constant relation transformer with value `{(a, a)}`). -/
theorem free_hkId (h : Typed [] [] t hkIdTy) (ρ : ℕ → M.D) (a : M.D) :
    M.app (t.erase.eval M ρ) a = a :=
  Silmaril.Proofs.Calculi.LambdaCube.PER.ParametricityOmega.Omega.free_hkId h ρ a

end SystemFOmega

namespace SystemF

variable {M : CombAlg.{u}}

/-- Reynolds' abstraction theorem for System F in the purely relational model:
the kind-`*` instance of `SystemFOmega.Typed.abstraction`. -/
theorem Typed.abstraction_rel (h : Typed Γ t A) (R : ℕ → M.D → M.D → Prop)
    {ρ₁ ρ₂ : ℕ → M.D} (hρ : ∀ n (B : Ty), Γ[n]? = some B → B.rinterp M R (ρ₁ n) (ρ₂ n)) :
    A.rinterp M R (t.erase.eval M ρ₁) (t.erase.eval M ρ₂) :=
  Silmaril.Proofs.Calculi.LambdaCube.PER.ParametricityOmega.abstraction_rel h R hρ

end SystemF

end Silmaril.Calculi.LambdaCube.PERModel
