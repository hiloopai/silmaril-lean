module

public import Silmaril.Calculi.LambdaCube.PER.Parametricity.Defs
import Silmaril.Proofs.Calculi.LambdaCube.PER.Parametricity

@[expose] public section

set_option autoImplicit true

/-! The abstraction theorem and free theorems for saturated relations between PERs. -/

namespace Silmaril.Calculi.LambdaCube.PERModel.SystemF

variable {M : CombAlg.{u}}

/-- **Reynolds' abstraction theorem** for System F in the PER model: a typed
term's erasure, evaluated in related environments, gives related realizers. -/
theorem Typed.abstraction (h : Typed Γ t A) (E : RelEnv M) {ρ₁ ρ₂ : ℕ → M.D}
    (hρ : RelCtx Γ E ρ₁ ρ₂) : A.relR E (t.erase.eval M ρ₁) (t.erase.eval M ρ₂) :=
  Silmaril.Proofs.Calculi.LambdaCube.PER.Parametricity.abstraction h E hρ

/-- The abstraction theorem for closed terms. -/
theorem Typed.abstraction_closed (h : Typed [] t A) (E : RelEnv M) (ρ₁ ρ₂ : ℕ → M.D) :
    A.relR E (t.erase.eval M ρ₁) (t.erase.eval M ρ₂) :=
  Silmaril.Proofs.Calculi.LambdaCube.PER.Parametricity.abstraction_closed h E ρ₁ ρ₂

/-- In the plain PER model every element of `∀X. X → X` is the identity:
instantiate at the singleton PER. -/
theorem interp_polyId_rel (η : ℕ → PER M.D) {e e' : M.D}
    (h : (idTy.interp M η).rel e e') (a : M.D) : M.app e a = a ∧ M.app e' a = a :=
  Silmaril.Proofs.Calculi.LambdaCube.PER.Parametricity.interp_polyId_rel η h a

/-- Free theorem for `I : ∀X. X → X` (Wadler 1989, Figure 1): every closed
inhabitant realizes the identity. -/
theorem free_id (h : Typed [] t idTy) (ρ : ℕ → M.D) (a : M.D) :
    M.app (t.erase.eval M ρ) a = a :=
  Silmaril.Proofs.Calculi.LambdaCube.PER.Parametricity.free_id h ρ a

/-- Free theorem for `K : ∀X. ∀Y. X → Y → X` (Wadler 1989, Figure 1). -/
theorem free_K (h : Typed [] t kTy) (ρ : ℕ → M.D) (a b : M.D) :
    M.app (M.app (t.erase.eval M ρ) a) b = a :=
  Silmaril.Proofs.Calculi.LambdaCube.PER.Parametricity.free_K h ρ a b

/-- Free theorem for the Church booleans: an inhabitant of `∀X. X → X → X`
selects the same argument position at every pair of arguments, via the
relation `{(a, c), (b, d)}` between discrete PERs, which need not itself be a PER. -/
theorem free_bool (h : Typed [] t boolTy) (ρ : ℕ → M.D) (a b c d : M.D) :
    (M.app (M.app (t.erase.eval M ρ) a) b = a ∧ M.app (M.app (t.erase.eval M ρ) c) d = c) ∨
      (M.app (M.app (t.erase.eval M ρ) a) b = b ∧
        M.app (M.app (t.erase.eval M ρ) c) d = d) :=
  Silmaril.Proofs.Calculi.LambdaCube.PER.Parametricity.free_bool h ρ a b c d

/-- The Church booleans `tru` and `fls` realize the two projections; with
`free_bool` every closed boolean behaves like one of them. -/
theorem tru_app (ρ : ℕ → M.D) (a b : M.D) :
    M.app (M.app (tru.erase.eval M ρ) a) b = a :=
  Silmaril.Proofs.Calculi.LambdaCube.PER.Parametricity.tru_app ρ a b

theorem fls_app (ρ : ℕ → M.D) (a b : M.D) :
    M.app (M.app (fls.erase.eval M ρ) a) b = b :=
  Silmaril.Proofs.Calculi.LambdaCube.PER.Parametricity.fls_app ρ a b

/-- Every closed Church boolean is uniformly the first or the second projection. -/
theorem free_bool_uniform (h : Typed [] t boolTy) (ρ : ℕ → M.D) :
    (∀ a b, M.app (M.app (t.erase.eval M ρ) a) b = a) ∨
      (∀ a b, M.app (M.app (t.erase.eval M ρ) a) b = b) :=
  Silmaril.Proofs.Calculi.LambdaCube.PER.Parametricity.free_bool_uniform h ρ

end Silmaril.Calculi.LambdaCube.PERModel.SystemF
