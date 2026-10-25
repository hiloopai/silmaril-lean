module

public import Silmaril.Logic.Arithmetic.Defs
import Silmaril.Proofs.Logic.Arithmetic.Soundness

@[expose] public section

namespace Silmaril.Logic.Arithmetic.Derivation

variable {n : ℕ} {Γ : Context n} {ψ : Formula n}
variable {Ax : {n : ℕ} → Formula n → Type}

/-- Soundness with assumptions, including the eigenvariable cases. -/
theorem sound (hAx : ∀ {n} {φ : Formula n}, Ax φ → Valid φ)
    (d : Derivation Ax Γ ψ) (e : Assignment n) (hΓ : Satisfies e Γ) : ψ.eval e :=
  Silmaril.Proofs.Logic.Arithmetic.derivation_sound hAx d e hΓ

end Silmaril.Logic.Arithmetic.Derivation
