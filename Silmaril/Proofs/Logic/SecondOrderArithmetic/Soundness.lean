module

public import Silmaril.Logic.SecondOrderArithmetic.Defs
public import Silmaril.Logic.SecondOrderArithmetic.Hilbert

@[expose] public section

namespace Silmaril.Proofs.Logic.SecondOrderArithmetic

open Silmaril.Logic.SecondOrderArithmetic

variable {N : Type} [DecidableEq N] {S : Subsystem} {p : Formula N}

theorem proof_sound (M : HenkinStructure) (h : ValidAxioms (N := N) S M)
    (d : Proof S p) : ∀ ρ : M.Env N, p.henkinEval M ρ := by
  induction d with
  | «axiom» a => exact h a
  | mp _ _ ihp ihi => exact fun ρ => ihi ρ (ihp ρ)
  | gen x _ ih => exact fun ρ n => ih (Function.update ρ (.inl x) n)
  | setGen X _ ih => exact fun ρ A => ih (Function.update ρ (.inr X) A)

theorem hilbert_sound (M : HenkinStructure) (d : HilbertProof p) :
    ∀ ρ : M.Env N, p.henkinEval M ρ := by
  induction d with
  | ax1 _ _ => exact fun _ hp _ => hp
  | ax2 _ _ _ => exact fun _ hpq hq hp => hpq hp (hq hp)
  | ax3 _ _ =>
    intro ρ hn hp
    exact Classical.byContradiction (fun h => hn h hp)
  | mp _ _ ihp ihi => exact fun ρ => ihi ρ (ihp ρ)

end Silmaril.Proofs.Logic.SecondOrderArithmetic
