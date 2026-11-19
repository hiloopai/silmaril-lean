module

public import Silmaril.Containers.Outcome.Defs

public section
namespace Silmaril.Proofs.Containers.Outcome
open Silmaril.Containers
variable {U : Type}

theorem approx_trans {a b c : Outcome U} (h : a.Approx b) (k : b.Approx c) : a.Approx c := by
  rcases k with rfl | ⟨u, rfl⟩
  · exact h
  · exact .inr ⟨u, rfl⟩

theorem mutual_iff_erase (a b : Outcome U) :
    (a.Approx b ∧ b.Approx a) ↔ a.erase = b.erase := by
  cases a <;> cases b <;> simp [Outcome.Approx, Outcome.erase, Outcome.mapUB] <;> exact Eq.symm

/-- A more-UB certificate implies the default one, but a defined trap need not meet the
more-UB policy. No claim about guest progress follows from either certificate. -/
theorem trap_policy (u : U) (s : Outcome U) :
    (s.trapAsUB u).NoUB → s.NoUB := by
  cases s <;> simp [Outcome.trapAsUB, Outcome.NoUB]

end Silmaril.Proofs.Containers.Outcome
