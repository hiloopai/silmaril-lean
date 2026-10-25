module

public import Silmaril.Compile.PassAPI.Checked.Defs
import Silmaril.Proofs.Compile.PassAPI.Checked.Correctness

@[expose] public section

/-! # Checked-pass equations and sequencing behavior

These declarations expose the public statements; their proofs and the Boolean
counterexample live in `Silmaril.Proofs.Compile.PassAPI.Checked`.
-/

namespace Silmaril.Compile.PassAPI

universe u
variable {X : Type u} {C : Contract X}

namespace CheckedPass

theorem checked_run (c : CheckedPass C) (x : X) :
    c.checked.run x = if c.check x (c.transform x) then c.transform x else x := rfl

theorem checked_run_of_check {c : CheckedPass C} {x : X}
    (h : c.check x (c.transform x) = true) : c.checked.run x = c.transform x :=
  Proofs.Checked.checked_run_of_check h

theorem checked_run_of_not_check {c : CheckedPass C} {x : X}
    (h : c.check x (c.transform x) = false) : c.checked.run x = x :=
  Proofs.Checked.checked_run_of_not_check h

/-- If both checks accept, transactional and stepwise checked sequencing agree. -/
theorem checked_seq_run_of_check (c d : CheckedPass C) {x : X}
    (h₁ : c.check x (c.transform x) = true)
    (h₂ : d.check (c.transform x) (d.transform (c.transform x)) = true) :
    (c.seq d).checked.run x = (c.checked * d.checked).run x :=
  Proofs.Checked.checked_seq_run_of_check c d h₁ h₂

/-- A failed first check aborts the transaction; stepwise sequencing still tries `d`. -/
theorem checked_seq_run_of_not_check₁ (c d : CheckedPass C) {x : X}
    (h₁ : c.check x (c.transform x) = false) :
    (c.seq d).checked.run x = x ∧ (c.checked * d.checked).run x = d.checked.run x :=
  Proofs.Checked.checked_seq_run_of_not_check₁ c d h₁

end CheckedPass

/-- Transactional fallback and per-step fallback differ in general. -/
theorem checked_seq_ne_seq_checked :
    (cTrue.seq cReject).checked ≠ cTrue.checked * cReject.checked :=
  Proofs.Checked.checked_seq_ne_seq_checked

/-- Evaluation validates the example constant-folding pass. -/
theorem Toy.cfoldPass_sound (e : Toy.AExp) : (Toy.cfoldPass.run e).eval = e.eval :=
  Proofs.Checked.cfoldPass_sound e

end Silmaril.Compile.PassAPI
