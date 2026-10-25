module

public import Silmaril.Compile.PassAPI.Checked.Defs

@[expose] public section

namespace Silmaril.Compile.PassAPI.Proofs.Checked

universe u
variable {X : Type u} {C : Contract X}

theorem checked_run (c : CheckedPass C) (x : X) :
    c.checked.run x = if c.check x (c.transform x) then c.transform x else x := rfl

theorem checked_run_of_check {c : CheckedPass C} {x : X}
    (h : c.check x (c.transform x) = true) : c.checked.run x = c.transform x := by
  simp [checked_run, h]

theorem checked_run_of_not_check {c : CheckedPass C} {x : X}
    (h : c.check x (c.transform x) = false) : c.checked.run x = x := by
  simp [checked_run, h]

theorem checked_seq_run_of_check (c d : CheckedPass C) {x : X}
    (h₁ : c.check x (c.transform x) = true)
    (h₂ : d.check (c.transform x) (d.transform (c.transform x)) = true) :
    (c.seq d).checked.run x = (c.checked * d.checked).run x := by
  rw [Pass.mul_run, checked_run_of_check h₁, checked_run_of_check h₂, checked_run]
  simp [CheckedPass.seq, h₁, h₂]

theorem checked_seq_run_of_not_check₁ (c d : CheckedPass C) {x : X}
    (h₁ : c.check x (c.transform x) = false) :
    (c.seq d).checked.run x = x ∧ (c.checked * d.checked).run x = d.checked.run x := by
  refine ⟨?_, ?_⟩
  · rw [checked_run]; simp [CheckedPass.seq, h₁]
  · rw [Pass.mul_run, checked_run_of_not_check h₁]

theorem checked_seq_ne_seq_checked :
    (cTrue.seq cReject).checked ≠ cTrue.checked * cReject.checked := by
  intro h
  have := congrArg (fun p : Pass trivialContract => p.run false) h
  simp [CheckedPass.seq, cTrue, cReject, Pass.checked] at this

theorem cfoldPass_sound (e : Toy.AExp) : (Toy.cfoldPass.run e).eval = e.eval :=
  (show e.eval = (Toy.cfoldPass.run e).eval from Toy.cfoldPass.sound trivial).symm

end Silmaril.Compile.PassAPI.Proofs.Checked
