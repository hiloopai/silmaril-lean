module

public import Silmaril.X86.Extends.Defs

/-!
# Runs along a machine extension

`run`: a run of `I` from the view of `x` is a run of `J` from `x` of the same length, ending
at `x` with its view replaced.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Extends

open Silmaril.X86.SegVC (Isa)

theorem run {σ τ : Type} {I : Isa σ} {J : Isa τ} (E : I.Extends J) (n : Nat) {x : τ} {t : σ}
    (h : Silmaril.Machine.Execution.run I.step n (E.view x) = some t) :
    Silmaril.Machine.Execution.run J.step n x = some (E.put x t) := by
  obtain ⟨y, hy, rfl⟩ := Silmaril.Machine.Execution.run_simulates I.step J.step
    (fun s y => y = E.put x s)
    (fun s y s' hy hs => ⟨E.put x s', by
      subst hy
      rw [E.step (by rw [E.view_put]; exact hs), E.put_put], rfl⟩)
    n (E.put_view x).symm h
  exact hy

end Silmaril.Proofs.X86.Extends
