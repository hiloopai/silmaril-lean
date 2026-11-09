module

public import Silmaril.X86.Extends.Defs
import Silmaril.Proofs.X86.Extends.Run

/-!
# Machine extensions: runs and composition

* `run`, `reaches`: **every run of `I` from the view is a run of `J`** that changes only
  the view (same length);
* `trans`: extensions compose, so a tower `I ⊑ J ⊑ K` needs one lemma per edge.
-/

@[expose] public section

namespace Silmaril.X86.SegVC.Isa.Extends

open Silmaril.Machine.Execution (run Reaches)

variable {σ τ υ : Type} {I : Isa σ} {J : Isa τ} {K : Isa υ}

/-- A run of `I` of length `n` from the view of `x` is a run of `J` of length `n` from `x`. -/
theorem run (E : I.Extends J) (n : Nat) {x : τ} {t : σ}
    (h : Silmaril.Machine.Execution.run I.step n (E.view x) = some t) :
    Silmaril.Machine.Execution.run J.step n x = some (E.put x t) :=
  Silmaril.Proofs.X86.Extends.run E n h

/-- **A run of `I` from the view of `x` is a run of `J` from `x`.** -/
theorem reaches (E : I.Extends J) {x : τ} {t : σ} (h : Reaches I.step (E.view x) t) :
    Reaches J.step x (E.put x t) :=
  let ⟨n, hn⟩ := h; ⟨n, E.run n hn⟩

/-- **Extensions compose.** -/
@[reducible] def trans (E : I.Extends J) (F : J.Extends K) : I.Extends K where
  view z := E.view (F.view z)
  put z s := F.put z (E.put (F.view z) s)
  view_put z s := by rw [F.view_put, E.view_put]
  put_put z s s' := by rw [F.view_put, E.put_put, F.put_put]
  put_view z := by rw [E.put_view, F.put_view]
  core z := (F.core z).trans (E.core _)
  mem z := (F.mem z).trans (E.mem _)
  upd z c m := by rw [F.upd, E.upd]
  live z h := E.live _ (F.live z h)
  step h := F.step (E.step h)

end Silmaril.X86.SegVC.Isa.Extends
