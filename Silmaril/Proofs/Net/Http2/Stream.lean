module

public import Silmaril.Net.Http2.Stream.Defs

/-!
# HTTP/2 stream states: proofs

For `Silmaril.Net.Http2.Stream.Thms` (RFC 9113 §5.1). Every proof is a finite case analysis
over states, frames and END_STREAM flags.
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Http2

open Silmaril.Net.Http2

theorem step_closed {e : Event} {s : StreamState} (h : step .closed e = .ok s) : s = .closed := by
  obtain ⟨d, g⟩ := e
  cases d <;> cases g <;> simp_all [step]

theorem step_send_dual {s s' : StreamState} {g : Signal} (h : step s ⟨.send, g⟩ = .ok s') :
    step s.dual ⟨.recv, g⟩ = .ok s'.dual := by
  cases s <;> cases g <;> (try rename_i es; cases es) <;>
    simp_all [step, StreamState.dual] <;> subst_vars <;> rfl

theorem step_recv_dual {s s' : StreamState} {g : Signal} (h : step s ⟨.recv, g⟩ = .ok s') :
    step s.dual ⟨.send, g⟩ = .ok s'.dual ∨ s = .closed := by
  cases s <;> cases g <;> (try rename_i es; cases es) <;>
    simp_all [step, StreamState.dual] <;> subst_vars <;> simp

theorem step_rank {s s' : StreamState} {e : Event} (h : step s e = .ok s') : s.rank ≤ s'.rank := by
  obtain ⟨d, g⟩ := e
  cases s <;> cases d <;> cases g <;> (try rename_i es; cases es) <;>
    simp_all [step, StreamState.rank] <;> subst_vars <;> simp

theorem run_rank {s s' : StreamState} {es : List Event} (h : run s es = .ok s') :
    s.rank ≤ s'.rank := by
  induction es generalizing s with
  | nil => simp only [run, Except.ok.injEq] at h; subst h; exact Nat.le_refl _
  | cons e es ih =>
    simp only [run] at h
    split at h
    · next s₁ h₁ => exact Nat.le_trans (step_rank h₁) (ih h)
    · cases h

theorem step_rst {s : StreamState} {d : Dir} (hi : s ≠ .idle) (hc : d = .send → s ≠ .closed) :
    step s ⟨d, .rstStream⟩ = .ok .closed := by
  cases s <;> cases d <;> simp_all [step]

theorem step_recv_data {s s' : StreamState} {es : Bool} (h : step s ⟨.recv, .data es⟩ = .ok s') :
    s = .open ∨ s = .halfClosedLocal ∨ s = .closed := by
  cases s <;> cases es <;> simp_all [step]

theorem step_send_data {s s' : StreamState} {es : Bool} (h : step s ⟨.send, .data es⟩ = .ok s') :
    s = .open ∨ s = .halfClosedRemote := by
  cases s <;> cases es <;> simp_all [step]

end Silmaril.Proofs.Net.Http2
