module

public import Silmaril.Net.WebTransport.Session.Defs

/-!
# WebTransport session state machine: proofs

For `Silmaril.Net.WebTransport.Session.Thms` (draft-ietf-webtrans-http3-17 §3.2, §4.7, §6).
Every proof is a case analysis over states and events.
-/

@[expose] public section

namespace Silmaril.Proofs.Net.WebTransport.Session

open Silmaril.Net.WebTransport SessionState

theorem step_closed (r : CloseReason) (e : SessionEvent) : (step (.closed r) e).1 = .closed r := by
  cases e <;> rfl

theorem run_cons_fst (s : SessionState) (e : SessionEvent) (es : List SessionEvent) :
    (run s (e :: es)).1 = (run (step s e).1 es).1 := by
  cases h : step s e
  simp only [run, h]

theorem run_closed (r : CloseReason) (es : List SessionEvent) :
    (run (.closed r) es).1 = .closed r := by
  induction es with
  | nil => rfl
  | cons e es ih => rw [run_cons_fst, step_closed, ih]

theorem rank_step (s : SessionState) (e : SessionEvent) : s.rank ≤ (step s e).1.rank := by
  cases s <;> cases e <;> simp only [step, rank] <;> (try split) <;> simp

theorem rank_run (s : SessionState) (es : List SessionEvent) : s.rank ≤ (run s es).1.rank := by
  induction es generalizing s with
  | nil => exact Nat.le_refl _
  | cons e es ih =>
    rw [run_cons_fst]
    exact Nat.le_trans (rank_step s e) (ih (step s e).1)

theorem step_terminates (s : SessionState) (e : SessionEvent) (hs : s.isClosed = false)
    (h : (step s e).1.isClosed = true) : Action.resetStreams .sessionGone ∈ (step s e).2 := by
  cases s with
  | closed r => cases hs
  | establishing =>
    cases e <;> simp only [step, isClosed, terminate] at h ⊢ <;> (try split at h) <;>
      (try split) <;> simp_all
  | established => cases e <;> simp_all [step, isClosed, terminate]
  | draining => cases e <;> simp_all [step, isClosed, terminate]

theorem step_finReceived (s : SessionState) :
    step s .finReceived = step s (.closeReceived 0 []) := by
  cases s <;> rfl

theorem step_closeSent_fin (s : SessionState) (hs : s.isClosed = false) (code : Nat)
    (msg : List UInt8) :
    (step s (.closeSent code msg)).1 = .closed (.closed code msg) ∧
      Action.finConnect ∈ (step s (.closeSent code msg)).2 := by
  cases s <;> simp_all [step, isClosed]

end Silmaril.Proofs.Net.WebTransport.Session
