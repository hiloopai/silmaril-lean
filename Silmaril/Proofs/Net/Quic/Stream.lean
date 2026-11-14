module

public import Silmaril.Net.Quic.Stream.Defs

/-!
# QUIC stream states: proofs

For `Silmaril.Net.Quic.Stream.Thms` (RFC 9000 §3.1, §3.2, §4.5). Case analyses over states
and events.
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Quic.Stream

open Silmaril.Net.Quic

/-! ## Sending part -/

theorem sendStep_terminal {s s' : SendStream} {e : SendEvent} (ht : s.state.terminal = true)
    (h : sendStep s e = some s') : s' = s := by
  obtain ⟨st, sent, fs, rc⟩ := s
  cases st <;> simp [SendState.terminal] at ht <;> cases e <;> simp_all [sendStep]

theorem sendStep_ok {s s' : SendStream} {e : SendEvent} (hs : s.Ok)
    (h : sendStep s e = some s') : s'.Ok := by
  obtain ⟨st, sent, fs, rc⟩ := s
  obtain ⟨h1, h2⟩ := hs
  cases e <;> cases st <;> simp only [sendStep, SendStream.doReset, reduceCtorEq,
    Option.some.injEq] at h <;> subst_vars <;> simp_all [SendStream.Ok]

theorem sendStep_finalSize {s s' : SendStream} {e : SendEvent} {n : Nat} (hs : s.Ok)
    (hn : s.finalSize = some n) (h : sendStep s e = some s') : s'.finalSize = some n := by
  obtain ⟨st, sent, fs, rc⟩ := s
  obtain ⟨h1, h2⟩ := hs
  simp only at hn h1 h2; subst hn
  cases e <;> cases st <;> simp only [sendStep, SendStream.doReset, reduceCtorEq,
    Option.some.injEq] at h <;> subst_vars <;> simp_all

theorem sendStep_no_data {s : SendStream} {n k : Nat} (hs : s.Ok)
    (hn : s.finalSize = some n) : sendStep s (.data k) = none ∧ sendStep s .blocked = none ∧
      sendStep s .fin = none := by
  obtain ⟨st, sent, fs, rc⟩ := s
  obtain ⟨h1, -⟩ := hs
  simp only at hn h1; subst hn
  cases st <;> simp_all [sendStep]

theorem sendStep_sent {s s' : SendStream} {e : SendEvent} (h : sendStep s e = some s') :
    s'.sent = s.sent + (match e with | .data n => n | _ => 0) := by
  obtain ⟨st, sent, fs, rc⟩ := s
  cases e <;> cases st <;> simp only [sendStep, SendStream.doReset, reduceCtorEq,
    Option.some.injEq] at h <;> subst_vars <;> rfl

theorem sendSteps_ok {s s' : SendStream} {es : List SendEvent} (hs : s.Ok)
    (h : sendSteps s es = some s') : s'.Ok := by
  induction es generalizing s with
  | nil => simp only [sendSteps, Option.some.injEq] at h; exact h ▸ hs
  | cons e es ih =>
    simp only [sendSteps, Option.bind_eq_some_iff] at h
    obtain ⟨t, ht, h⟩ := h
    exact ih (sendStep_ok hs ht) h

theorem sendSteps_finalSize {s s' : SendStream} {es : List SendEvent} {n : Nat} (hs : s.Ok)
    (hn : s.finalSize = some n) (h : sendSteps s es = some s') : s'.finalSize = some n := by
  induction es generalizing s with
  | nil => simp only [sendSteps, Option.some.injEq] at h; exact h ▸ hn
  | cons e es ih =>
    simp only [sendSteps, Option.bind_eq_some_iff] at h
    obtain ⟨t, ht, h⟩ := h
    exact ih (sendStep_ok hs ht) (sendStep_finalSize hs hn ht) h

/-! ## Receiving part -/

theorem recvStep_terminal {s s' : RecvStream} {e : RecvEvent} (ht : s.state.terminal = true)
    (h : recvStep s e = .ok s') : s'.state = s.state := by
  obtain ⟨st, hi, fs, rc⟩ := s
  cases st <;> simp [RecvState.terminal] at ht <;> cases e <;> cases fs <;>
    simp only [recvStep] at h <;> (repeat' split at h) <;>
    simp_all [RecvState.afterReset] <;> subst_vars <;> rfl

theorem recvStep_finalSize {s s' : RecvStream} {e : RecvEvent} {n : Nat}
    (hn : s.finalSize = some n) (h : recvStep s e = .ok s') : s'.finalSize = some n := by
  obtain ⟨st, hi, fs, rc⟩ := s
  simp only at hn; subst hn
  cases e <;> simp only [recvStep] at h <;> (repeat' split at h) <;> simp_all <;>
    subst_vars <;> first | rfl | simp_all

theorem recvStep_beyond {s : RecvStream} {n off len : Nat} (fin : Bool)
    (hn : s.finalSize = some n) (hb : n < off + len) :
    recvStep s (.stream off len fin) = .error .finalSizeError := by
  simp only [recvStep, hn, hb, ↓reduceIte]

theorem recvStep_fin_change {s : RecvStream} {n off len : Nat}
    (hn : s.finalSize = some n) (hb : off + len ≠ n) :
    recvStep s (.stream off len true) = .error .finalSizeError := by
  simp only [recvStep, hn]; split <;> simp_all

theorem recvStep_reset_change {s : RecvStream} {m n c : Nat}
    (hn : s.finalSize = some m) (hb : m ≠ n) :
    recvStep s (.resetStream c n) = .error .finalSizeError := by
  simp only [recvStep, hn, ne_eq, hb, not_false_eq_true, ↓reduceIte]

theorem recvStep_fin_lower {s : RecvStream} {off len : Nat} (hn : s.finalSize = none)
    (hb : off + len < s.highest) : recvStep s (.stream off len true) = .error .finalSizeError := by
  simp only [recvStep, hn, hb, ↓reduceIte]

theorem recvStep_reset_lower {s : RecvStream} {c n : Nat} (hn : s.finalSize = none)
    (hb : n < s.highest) : recvStep s (.resetStream c n) = .error .finalSizeError := by
  simp only [recvStep, hn, hb, ↓reduceIte]

theorem recvStep_ok {s s' : RecvStream} {e : RecvEvent} (hs : s.Ok)
    (h : recvStep s e = .ok s') : s'.Ok := by
  obtain ⟨st, hi, fs, rc⟩ := s
  obtain ⟨h1, h2⟩ := hs
  simp only at h1 h2
  cases e <;> cases fs <;> simp only [recvStep] at h <;> (repeat' split at h) <;>
    simp only [Except.ok.injEq, reduceCtorEq] at h <;> subst h <;>
    refine ⟨?_, fun k hk => ?_⟩ <;> dsimp only at * <;> (try cases st) <;>
    simp_all [RecvState.afterReset] <;> omega

theorem recvSteps_ok {s s' : RecvStream} {es : List RecvEvent} (hs : s.Ok)
    (h : recvSteps s es = .ok s') : s'.Ok := by
  induction es generalizing s with
  | nil => simp only [recvSteps, Except.ok.injEq] at h; exact h ▸ hs
  | cons e es ih =>
    simp only [recvSteps] at h
    cases ht : recvStep s e with
    | error _ => simp [ht, Except.bind] at h
    | ok t => simp only [ht, Except.bind] at h; exact ih (recvStep_ok hs ht) h

theorem recvSteps_finalSize {s s' : RecvStream} {es : List RecvEvent} {n : Nat}
    (hn : s.finalSize = some n) (h : recvSteps s es = .ok s') : s'.finalSize = some n := by
  induction es generalizing s with
  | nil => simp only [recvSteps, Except.ok.injEq] at h; exact h ▸ hn
  | cons e es ih =>
    simp only [recvSteps] at h
    cases ht : recvStep s e with
    | error _ => simp [ht, Except.bind] at h
    | ok t => simp only [ht, Except.bind] at h; exact ih (recvStep_finalSize hn ht) h

theorem recvSteps_terminal {s s' : RecvStream} {es : List RecvEvent}
    (ht : s.state.terminal = true) (h : recvSteps s es = .ok s') : s'.state = s.state := by
  induction es generalizing s with
  | nil => simp only [recvSteps, Except.ok.injEq] at h; exact h ▸ rfl
  | cons e es ih =>
    simp only [recvSteps] at h
    cases he : recvStep s e with
    | error _ => simp [he, Except.bind] at h
    | ok t =>
      simp only [he, Except.bind] at h
      have h1 := recvStep_terminal ht he
      rw [ih (h1 ▸ ht) h, h1]

end Silmaril.Proofs.Net.Quic.Stream
