module

public import Silmaril.Net.WebTransport.Flow.Defs

/-!
# WebTransport session flow control: proofs

For `Silmaril.Net.WebTransport.Flow.Thms` (draft-ietf-webtrans-http3-17 §5.3–§5.6). Every proof
is a case split on the direction and linear arithmetic.
-/

@[expose] public section

namespace Silmaril.Proofs.Net.WebTransport.Flow

open Silmaril.Net.WebTransport

theorem le_refl (l : Limits) : l.Le l := ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem onCapsule_mono {s s' : SendState} {c : WtCapsule} (h : s.onCapsule c = .ok s') :
    s.limits.Le s'.limits ∧ s'.used = s.used := by
  cases c with
  | maxStreams d n =>
    simp only [SendState.onCapsule, Bool.or_eq_true, decide_eq_true_eq] at h
    split at h
    · cases h
    · rename_i hn
      simp only [Except.ok.injEq] at h
      subst h
      cases d <;> simp_all [Limits.streams, Limits.setStreams, Limits.Le] <;> omega
  | maxData n =>
    simp only [SendState.onCapsule] at h
    split at h
    · cases h
    · rename_i hn
      simp only [Except.ok.injEq] at h
      subst h
      exact ⟨⟨Nat.le_refl _, Nat.le_refl _, by simp only; omega⟩, rfl⟩
  | _ => simp only [SendState.onCapsule, Except.ok.injEq] at h; subst h; exact ⟨le_refl _, rfl⟩

theorem within_mono {u : Usage} {a b : Limits} (hu : u.Within a) (h : a.Le b) : u.Within b := by
  obtain ⟨h1, h2, h3⟩ := hu; obtain ⟨g1, g2, g3⟩ := h
  exact ⟨Nat.le_trans h1 g1, Nat.le_trans h2 g2, Nat.le_trans h3 g3⟩

theorem onCapsule_within {s s' : SendState} {c : WtCapsule} (hs : s.used.Within s.limits)
    (h : s.onCapsule c = .ok s') : s'.used.Within s'.limits := by
  obtain ⟨hl, hu⟩ := onCapsule_mono h
  rw [hu]; exact within_mono hs hl

theorem tryOpen_within {s s' : SendState} {d : Dir} (hs : s.used.Within s.limits)
    (h : s.tryOpen d = some s') : s'.used.Within s'.limits := by
  unfold SendState.tryOpen at h
  split at h
  · rename_i hlt
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨h1, h2, h3⟩ := hs
    cases d <;> simp_all [Usage.opened, Usage.openOne, Limits.streams, Usage.Within] <;> omega
  · cases h

theorem trySend_within {s s' : SendState} {n : Nat} (hs : s.used.Within s.limits)
    (h : s.trySend n = some s') : s'.used.Within s'.limits := by
  unfold SendState.trySend at h
  split at h
  · rename_i hle
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨h1, h2, h3⟩ := hs
    exact ⟨h1, h2, hle⟩
  · cases h

theorem onOpen_of_tryOpen {s s' : SendState} {r : RecvState} {d : Dir}
    (h : s.tryOpen d = some s') (hl : s.limits.Le r.limits) (hu : s.used = r.used) :
    ∃ r', r.onOpen d = .ok r' ∧ r'.used = s'.used ∧ r'.limits = r.limits := by
  unfold SendState.tryOpen at h
  split at h
  · rename_i hlt
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨g1, g2, -⟩ := hl
    have : ¬ r.limits.streams d < r.used.opened d + 1 := by
      rw [← hu]; cases d <;> simp_all [Limits.streams, Usage.opened] <;> omega
    exact ⟨{ r with used := r.used.openOne d }, by simp only [RecvState.onOpen, this, ↓reduceIte],
      by simp [hu], rfl⟩
  · cases h

theorem onData_of_trySend {s s' : SendState} {r : RecvState} {n : Nat}
    (h : s.trySend n = some s') (hl : s.limits.Le r.limits) (hu : s.used = r.used) :
    ∃ r', r.onData n = .ok r' ∧ r'.used = s'.used ∧ r'.limits = r.limits := by
  unfold SendState.trySend at h
  split at h
  · rename_i hle
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨-, -, g3⟩ := hl
    have : ¬ r.limits.maxData < r.used.dataBytes + n := by rw [← hu]; omega
    exact ⟨{ r with used := r.used.addData n }, by simp only [RecvState.onData, this, ↓reduceIte],
      by simp [hu], rfl⟩
  · cases h

theorem onOpen_exceed {r : RecvState} {d : Dir} (h : r.limits.streams d ≤ r.used.opened d) :
    r.onOpen d = .error .flowControlError := by
  simp only [RecvState.onOpen, show r.limits.streams d < r.used.opened d + 1 by omega, ↓reduceIte]

theorem onData_exceed {r : RecvState} {n : Nat} (h : r.limits.maxData < r.used.dataBytes + n) :
    r.onData n = .error .flowControlError := by
  simp only [RecvState.onData, h, ↓reduceIte]

theorem onCapsule_of_raiseStreams {s : SendState} {r r' : RecvState} {d : Dir} {n : Nat}
    {c : WtCapsule} (h : r.raiseStreams d n = some (r', c)) (hl : s.limits.Le r.limits) :
    ∃ s', s.onCapsule c = .ok s' ∧ s'.used = s.used ∧ s'.limits.Le r'.limits := by
  unfold RecvState.raiseStreams at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨g1, g2, g3⟩ := hl
    have h1 : s.limits.streams d < n := by
      cases d <;> simp only [Limits.streams] at hc ⊢ <;> omega
    have hs : (decide (maxStreamsLimit < n) || decide (n ≤ s.limits.streams d)) = false := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
    refine ⟨{ s with limits := s.limits.setStreams d n },
      by simp only [SendState.onCapsule, hs, Bool.false_eq_true, ↓reduceIte], rfl, ?_⟩
    cases d <;> simp only [Limits.streams, Limits.setStreams, Limits.Le] at hc ⊢ <;> omega
  · cases h

theorem onCapsule_of_raiseData {s : SendState} {r r' : RecvState} {n : Nat}
    {c : WtCapsule} (h : r.raiseData n = some (r', c)) (hl : s.limits.Le r.limits) :
    ∃ s', s.onCapsule c = .ok s' ∧ s'.used = s.used ∧ s'.limits.Le r'.limits := by
  unfold RecvState.raiseData at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨g1, g2, g3⟩ := hl
    have hs : ¬ n ≤ s.limits.maxData := by omega
    refine ⟨{ s with limits := { s.limits with maxData := n } },
      by simp only [SendState.onCapsule, hs, ↓reduceIte], rfl, ?_⟩
    simp only [Limits.Le]; omega
  · cases h

theorem le_antisymm' {a b : Limits} (h1 : a.Le b) (h2 : b.Le a) : a = b := by
  obtain ⟨_, _, _⟩ := a; obtain ⟨_, _, _⟩ := b
  simp only [Limits.Le] at h1 h2
  simp only [Limits.mk.injEq]; omega

theorem raiseStreams_mono {r r' : RecvState} {d : Dir} {n : Nat} {c : WtCapsule}
    (h : r.raiseStreams d n = some (r', c)) : r.limits.Le r'.limits ∧ r'.used = r.used := by
  unfold RecvState.raiseStreams at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases d <;> simp_all [Limits.setStreams, Limits.Le, Limits.streams] <;> omega
  · cases h

theorem raiseData_mono {r r' : RecvState} {n : Nat} {c : WtCapsule}
    (h : r.raiseData n = some (r', c)) : r.limits.Le r'.limits ∧ r'.used = r.used := by
  unfold RecvState.raiseData at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨Nat.le_refl _, Nat.le_refl _, by simp only; omega⟩, rfl⟩
  · cases h

theorem step_inv {S : System} (hS : S.Inv) (e : Event) :
    ∃ S', S.step e = .ok S' ∧ S'.Inv := by
  obtain ⟨hl, hu, hw⟩ := hS
  have hle : S.send.limits.Le S.recv.limits := hl ▸ le_refl _
  cases e with
  | open_ d =>
    cases ho : S.send.tryOpen d with
    | none => exact ⟨S, by simp only [System.step, ho], hl, hu, hw⟩
    | some s' =>
      obtain ⟨r', hr, hru, hrl⟩ := onOpen_of_tryOpen ho hle hu
      have hsl : s'.limits = S.send.limits := by
        unfold SendState.tryOpen at ho
        split at ho
        · cases ho; rfl
        · cases ho
      refine ⟨⟨s', r'⟩, by simp [System.step, ho, hr, Except.map], ?_, hru.symm,
        tryOpen_within hw ho⟩
      simp only [hsl, hrl, hl]
  | data n =>
    cases ho : S.send.trySend n with
    | none => exact ⟨S, by simp only [System.step, ho], hl, hu, hw⟩
    | some s' =>
      obtain ⟨r', hr, hru, hrl⟩ := onData_of_trySend ho hle hu
      have hsl : s'.limits = S.send.limits := by
        unfold SendState.trySend at ho
        split at ho
        · cases ho; rfl
        · cases ho
      refine ⟨⟨s', r'⟩, by simp [System.step, ho, hr, Except.map], ?_, hru.symm,
        trySend_within hw ho⟩
      simp only [hsl, hrl, hl]
  | raiseStreams d n =>
    cases hr : S.recv.raiseStreams d n with
    | none => exact ⟨S, by simp only [System.step, hr], hl, hu, hw⟩
    | some rc =>
      obtain ⟨r', c⟩ := rc
      obtain ⟨s', hs, hsu, hsl⟩ := onCapsule_of_raiseStreams hr hle
      obtain ⟨hrm, hru⟩ := raiseStreams_mono hr
      obtain ⟨hsm, -⟩ := onCapsule_mono hs
      have hll : s'.limits = r'.limits := by
        -- the sender's new limits are the receiver's: both moved to `n`
        unfold RecvState.raiseStreams at hr
        split at hr
        · simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          simp only [SendState.onCapsule] at hs
          split at hs
          · cases hs
          · simp only [Except.ok.injEq] at hs; subst hs; simp [hl]
        · cases hr
      refine ⟨⟨s', r'⟩, by simp [System.step, hr, hs, Except.map], hll, by simp [hsu, hru, hu],
        onCapsule_within hw hs⟩
  | raiseData n =>
    cases hr : S.recv.raiseData n with
    | none => exact ⟨S, by simp only [System.step, hr], hl, hu, hw⟩
    | some rc =>
      obtain ⟨r', c⟩ := rc
      obtain ⟨s', hs, hsu, hsl⟩ := onCapsule_of_raiseData hr hle
      obtain ⟨hrm, hru⟩ := raiseData_mono hr
      have hll : s'.limits = r'.limits := by
        unfold RecvState.raiseData at hr
        split at hr
        · simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          simp only [SendState.onCapsule] at hs
          split at hs
          · cases hs
          · simp only [Except.ok.injEq] at hs; subst hs; simp [hl]
        · cases hr
      refine ⟨⟨s', r'⟩, by simp [System.step, hr, hs, Except.map], hll, by simp [hsu, hru, hu],
        onCapsule_within hw hs⟩

theorem run_inv {S : System} (hS : S.Inv) (es : List Event) :
    ∃ S', S.run es = .ok S' ∧ S'.Inv := by
  induction es generalizing S with
  | nil => exact ⟨S, rfl, hS⟩
  | cons e es ih =>
    obtain ⟨S1, h1, hS1⟩ := step_inv hS e
    obtain ⟨S2, h2, hS2⟩ := ih hS1
    exact ⟨S2, by simp only [System.run, h1, h2], hS2⟩

theorem init_inv (w : WtSettings) : (System.init w).Inv :=
  ⟨rfl, rfl, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

end Silmaril.Proofs.Net.WebTransport.Flow
