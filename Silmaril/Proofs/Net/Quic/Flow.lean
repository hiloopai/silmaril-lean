module

public import Silmaril.Net.Quic.Flow.Defs

/-!
# QUIC flow control: proofs

For `Silmaril.Net.Quic.Flow.Thms` (RFC 9000 §4.1).
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Quic.Flow

open Silmaril.Net.Quic

theorem update_same {α : Type} (f : Nat → α) (i : Nat) (a : α) : update f i a i = a := by
  simp [update]

theorem update_other {α : Type} (f : Nat → α) {i j : Nat} (a : α) (h : j ≠ i) :
    update f i a j = f j := by
  simp [update, h]

theorem consume_spec {c c' : Credit} {n : Nat} :
    c.consume n = some c' ↔ c.used + n ≤ c.limit ∧ c' = { c with used := c.used + n } := by
  unfold Credit.consume; split
  · simp only [Option.some.injEq, eq_comm, true_and, *]
  · simp only [reduceCtorEq, false_iff, not_and]; intro h; omega

theorem send_spec {f f' : SendFlow} {id n : Nat} (h : f.send id n = some f') :
    f.conn.used + n ≤ f.conn.limit ∧ (f.streams id).used + n ≤ (f.streams id).limit ∧
      f'.conn = { f.conn with used := f.conn.used + n } ∧
      f'.streams = update f.streams id { f.streams id with used := (f.streams id).used + n } := by
  simp only [SendFlow.send, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨c, hc, s, hs, rfl⟩ := h
  obtain ⟨h1, rfl⟩ := consume_spec.1 hc
  obtain ⟨h2, rfl⟩ := consume_spec.1 hs
  exact ⟨h1, h2, rfl, rfl⟩

theorem send_ok {f f' : SendFlow} {id n : Nat} (hf : f.Ok) (h : f.send id n = some f') :
    f'.Ok := by
  obtain ⟨h1, h2, h3, h4⟩ := send_spec h
  refine ⟨by simp only [Credit.Ok, h3]; omega, fun j => ?_⟩
  rw [h4]; by_cases hj : j = id
  · subst hj; simp only [update_same, Credit.Ok]; omega
  · rw [update_other _ _ hj]; exact hf.2 j

theorem send_none {f : SendFlow} {id n : Nat} :
    f.send id n = none ↔
      f.conn.limit < f.conn.used + n ∨ (f.streams id).limit < (f.streams id).used + n := by
  cases h : f.send id n with
  | some f' => obtain ⟨h1, h2, -⟩ := send_spec h; simp only [reduceCtorEq, false_iff]; omega
  | none =>
    simp only [true_iff]
    refine Classical.byContradiction fun hc => ?_
    have h1 : f.conn.used + n ≤ f.conn.limit := by omega
    have h2 : (f.streams id).used + n ≤ (f.streams id).limit := by omega
    simp [SendFlow.send, Credit.consume, h1, h2] at h

theorem onData_spec {f f' : RecvFlow} {id e : Nat} (h : f.onData id e = .ok f') :
    e ≤ f.streamMax id ∧ f.received + (e - f.highest id) ≤ f.maxData ∧
      f' = { f with received := f.received + (e - f.highest id),
                    highest := update f.highest id (max (f.highest id) e) } := by
  unfold RecvFlow.onData at h
  split at h
  · cases h
  · dsimp only at h; split at h
    · cases h
    · simp only [Except.ok.injEq] at h; exact ⟨by omega, by omega, h.symm⟩

theorem onData_error {f : RecvFlow} {id e : Nat} :
    f.onData id e = .error .flowControlError ↔
      f.streamMax id < e ∨ f.maxData < f.received + (e - f.highest id) := by
  unfold RecvFlow.onData
  by_cases h1 : f.streamMax id < e <;> by_cases h2 : f.maxData < f.received + (e - f.highest id) <;>
    simp [h1, h2]

theorem onData_ok {f f' : RecvFlow} {id e : Nat} (hf : f.Ok) (h : f.onData id e = .ok f') :
    f'.Ok := by
  obtain ⟨h1, h2, rfl⟩ := onData_spec h
  refine ⟨h2, fun j => ?_⟩
  by_cases hj : j = id
  · subst hj; simp only [update_same]; have := hf.2 j; omega
  · simp only [update_other _ _ hj]; exact hf.2 j

theorem raiseMaxData_ok {f : RecvFlow} (hf : f.Ok) (m : Nat) : (f.raiseMaxData m).Ok :=
  ⟨by simp only [RecvFlow.raiseMaxData]; have := hf.1; omega, hf.2⟩

theorem raiseStreamMax_ok {f : RecvFlow} (hf : f.Ok) (id m : Nat) :
    (f.raiseStreamMax id m).Ok := by
  refine ⟨hf.1, fun j => ?_⟩
  simp only [RecvFlow.raiseStreamMax]
  by_cases hj : j = id
  · subst hj; simp only [update_same]; have := hf.2 j; omega
  · simp only [update_other _ _ hj]; exact hf.2 j

theorem sync_send {snd snd' : SendFlow} {rcv : RecvFlow} {id n : Nat} (hs : Sync snd rcv)
    (h : snd.send id n = some snd') :
    ∃ rcv', rcv.onData id ((snd.streams id).used + n) = .ok rcv' ∧ Sync snd' rcv' := by
  obtain ⟨h1, h2, h3, h4⟩ := send_spec h
  obtain ⟨hc, hl, hst⟩ := hs
  have hid := hst id
  refine ⟨{ rcv with
    received := rcv.received + ((snd.streams id).used + n - rcv.highest id),
    highest := update rcv.highest id (max (rcv.highest id) ((snd.streams id).used + n)) },
    ?_, ?_⟩
  · unfold RecvFlow.onData
    simp only [show ¬ rcv.streamMax id < (snd.streams id).used + n by omega,
      show ¬ rcv.maxData < rcv.received + ((snd.streams id).used + n - rcv.highest id) by omega,
      ↓reduceIte]
  · refine ⟨?_, ?_, fun j => ?_⟩
    · simp only [h3]; omega
    · simp only [h3]; omega
    · rw [h4]
      by_cases hj : j = id
      · subst hj; simp only [update_same]; omega
      · simp only [update_other _ _ hj]; exact hst j

theorem sync_onMaxData {snd : SendFlow} {rcv : RecvFlow} {m : Nat} (hs : Sync snd rcv)
    (hm : m ≤ rcv.maxData) : Sync (snd.onMaxData m) rcv := by
  obtain ⟨hc, hl, hst⟩ := hs
  exact ⟨hc, by simp only [SendFlow.onMaxData, Credit.onMax]; omega, hst⟩

theorem sync_onMaxStreamData {snd : SendFlow} {rcv : RecvFlow} {id m : Nat} (hs : Sync snd rcv)
    (hm : m ≤ rcv.streamMax id) : Sync (snd.onMaxStreamData id m) rcv := by
  obtain ⟨hc, hl, hst⟩ := hs
  refine ⟨hc, hl, fun j => ?_⟩
  simp only [SendFlow.onMaxStreamData]
  by_cases hj : j = id
  · subst hj; simp only [update_same, Credit.onMax]; have := hst j; omega
  · simp only [update_other _ _ hj]; exact hst j

theorem sync_raiseMaxData {snd : SendFlow} {rcv : RecvFlow} (hs : Sync snd rcv) (m : Nat) :
    Sync snd (rcv.raiseMaxData m) := by
  obtain ⟨hc, hl, hst⟩ := hs
  exact ⟨hc, by simp only [RecvFlow.raiseMaxData]; omega, hst⟩

theorem sync_raiseStreamMax {snd : SendFlow} {rcv : RecvFlow} (hs : Sync snd rcv) (id m : Nat) :
    Sync snd (rcv.raiseStreamMax id m) := by
  obtain ⟨hc, hl, hst⟩ := hs
  refine ⟨hc, hl, fun j => ⟨(hst j).1, ?_⟩⟩
  simp only [RecvFlow.raiseStreamMax]
  by_cases hj : j = id
  · subst hj; simp only [update_same]; have := hst j; omega
  · simp only [update_other _ _ hj]; exact (hst j).2

end Silmaril.Proofs.Net.Quic.Flow
