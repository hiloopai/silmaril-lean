module

public import Silmaril.Net.Quic.StreamId.Defs

/-!
# QUIC stream identifiers: proofs

For `Silmaril.Net.Quic.StreamId.Thms` (RFC 9000 §2.1, §4.6). Everything reduces to
arithmetic on `4 n + bits` with `bits < 4`.
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Quic.StreamId

open Silmaril.Net.Quic Silmaril.Net.Quic.StreamId

theorem bits_lt (t : StreamType) : t.bits < 4 := by
  obtain ⟨i, d⟩ := t; cases i <;> cases d <;> decide

theorem bits_inj {t t' : StreamType} (h : t.bits = t'.bits) : t = t' := by
  obtain ⟨i, d⟩ := t; obtain ⟨i', d'⟩ := t'
  cases i <;> cases d <;> cases i' <;> cases d' <;> simp_all [StreamType.bits]

theorem index_nth (t : StreamType) (n : Nat) : index (nth t n) = n := by
  have := bits_lt t; simp only [index, nth]; omega

theorem type_bits (id : Nat) : (type id).bits = id % 4 := by
  simp only [type, initiator, dir, StreamType.bits]
  by_cases h1 : id % 2 = 0 <;> by_cases h2 : id / 2 % 2 = 0 <;> simp only [h1, h2, ↓reduceIte] <;>
    omega

theorem type_nth (t : StreamType) (n : Nat) : type (nth t n) = t := by
  have := bits_lt t
  apply bits_inj; rw [type_bits]; simp only [nth]; omega

theorem nth_type_index (id : Nat) : nth (type id) (index id) = id := by
  simp only [nth, index, type_bits]; omega

theorem nth_inj {t t' : StreamType} {n n' : Nat} (h : nth t n = nth t' n') : t = t' ∧ n = n' := by
  have h1 := type_nth t n; have h2 := index_nth t n
  rw [h] at h1 h2; rw [type_nth] at h1; rw [index_nth] at h2
  exact ⟨h1.symm, h2.symm⟩

theorem nth_lt_nth (t : StreamType) (n m : Nat) : nth t n < nth t m ↔ n < m := by
  simp only [nth]; omega

theorem nth_valid (t : StreamType) (n : Nat) : Valid (nth t n) ↔ n < maxStreamsLimit := by
  have := bits_lt t
  simp only [Valid, nth, VarInt.maxValue, maxStreamsLimit, Nat.reducePow]; omega

theorem withinLimit_iff (m id : Nat) : withinLimit m id = true ↔ index id < m := by
  simp only [withinLimit, type_bits, index, decide_eq_true_eq]; omega

theorem canSend_peer (r : Role) (id : Nat) : canSend r.peer id = canRecv r id := by
  cases r <;> simp only [canSend, canRecv, Role.peer] <;>
    cases initiator id <;> cases dir id <;> rfl

theorem uni_exclusive (r : Role) (id : Nat) (h : dir id = .uni) :
    canSend r id = !canRecv r id := by
  cases r <;> simp only [canSend, canRecv, h] <;> cases initiator id <;> rfl

theorem open_spec {o o' : Opener} {id : Nat} (h : o.open = some (id, o')) :
    id = nth o.type o.opened ∧ o'.opened = o.opened + 1 ∧ o'.type = o.type ∧
      o'.limit = o.limit ∧ o.opened < o.limit := by
  unfold Opener.open at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl, rfl, rfl, by assumption⟩
  · cases h

theorem open_ok {o o' : Opener} {id : Nat} (h : o.open = some (id, o')) : o'.Ok := by
  obtain ⟨-, h1, -, h2, h3⟩ := open_spec h; simp only [Opener.Ok, h1, h2]; omega

theorem open_valid {o o' : Opener} {id : Nat} (hl : o.limit ≤ maxStreamsLimit)
    (h : o.open = some (id, o')) : Valid id := by
  obtain ⟨rfl, -, -, -, h3⟩ := open_spec h; exact (nth_valid _ _).2 (by omega)

theorem onMaxStreams_ok {o o' : Opener} {m : Nat} (ho : o.Ok) (h : o.onMaxStreams m = .ok o') :
    o'.Ok ∧ o.limit ≤ o'.limit ∧ o'.limit ≤ max o.limit maxStreamsLimit ∧ o'.opened = o.opened := by
  unfold Opener.onMaxStreams at h
  split at h
  · cases h
  · simp only [Except.ok.injEq] at h; subst h
    unfold Opener.Ok at *; dsimp only; omega

theorem accept_spec {a a' : Acceptor} {id : Nat} (h : a.accept id = .ok a') :
    index id < a.limit ∧ a'.opened = max a.opened (index id + 1) ∧ a'.limit = a.limit ∧
      a'.type = a.type := by
  unfold Acceptor.accept at h
  split at h
  · cases h
  · simp only [Except.ok.injEq] at h; subst h; exact ⟨by omega, rfl, rfl, rfl⟩

theorem accept_error {a : Acceptor} {id : Nat} :
    a.accept id = .error .streamLimitError ↔ a.limit ≤ index id := by
  unfold Acceptor.accept; split <;> simp_all

theorem accept_ok {a a' : Acceptor} {id : Nat} (ha : a.Ok) (h : a.accept id = .ok a') :
    a'.Ok ∧ a'.isOpen id = true ∧ (∀ j, a.isOpen j = true → a'.isOpen j = true) := by
  obtain ⟨h1, h2, h3, -⟩ := accept_spec h
  simp only [Acceptor.Ok, Acceptor.isOpen, decide_eq_true_eq, h2, h3] at *
  refine ⟨by omega, by omega, fun j hj => by omega⟩

theorem accept_lower {a a' : Acceptor} {id j : Nat} (h : a.accept id = .ok a')
    (hj : index j ≤ index id) : a'.isOpen j = true := by
  obtain ⟨-, h2, -, -⟩ := accept_spec h
  simp only [Acceptor.isOpen, decide_eq_true_eq, h2]; omega

end Silmaril.Proofs.Net.Quic.StreamId
