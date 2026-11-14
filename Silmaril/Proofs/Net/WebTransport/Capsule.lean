module

public import Silmaril.Net.WebTransport.Capsule.Defs
import Silmaril.Net.Quic.VarInt.Thms
import Silmaril.Net.Http3.Capsule.Thms

/-!
# WebTransport capsules: proofs

For `Silmaril.Net.WebTransport.Capsule.Thms` (draft-ietf-webtrans-http3-17 §4.7, §5.6, §6).
-/

@[expose] public section

namespace Silmaril.Proofs.Net.WebTransport.Capsule

open Silmaril.Net.Quic Silmaril.Net.Http3 Silmaril.Net.WebTransport

theorem toNat_toUInt8 (n : Nat) : n.toUInt8.toNat = n % 256 := by
  simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow]

theorem u32Read_u32Bytes {n : Nat} (h : n < 2 ^ 32) (rest : List UInt8) :
    u32Read (u32Bytes n ++ rest) = some (n, rest) := by
  simp only [u32Bytes, List.cons_append, List.nil_append, u32Read, toNat_toUInt8,
    Option.some.injEq, Prod.mk.injEq, and_true]
  omega

theorem u32Bytes_length (n : Nat) : (u32Bytes n).length = 4 := rfl

theorem u32Read_lt {xs : List UInt8} {n : Nat} {rest : List UInt8}
    (h : u32Read xs = some (n, rest)) : n < 2 ^ 32 := by
  match xs, h with
  | a :: b :: c :: d :: r, h =>
    simp only [u32Read, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have := a.toNat_lt; have := b.toNat_lt; have := c.toNat_lt; have := d.toNat_lt
    omega

theorem oneVarInt_encode {n : Nat} (h : VarInt.Valid n) : oneVarInt (VarInt.encode n) = some n := by
  have := VarInt.decode_encode h []
  rw [List.append_nil] at this
  simp only [oneVarInt, this]

theorem oneVarInt_valid {v : List UInt8} {n : Nat} (h : oneVarInt v = some n) : VarInt.Valid n := by
  unfold oneVarInt at h
  split at h
  · rename_i m hm; cases h; exact VarInt.decode_valid hm
  · cases h

theorem limit_valid {n : Nat} (h : n ≤ maxStreamsLimit) : VarInt.Valid n := by
  unfold maxStreamsLimit at h; unfold VarInt.Valid VarInt.maxValue; omega

theorem ofCapsule_toCapsule {w : WtCapsule} (h : w.Valid) :
    WtCapsule.ofCapsule w.toCapsule = .ok (some w) := by
  cases w with
  | datagram p => rfl
  | closeSession code msg =>
    obtain ⟨hc, hl, hu⟩ := h
    simp only [WtCapsule.ofCapsule, WtCapsule.toCapsule, u32Read_u32Bytes hc, hl, hu,
      decide_true, Bool.and_self, ↓reduceIte, Capsule.typeDatagram, typeCloseSession]
    rfl
  | drainSession => rfl
  | maxStreams d n =>
    have h' : ¬ maxStreamsLimit < n := Nat.not_lt.2 h
    cases d <;>
    simp [WtCapsule.ofCapsule, WtCapsule.toCapsule, WtCapsule.maxStreamsType,
      WtCapsule.streamCount, oneVarInt_encode (limit_valid h), h', Capsule.typeDatagram,
      typeCloseSession, typeDrainSession, typeMaxStreamsBidi, typeMaxStreamsUni]
  | streamsBlocked d n =>
    have h' : ¬ maxStreamsLimit < n := Nat.not_lt.2 h
    cases d <;>
    simp [WtCapsule.ofCapsule, WtCapsule.toCapsule, WtCapsule.streamsBlockedType,
      WtCapsule.streamCount, oneVarInt_encode (limit_valid h), h', Capsule.typeDatagram,
      typeCloseSession, typeDrainSession, typeMaxStreamsBidi, typeMaxStreamsUni,
      typeStreamsBlockedBidi, typeStreamsBlockedUni]
  | maxData n =>
    simp [WtCapsule.ofCapsule, WtCapsule.toCapsule, WtCapsule.dataCount, oneVarInt_encode h,
      Capsule.typeDatagram, typeCloseSession, typeDrainSession, typeMaxStreamsBidi,
      typeMaxStreamsUni, typeStreamsBlockedBidi, typeStreamsBlockedUni, typeMaxData]
  | dataBlocked n =>
    simp [WtCapsule.ofCapsule, WtCapsule.toCapsule, WtCapsule.dataCount, oneVarInt_encode h,
      Capsule.typeDatagram, typeCloseSession, typeDrainSession, typeMaxStreamsBidi,
      typeMaxStreamsUni, typeStreamsBlockedBidi, typeStreamsBlockedUni, typeMaxData,
      typeDataBlocked]

theorem streamCount_valid {v : List UInt8} {k : Nat → WtCapsule} {w : WtCapsule}
    (hk : ∀ n, n ≤ maxStreamsLimit → (k n).Valid)
    (h : WtCapsule.streamCount v k = .ok (some w)) : w.Valid := by
  unfold WtCapsule.streamCount at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i n _ hn
      simp only [Except.ok.injEq, Option.some.injEq] at h
      subst h; exact hk n (Nat.not_lt.1 hn)

theorem dataCount_valid {v : List UInt8} {k : Nat → WtCapsule} {w : WtCapsule}
    (hk : ∀ n, VarInt.Valid n → (k n).Valid)
    (h : WtCapsule.dataCount v k = .ok (some w)) : w.Valid := by
  unfold WtCapsule.dataCount at h
  split at h
  · cases h
  · rename_i n hn
    simp only [Except.ok.injEq, Option.some.injEq] at h
    subst h; exact hk n (oneVarInt_valid hn)

theorem ofCapsule_valid {c : Capsule} {w : WtCapsule} (hc : c.Valid)
    (h : WtCapsule.ofCapsule c = .ok (some w)) : w.Valid := by
  unfold WtCapsule.ofCapsule at h
  split at h
  · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h; exact hc.2
  split at h
  · split at h
    · cases h
    · rename_i code msg hr
      split at h
      · rename_i hm
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
        simp only [Except.ok.injEq, Option.some.injEq] at h
        subst h
        exact ⟨u32Read_lt hr, hm.1, hm.2⟩
      · cases h
  split at h
  · split at h
    · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h; trivial
    · cases h
  split at h
  · refine streamCount_valid ?_ h; intro n hn; exact hn
  split at h
  · refine streamCount_valid ?_ h; intro n hn; exact hn
  split at h
  · refine streamCount_valid ?_ h; intro n hn; exact hn
  split at h
  · refine streamCount_valid ?_ h; intro n hn; exact hn
  split at h
  · refine dataCount_valid ?_ h; intro n hn; exact hn
  split at h
  · refine dataCount_valid ?_ h; intro n hn; exact hn
  split at h
  · cases h
  · cases h

theorem ofCapsule_unknown {c : Capsule} (h : c.type ∉ knownCapsuleTypes) :
    WtCapsule.ofCapsule c = .ok none := by
  simp only [knownCapsuleTypes, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  simp [WtCapsule.ofCapsule, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

theorem toCapsule_type_valid (w : WtCapsule) : VarInt.Valid w.toCapsule.type := by
  unfold VarInt.Valid VarInt.maxValue
  cases w with
  | maxStreams d n => cases d <;> simp only [WtCapsule.toCapsule, WtCapsule.maxStreamsType] <;> decide
  | streamsBlocked d n =>
    cases d <;> simp only [WtCapsule.toCapsule, WtCapsule.streamsBlockedType] <;> decide
  | _ => simp only [WtCapsule.toCapsule] <;> decide

theorem toCapsule_valid {w : WtCapsule} (h : w.Valid) : w.toCapsule.Valid := by
  have e8 (n : Nat) : (VarInt.encode n).length ≤ 8 := by
    rw [VarInt.encode_length]; have := VarInt.lenOf_mem n
    simp only [VarInt.lengths, List.mem_cons, List.not_mem_nil, or_false] at this; omega
  refine ⟨toCapsule_type_valid w, ?_⟩
  unfold VarInt.Valid VarInt.maxValue
  cases w with
  | datagram p => exact h
  | closeSession code msg =>
    obtain ⟨-, hl, -⟩ := h
    unfold maxCloseMessage at hl
    simp only [WtCapsule.toCapsule, List.length_append, u32Bytes_length]
    omega
  | drainSession => decide
  | maxStreams d n => have := e8 n; cases d <;> simp [WtCapsule.toCapsule] <;> omega
  | streamsBlocked d n => have := e8 n; cases d <;> simp [WtCapsule.toCapsule] <;> omega
  | maxData n => have := e8 n; simp [WtCapsule.toCapsule]; omega
  | dataBlocked n => have := e8 n; simp [WtCapsule.toCapsule]; omega

theorem decode_encode {m : Nat} {w : WtCapsule} (h : w.Valid)
    (hm : w.toCapsule.value.length ≤ m) (rest : List UInt8) :
    WtCapsule.decode m (w.encode ++ rest) = .ok (some w, rest) := by
  simp only [WtCapsule.decode, WtCapsule.encode,
    Capsule.read_encode (toCapsule_valid h) hm rest, ofCapsule_toCapsule h]

end Silmaril.Proofs.Net.WebTransport.Capsule
