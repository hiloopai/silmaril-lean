module

public import Silmaril.Net.Quic.Frame.Defs
import Silmaril.Net.Quic.VarInt.Thms

/-!
# QUIC frames: proofs

For `Silmaril.Net.Quic.Frame.Thms` (RFC 9000 §12.4, §19; RFC 9221 §4). The round trips are
field-by-field rewrites with `VarInt.decode_encode`.
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Quic.Frame

open Silmaril.Net.Quic Silmaril.Net.Quic.Frame

theorem dvi {v : Nat} (h : VarInt.Valid v) (rest : List UInt8) :
    VarInt.decode (vi v ++ rest) = some (v, rest) :=
  VarInt.decode_encode h rest

theorem takeN_append (bs rest : List UInt8) : takeN bs.length (bs ++ rest) = some (bs, rest) := by
  simp [takeN]

theorem decodeWithLen_append {bs : List UInt8} (h : VarInt.Valid bs.length) (rest : List UInt8) :
    decodeWithLen (withLen bs ++ rest) = some (bs, rest) := by
  simp only [decodeWithLen, withLen, List.append_assoc, dvi h, takeN_append, Option.bind_eq_bind,
    Option.bind_some]

@[simp] theorem allVarInt_nil : AllVarInt [] := by simp [AllVarInt]

@[simp] theorem allVarInt_cons {v : Nat} {vs : List Nat} :
    AllVarInt (v :: vs) ↔ VarInt.Valid v ∧ AllVarInt vs := by
  simp [AllVarInt]

@[simp] theorem allVarInt_append {vs ws : List Nat} :
    AllVarInt (vs ++ ws) ↔ AllVarInt vs ∧ AllVarInt ws := by
  simp only [AllVarInt, List.mem_append]
  exact ⟨fun h => ⟨fun v hv => h v (.inl hv), fun v hv => h v (.inr hv)⟩,
    fun h v hv => hv.elim (h.1 v) (h.2 v)⟩

theorem decodeRanges_append (rs : List AckRange)
    (h : AllVarInt (rs.flatMap fun r => [r.gap, r.len])) (rest : List UInt8) :
    decodeRanges rs.length (rs.flatMap (fun r => vi r.gap ++ vi r.len) ++ rest) =
      some (rs, rest) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.flatMap_cons, allVarInt_append, allVarInt_cons, allVarInt_nil, and_true]
      at h
    simp only [List.length_cons, List.flatMap_cons, decodeRanges, List.append_assoc, dvi h.1.1,
      dvi h.1.2, ih h.2, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

theorem type_lt (f : Frame) : f.type < 64 := by
  cases f <;> simp only [type, streamType] <;> (repeat' split) <;> omega

theorem toNat_toUInt8 (n : Nat) : n.toUInt8.toNat = n % 256 := by
  simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow]

/-- The fields of a valid frame are read back by the decoder for its type. -/
theorem decodeBody_body (f : Frame) (hv : f.Valid) (rest : List UInt8)
    (hr : f.toEnd = true → rest = []) : decodeBody f.type (f.body ++ rest) = some (f, rest) := by
  cases f with
  | padding | ping | handshakeDone => rfl
  | ack l d fr rs ecn =>
    obtain ⟨h1, h2⟩ := hv
    simp only [allVarInt_append, allVarInt_cons, allVarInt_nil, and_true] at h1
    obtain ⟨⟨⟨hl, hd, hf, hn⟩, hrs⟩, he⟩ := h1
    cases ecn with
    | none =>
      simp only [type, body, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, decodeBody,
        decodeAck, List.append_assoc, dvi hl, dvi hd, dvi hn, dvi hf, decodeRanges_append rs hrs,
        List.nil_append, h2, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    | some e =>
      simp only [allVarInt_cons, allVarInt_nil, and_true] at he
      simp only [type, body, Option.isSome_some, ↓reduceIte, decodeBody, decodeAck,
        List.append_assoc, dvi hl, dvi hd, dvi hn, dvi hf, decodeRanges_append rs hrs, dvi he.1,
        dvi he.2.1, dvi he.2.2, h2, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  | resetStream i e s =>
    simp only [Valid, allVarInt_cons, allVarInt_nil, and_true] at hv
    simp only [type, body, decodeBody, List.append_assoc, dvi hv.1, dvi hv.2.1, dvi hv.2.2,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  | stopSending i e =>
    simp only [Valid, allVarInt_cons, allVarInt_nil, and_true] at hv
    simp only [type, body, decodeBody, List.append_assoc, dvi hv.1, dvi hv.2,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  | crypto o d =>
    simp only [Valid] at hv
    have ho : VarInt.Valid o := by unfold VarInt.Valid; omega
    have hd : VarInt.Valid d.length := by unfold VarInt.Valid; omega
    simp only [type, body, decodeBody, List.append_assoc, dvi ho, decodeWithLen_append hd, hv,
      ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  | newToken t =>
    obtain ⟨h1, h2⟩ := hv
    simp only [type, body, decodeBody, decodeWithLen_append h2, h1, ↓reduceIte,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  | stream i off len fin d =>
    obtain ⟨hi, hod⟩ := hv
    have hd : VarInt.Valid d.length := by unfold VarInt.Valid; omega
    cases off with
    | none =>
      simp only [Option.getD_none, Nat.zero_add] at hod
      cases len <;> cases fin <;>
        simp_all [type, body, streamType, decodeBody, decodeStream, List.append_assoc, dvi hi,
          decodeWithLen_append hd, toEnd]
    | some o =>
      simp only [Option.getD_some] at hod
      have ho : VarInt.Valid o := by unfold VarInt.Valid; omega
      cases len <;> cases fin <;>
        simp_all [type, body, streamType, decodeBody, decodeStream, List.append_assoc, dvi hi,
          dvi ho, decodeWithLen_append hd, toEnd]
  | maxData m | dataBlocked m | retireConnectionId m =>
    simp only [type, body, decodeBody, dvi hv, Option.map_some]
  | maxStreamData i m | streamDataBlocked i m =>
    simp only [Valid, allVarInt_cons, allVarInt_nil, and_true] at hv
    simp only [type, body, decodeBody, List.append_assoc, dvi hv.1, dvi hv.2,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  | maxStreams dir m | streamsBlocked dir m =>
    simp only [Valid] at hv
    have hm : VarInt.Valid m := by
      unfold VarInt.Valid VarInt.maxValue; unfold maxStreamsLimit at hv; omega
    cases dir <;> simp only [type, body, decodeBody, dvi hm, hv, ↓reduceIte, reduceCtorEq,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  | newConnectionId s r c t =>
    obtain ⟨hs, hrs, hc1, hc2, ht⟩ := hv
    have hr' : VarInt.Valid r := by unfold VarInt.Valid at *; omega
    have hn : (c.length.toUInt8).toNat = c.length := by rw [toNat_toUInt8]; omega
    have h1 : takeN 1 ([c.length.toUInt8] ++ (c ++ (t ++ rest))) =
        some ([c.length.toUInt8], c ++ (t ++ rest)) := takeN_append [_] _
    have h16 : takeN 16 (t ++ rest) = some (t, rest) := ht ▸ takeN_append t rest
    simp only [type, body, decodeBody, List.append_assoc, dvi hs, dvi hr', h1, List.headD_cons,
      hn, takeN_append, h16, hrs, hc1, hc2, and_self, ↓reduceIte, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]
  | pathChallenge d | pathResponse d =>
    simp only [Valid] at hv
    have h8 : takeN 8 (d ++ rest) = some (d, rest) := hv ▸ takeN_append d rest
    simp only [type, body, decodeBody, h8, Option.map_some]
  | connectionClose e t r =>
    simp only [Valid, allVarInt_cons, allVarInt_nil, and_true] at hv
    simp only [type, body, decodeBody, List.append_assoc, dvi hv.1, dvi hv.2.1,
      decodeWithLen_append hv.2.2, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  | applicationClose e r =>
    simp only [Valid, allVarInt_cons, allVarInt_nil, and_true] at hv
    simp only [type, body, decodeBody, List.append_assoc, dvi hv.1,
      decodeWithLen_append hv.2, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  | datagram len d =>
    cases len
    · simp only [toEnd, Bool.not_false, forall_const] at hr; subst hr
      simp [type, body, decodeBody]
    · simp only [Valid] at hv
      simp only [type, body, ↓reduceIte, decodeBody, decodeWithLen_append hv, Option.map_some]

theorem decode_encode (f : Frame) (hv : f.Valid) (rest : List UInt8)
    (hr : f.toEnd = true → rest = []) : decode (encode f ++ rest) = some (f, rest) := by
  have ht : VarInt.Valid f.type := by
    have := type_lt f; unfold VarInt.Valid VarInt.maxValue; omega
  simp only [decode, encode, List.append_assoc, dvi ht, decodeBody_body f hv rest hr,
    Option.bind_eq_bind, Option.bind_some]

theorem encode_ne_nil (f : Frame) : encode f ≠ [] := by
  simp [encode, VarInt.encode_ne_nil]

theorem length_le_encodePayload (fs : List Frame) : fs.length ≤ (encodePayload fs).length := by
  induction fs with
  | nil => simp [encodePayload]
  | cons f fs ih =>
    have := encode_ne_nil f
    have : 0 < (encode f).length := List.length_pos_iff.2 this
    simp only [encodePayload, List.flatMap_cons, List.length_append, List.length_cons] at *
    omega

theorem decodeFramesFuel_encode (fs : List Frame) (h : PayloadOk fs) (n : Nat)
    (hn : fs.length ≤ n) : decodeFramesFuel n (encodePayload fs) = some fs := by
  induction fs generalizing n with
  | nil => cases n <;> rfl
  | cons f fs ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    obtain ⟨b, bs, hb⟩ : ∃ b bs, encode f = b :: bs := by
      cases h' : encode f with
      | nil => exact absurd h' (encode_ne_nil f)
      | cons b bs => exact ⟨b, bs, rfl⟩
    cases fs with
    | nil =>
      have hd := decode_encode f h [] (fun _ => rfl)
      simp only [encodePayload, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hd ⊢
      rw [hb] at hd ⊢
      simp only [decodeFramesFuel, hd]
      cases m <;> rfl
    | cons g gs =>
      obtain ⟨hf, he, hgs⟩ := h
      have hd := decode_encode f hf (encodePayload (g :: gs)) (by simp [he])
      have ih' := ih hgs m (by simp at hn ⊢; omega)
      simp only [encodePayload, List.flatMap_cons] at hd ih' ⊢
      rw [hb] at hd ⊢
      simp only [List.cons_append, decodeFramesFuel]
      rw [← List.cons_append, hd]
      simp [ih']

theorem decodePayload_encode (fs : List Frame) (hne : fs ≠ []) (h : PayloadOk fs) :
    decodePayload (encodePayload fs) = .ok fs := by
  have hl := length_le_encodePayload fs
  have hne' : encodePayload fs ≠ [] := by
    intro he; rw [he] at hl; cases fs with
    | nil => exact hne rfl
    | cons _ _ => simp at hl
  simp only [decodePayload, hne', ↓reduceIte, decodeFramesFuel_encode fs h _ hl]

end Silmaril.Proofs.Net.Quic.Frame

namespace Silmaril.Proofs.Net.Quic.Frame

open Silmaril.Net.Quic Silmaril.Net.Quic.Frame

theorem decodeBody_unknown {t : Nat} (h : knownType t = false) (xs : List UInt8) :
    decodeBody t xs = none := by
  unfold decodeBody; split <;> first | rfl | simp [knownType] at h

theorem decode_unknown {t : Nat} (ht : VarInt.Valid t) (h : knownType t = false)
    (xs : List UInt8) : decode (vi t ++ xs) = none := by
  simp only [decode, dvi ht, decodeBody_unknown h, Option.bind_eq_bind, Option.bind_some]

theorem decode_encode_eq (f : Frame) (rest : List UInt8) :
    decode (encode f ++ rest) = decodeBody f.type (f.body ++ rest) := by
  have ht : VarInt.Valid f.type := by
    have := type_lt f; unfold VarInt.Valid VarInt.maxValue; omega
  simp only [decode, encode, List.append_assoc, dvi ht, Option.bind_eq_bind, Option.bind_some]

theorem maxStreams_reject {m : Nat} (hm : VarInt.Valid m) (hl : maxStreamsLimit < m)
    (d : Dir) (rest : List UInt8) : decode (encode (.maxStreams d m) ++ rest) = none := by
  have : ¬ m ≤ maxStreamsLimit := by omega
  cases d <;> simp only [decode_encode_eq, type, body, decodeBody, dvi hm, this, ↓reduceIte,
    reduceCtorEq, Option.bind_eq_bind, Option.bind_some]

theorem streamsBlocked_reject {m : Nat} (hm : VarInt.Valid m) (hl : maxStreamsLimit < m)
    (d : Dir) (rest : List UInt8) : decode (encode (.streamsBlocked d m) ++ rest) = none := by
  have : ¬ m ≤ maxStreamsLimit := by omega
  cases d <;> simp only [decode_encode_eq, type, body, decodeBody, dvi hm, this, ↓reduceIte,
    reduceCtorEq, Option.bind_eq_bind, Option.bind_some]

theorem newToken_empty_reject (rest : List UInt8) :
    decode (encode (.newToken []) ++ rest) = none := by
  simp [decode_encode_eq, type, body, decodeBody, decodeWithLen_append (bs := []) (by decide)]

theorem stream_overflow_reject {i o : Nat} {d : List UInt8} (hi : VarInt.Valid i)
    (ho : VarInt.Valid o) (hd : VarInt.Valid d.length) (hl : VarInt.maxValue < o + d.length)
    (fin : Bool) (rest : List UInt8) :
    decode (encode (.stream i (some o) true fin d) ++ rest) = none := by
  have : ¬ o + d.length ≤ VarInt.maxValue := by omega
  cases fin <;> simp [decode_encode_eq, type, body, streamType, decodeBody, decodeStream,
    dvi hi, dvi ho, decodeWithLen_append hd, this]

end Silmaril.Proofs.Net.Quic.Frame
