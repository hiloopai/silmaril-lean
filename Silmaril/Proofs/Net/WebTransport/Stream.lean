module

public import Silmaril.Net.WebTransport.Stream.Defs
import Silmaril.Net.Quic.VarInt.Thms

/-!
# WebTransport stream headers: proofs

For `Silmaril.Net.WebTransport.Stream.Thms` (draft-ietf-webtrans-http3-17 §4.2, §4.3).
-/

@[expose] public section

namespace Silmaril.Proofs.Net.WebTransport.Stream

open Silmaril.Net.Quic Silmaril.Net.Http3 Silmaril.Net.WebTransport

theorem validSessionId_varInt {sid : Nat} (h : validSessionId sid = true) : VarInt.Valid sid := by
  simp only [validSessionId, Datagram.isRequestStreamId, Datagram.maxStreamId,
    Bool.and_eq_true] at h
  have := of_decide_eq_true h.2
  unfold VarInt.Valid VarInt.maxValue; omega

theorem decodeHeader_encodeHeader {lead sid : Nat} (hl : VarInt.Valid lead)
    (h : validSessionId sid = true) (rest : List UInt8) :
    decodeHeader lead (encodeHeader lead sid ++ rest) = .ok (sid, rest) := by
  simp only [encodeHeader, List.append_assoc, decodeHeader, VarInt.decode_encode hl,
    VarInt.decode_encode (validSessionId_varInt h), h, ne_eq, not_true_eq_false, ↓reduceIte]

theorem decodeHeader_ok {lead : Nat} {xs : List UInt8} {sid : Nat} {rest : List UInt8}
    (h : decodeHeader lead xs = .ok (sid, rest)) :
    validSessionId sid = true ∧ ∃ r1, VarInt.decode xs = some (lead, r1) ∧
      VarInt.decode r1 = some (sid, rest) := by
  unfold decodeHeader at h
  split at h
  · cases h
  · rename_i t r1 h1
    split at h
    · cases h
    · rename_i ht
      split at h
      · cases h
      · rename_i s r2 h2
        split at h
        · rename_i hv
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [ne_eq, Decidable.not_not] at ht
          subst ht
          exact ⟨hv, r1, h1, h2⟩
        · cases h

theorem decodeHeader_badSession {lead sid : Nat} (hl : VarInt.Valid lead) (hs : VarInt.Valid sid)
    (h : validSessionId sid = false) (rest : List UInt8) :
    decodeHeader lead (encodeHeader lead sid ++ rest) = .error (.protocol .idError) := by
  simp only [encodeHeader, List.append_assoc, decodeHeader, VarInt.decode_encode hl,
    VarInt.decode_encode hs, h, ne_eq, not_true_eq_false, ↓reduceIte, Bool.false_eq_true]

theorem decodeHeader_local {lead : Nat} {xs : List UInt8} {sid : Nat} {rest : List UInt8}
    (tail : List UInt8) (h : decodeHeader lead xs = .ok (sid, rest)) :
    decodeHeader lead (xs ++ tail) = .ok (sid, rest ++ tail) := by
  obtain ⟨hv, r1, h1, h2⟩ := decodeHeader_ok h
  simp only [decodeHeader, VarInt.decode_local tail h1, VarInt.decode_local tail h2, hv,
    ne_eq, not_true_eq_false, ↓reduceIte]

end Silmaril.Proofs.Net.WebTransport.Stream
