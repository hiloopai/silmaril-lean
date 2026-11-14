module

public import Silmaril.Net.WebTransport.Capsule.Defs
import Silmaril.Proofs.Net.WebTransport.Capsule

@[expose] public section

/-!
# WebTransport capsules: theorems (draft-ietf-webtrans-http3-17)

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/WebTransport/Capsule.lean`):

* `ofCapsule_toCapsule`, `decode_encode`: every valid WebTransport capsule (32-bit close code,
  message at most 1024 bytes of UTF-8, Maximum Streams at most `2^60`, integers in range) round
  trips, through the raw capsule and through the bytes;
* `ofCapsule_valid`: whatever a receiver accepts is valid in that sense, so a too-long or
  non-UTF-8 WT_CLOSE_SESSION message (§6) and a Maximum Streams above `2^60` (§5.6.2, §5.6.3)
  never get through;
* `ofCapsule_unknown`: capsules of other types are skipped (RFC 9297 §3.2);
* `u32Read_u32Bytes`: the 32-bit Application Error Code field round trips.

CHECKED: byte encodings of each capsule, and the rejections of §5.4, §5.6.2 and §6.
-/

namespace Silmaril.Net.WebTransport

open Silmaril.Net.Quic Silmaril.Net.Http3

theorem u32Read_u32Bytes {n : Nat} (h : n < 2 ^ 32) (rest : List UInt8) :
    u32Read (u32Bytes n ++ rest) = some (n, rest) :=
  Silmaril.Proofs.Net.WebTransport.Capsule.u32Read_u32Bytes h rest

namespace WtCapsule

theorem ofCapsule_toCapsule {w : WtCapsule} (h : w.Valid) : ofCapsule w.toCapsule = .ok (some w) :=
  Silmaril.Proofs.Net.WebTransport.Capsule.ofCapsule_toCapsule h

theorem ofCapsule_valid {c : Capsule} {w : WtCapsule} (hc : c.Valid)
    (h : ofCapsule c = .ok (some w)) : w.Valid :=
  Silmaril.Proofs.Net.WebTransport.Capsule.ofCapsule_valid hc h

theorem ofCapsule_unknown {c : Capsule} (h : c.type ∉ knownCapsuleTypes) :
    ofCapsule c = .ok none :=
  Silmaril.Proofs.Net.WebTransport.Capsule.ofCapsule_unknown h

theorem toCapsule_valid {w : WtCapsule} (h : w.Valid) : w.toCapsule.Valid :=
  Silmaril.Proofs.Net.WebTransport.Capsule.toCapsule_valid h

theorem decode_encode {m : Nat} {w : WtCapsule} (h : w.Valid)
    (hm : w.toCapsule.value.length ≤ m) (rest : List UInt8) :
    decode m (w.encode ++ rest) = .ok (some w, rest) :=
  Silmaril.Proofs.Net.WebTransport.Capsule.decode_encode h hm rest

/-! ## Known answers -/

/-- WT_DRAIN_SESSION: type `0x78ae` (four bytes), length 0 (§4.7, Figure 5). -/
theorem encode_drain : drainSession.encode = [0x80, 0x00, 0x78, 0xae, 0x00] := by rfl

/-- WT_CLOSE_SESSION with code 7 and message "bye": type `0x2843`, length 7, the code on 32
bits, then the message (§6, Figure 11). -/
theorem encode_close :
    (closeSession 7 [0x62, 0x79, 0x65]).encode =
      [0x68, 0x43, 0x07, 0x00, 0x00, 0x00, 0x07, 0x62, 0x79, 0x65] := by rfl

/-- WT_MAX_STREAMS (bidirectional, `0x190B4D3F`) with 100 streams (§5.6.2). -/
theorem encode_maxStreams :
    (maxStreams .bidi 100).encode = [0x99, 0x0b, 0x4d, 0x3f, 0x02, 0x40, 0x64] := by rfl

theorem encode_types :
    (maxStreams .uni 0).toCapsule.type = 0x190B4D40 ∧
      (streamsBlocked .bidi 0).toCapsule.type = 0x190B4D43 ∧
      (streamsBlocked .uni 0).toCapsule.type = 0x190B4D44 ∧
      (maxData 0).toCapsule.type = 0x190B4D3D ∧ (dataBlocked 0).toCapsule.type = 0x190B4D41 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem decode_close :
    decode 2048 [0x68, 0x43, 0x07, 0x00, 0x00, 0x00, 0x07, 0x62, 0x79, 0x65] =
      .ok (some (closeSession 7 [0x62, 0x79, 0x65]), []) := by rfl

/-- A non-UTF-8 message (a lone continuation byte) is malformed (§6). -/
theorem decode_close_badUtf8 :
    decode 2048 [0x68, 0x43, 0x05, 0x00, 0x00, 0x00, 0x07, 0x80] =
      .error (.capsule .malformed) := by rfl

/-- A message longer than 1024 bytes is malformed (§6). -/
theorem ofCapsule_close_tooLong {code : Nat} {msg : List UInt8} (hc : code < 2 ^ 32)
    (hl : maxCloseMessage < msg.length) :
    ofCapsule ⟨typeCloseSession, u32Bytes code ++ msg⟩ = .error .malformed := by
  simp [ofCapsule, typeCloseSession, Capsule.typeDatagram, u32Read_u32Bytes hc msg,
    Nat.not_le.2 hl]

/-- A close code cut short (§6; RFC 9297 §3.3). -/
theorem ofCapsule_close_short : ofCapsule ⟨typeCloseSession, [0, 0, 0]⟩ = .error .malformed := by
  rfl

/-- WT_DRAIN_SESSION must be empty. -/
theorem ofCapsule_drain_nonempty : ofCapsule ⟨typeDrainSession, [0]⟩ = .error .malformed := by
  rfl

/-- Maximum Streams `2^60` is accepted, `2^60 + 1` is `WT_FLOW_CONTROL_ERROR` (§5.6.2). -/
theorem ofCapsule_maxStreams_limit :
    ofCapsule ⟨typeMaxStreamsBidi, VarInt.encode (2 ^ 60)⟩ = .ok (some (maxStreams .bidi (2 ^ 60))) ∧
      ofCapsule ⟨typeMaxStreamsUni, VarInt.encode (2 ^ 60 + 1)⟩ = .error .flowControl :=
  ⟨by rfl, by rfl⟩

/-- Trailing bytes after Maximum Data are malformed (RFC 9297 §3.3). -/
theorem ofCapsule_maxData_trailing : ofCapsule ⟨typeMaxData, [0x05, 0x00]⟩ = .error .malformed := by
  rfl

/-- WT_MAX_STREAM_DATA and WT_STREAM_DATA_BLOCKED are prohibited over HTTP/3 (§5.4). -/
theorem ofCapsule_prohibited : ofCapsule ⟨typeMaxStreamData, [0]⟩ = .error .prohibited ∧
    ofCapsule ⟨typeStreamDataBlocked, [0]⟩ = .error .prohibited := ⟨rfl, rfl⟩

/-- An unregistered type is skipped. -/
theorem ofCapsule_skip : ofCapsule ⟨0x17, [1, 2, 3]⟩ = .ok none := by rfl

/-- UTF-8 (RFC 3629 §4): "é" (`C3 A9`) and "€" (`E2 82 AC`) are valid; an overlong `C0 AF`, a
surrogate `ED A0 80` and `F4 90 80 80` (above U+10FFFF) are not. -/
example : validUtf8 [0xc3, 0xa9] ∧ validUtf8 [0xe2, 0x82, 0xac] ∧ !validUtf8 [0xc0, 0xaf] ∧
    !validUtf8 [0xed, 0xa0, 0x80] ∧ !validUtf8 [0xf4, 0x90, 0x80, 0x80] := by decide

end WtCapsule

end Silmaril.Net.WebTransport
