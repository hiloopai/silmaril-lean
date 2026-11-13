module

public import Silmaril.Net.Http3.Datagram.Defs
import Silmaril.Proofs.Net.Http3.Datagram

@[expose] public section

/-!
# HTTP/3 Datagrams: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Http3/Datagram.lean`), RFC 9297 §2.1:

* `decode_encode`: a datagram whose Quarter Stream ID is at most `2^60 - 1` round trips;
* `decode_ok`: whatever is accepted has a Quarter Stream ID at most `2^60 - 1` and is the
  variable-length integer at the front of the frame payload, the rest being the payload;
* `decode_error`: the only parse error is `H3_DATAGRAM_ERROR`; `decode_large`: a Quarter
  Stream ID above `2^60 - 1` is that error;
* `streamId_isRequest`, `ofStream_spec`: Quarter Stream IDs and client-initiated bidirectional
  stream IDs below `2^62` correspond one to one (`id = 4 * quarter`);
* `ofParams_h3Datagram_bad` (§2.1.1, "MUST be either 0 or 1"): a SETTINGS frame announcing
  `SETTINGS_H3_DATAGRAM` with a value above 1 is rejected with `H3_SETTINGS_ERROR` by
  `Settings.ofParams`, wherever it appears in the list.

CHECKED: sample datagrams, the empty and truncated payloads, the negotiation and 0-RTT rules.
-/

namespace Silmaril.Net.Http3.Datagram

open Silmaril.Net.Quic

theorem decode_encode {d : Datagram} (h : d.Valid) : decode d.encode = .ok d :=
  Silmaril.Proofs.Net.Http3.Datagram.decode_encode h

theorem decode_ok {xs : List UInt8} {d : Datagram} (h : decode xs = .ok d) :
    d.Valid ∧ VarInt.decode xs = some (d.quarterStreamId, d.payload) :=
  Silmaril.Proofs.Net.Http3.Datagram.decode_ok h

theorem decode_error {xs : List UInt8} {e : ErrorCode} (h : decode xs = .error e) :
    e = .datagramError :=
  Silmaril.Proofs.Net.Http3.Datagram.decode_error h

theorem decode_large {q : Nat} (hv : VarInt.Valid q) (hq : maxQuarterStreamId < q)
    (payload : List UInt8) : decode (VarInt.encode q ++ payload) = .error .datagramError :=
  Silmaril.Proofs.Net.Http3.Datagram.decode_large hv hq payload

theorem streamId_isRequest {d : Datagram} (h : d.Valid) : isRequestStreamId d.streamId = true :=
  Silmaril.Proofs.Net.Http3.Datagram.streamId_isRequest h

theorem ofStream_spec {sid : Nat} (h : isRequestStreamId sid = true) (payload : List UInt8) :
    (ofStream sid payload).streamId = sid ∧ (ofStream sid payload).Valid :=
  Silmaril.Proofs.Net.Http3.Datagram.ofStream_spec h payload

theorem ofParams_h3Datagram_bad {ps : List (Nat × Nat)} {v : Nat} (hv : 1 < v)
    (hm : (settingH3Datagram, v) ∈ ps) : Settings.ofParams ps = .error .settingsError :=
  Silmaril.Proofs.Net.Http3.Datagram.ofParams_h3Datagram_bad hv hm

/-- Without both settings, no datagrams (§2.1.1). -/
theorem not_negotiated_of_peer_missing (sent : Settings) :
    h3DatagramsNegotiated sent none = false := by
  simp [h3DatagramsNegotiated]

/-! ## Known answers -/

/-- A datagram on request stream 4 (quarter ID 1) carrying `ab`. -/
theorem encode_sample : (ofStream 4 [0x61, 0x62]).encode = [0x01, 0x61, 0x62] := by rfl

/-- The payload may be empty (§2.1). -/
theorem decode_empty_payload : decode [0x00] = .ok ⟨0, []⟩ := by rfl

/-- "a QUIC DATAGRAM frame whose payload is too short to allow parsing the Quarter Stream ID
field" is `H3_DATAGRAM_ERROR`. -/
theorem decode_short : decode [] = .error .datagramError ∧
    decode [0x40] = .error .datagramError := ⟨rfl, rfl⟩

/-- The largest legal Quarter Stream ID, `2^60 - 1`, on eight bytes, and the next one. -/
theorem decode_bounds :
    decode [0xcf, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] = .ok ⟨2 ^ 60 - 1, []⟩ ∧
      decode [0xd0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] = .error .datagramError :=
  ⟨rfl, rfl⟩

example : disposition .receiveClosed = .drop ∧
    disposition .noDatagramSemantics = .abortStream .datagramError := ⟨rfl, rfl⟩

example : maySendDatagrams { h3Datagram := true } (some { h3Datagram := true }) 65535 = true ∧
    maySendDatagrams { h3Datagram := true } (some { h3Datagram := true }) 0 = false ∧
    maySendDatagrams { h3Datagram := true } (some {}) 65535 = false := by decide

/-- A value of 2 in the peer's SETTINGS is a connection error (§2.1.1). -/
example : Settings.ofParams [(0x33, 2)] = .error .settingsError := rfl

example : checkZeroRttH3Datagram true false = .error .settingsError := rfl

end Silmaril.Net.Http3.Datagram
