module

public import Silmaril.Net.WebTransport.Stream.Defs
public import Silmaril.Net.Http3.Datagram.Thms
import Silmaril.Proofs.Net.WebTransport.Stream

@[expose] public section

/-!
# WebTransport stream headers: theorems (draft-ietf-webtrans-http3-17)

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/WebTransport/Stream.lean`):

* `decodeUniHeader_uniHeader`, `decodeBidiHeader_bidiHeader` (§4.2, §4.3): a header with a
  valid session ID reads back, and the rest of the stream is untouched;
* `decodeHeader_ok`: an accepted header names a valid session ID (a client-initiated
  bidirectional stream ID) and starts with the expected type or signal;
* `decodeHeader_badSession` (§4): any other session ID is `H3_ID_ERROR`;
* `decodeHeader_local`: the header can be read from a growing prefix of the stream;
* `sessionDatagram_spec` (§4.5): a session's datagrams name its CONNECT stream.

CHECKED: header bytes for session 0 and 4, a session ID of a unidirectional stream, an HTTP/3
request stream (not WebTransport), WT_STREAM outside the first bytes.
-/

namespace Silmaril.Net.WebTransport

open Silmaril.Net.Quic Silmaril.Net.Http3

theorem decodeHeader_encodeHeader {lead sid : Nat} (hl : VarInt.Valid lead)
    (h : validSessionId sid = true) (rest : List UInt8) :
    decodeHeader lead (encodeHeader lead sid ++ rest) = .ok (sid, rest) :=
  Silmaril.Proofs.Net.WebTransport.Stream.decodeHeader_encodeHeader hl h rest

theorem decodeUniHeader_uniHeader {sid : Nat} (h : validSessionId sid = true)
    (rest : List UInt8) : decodeUniHeader (uniHeader sid ++ rest) = .ok (sid, rest) :=
  decodeHeader_encodeHeader (by decide) h rest

theorem decodeBidiHeader_bidiHeader {sid : Nat} (h : validSessionId sid = true)
    (rest : List UInt8) : decodeBidiHeader (bidiHeader sid ++ rest) = .ok (sid, rest) :=
  decodeHeader_encodeHeader (by decide) h rest

theorem decodeHeader_ok {lead : Nat} {xs : List UInt8} {sid : Nat} {rest : List UInt8}
    (h : decodeHeader lead xs = .ok (sid, rest)) :
    validSessionId sid = true ∧ ∃ r1, VarInt.decode xs = some (lead, r1) ∧
      VarInt.decode r1 = some (sid, rest) :=
  Silmaril.Proofs.Net.WebTransport.Stream.decodeHeader_ok h

theorem decodeHeader_badSession {lead sid : Nat} (hl : VarInt.Valid lead) (hs : VarInt.Valid sid)
    (h : validSessionId sid = false) (rest : List UInt8) :
    decodeHeader lead (encodeHeader lead sid ++ rest) = .error (.protocol .idError) :=
  Silmaril.Proofs.Net.WebTransport.Stream.decodeHeader_badSession hl hs h rest

theorem decodeHeader_local {lead : Nat} {xs : List UInt8} {sid : Nat} {rest : List UInt8}
    (tail : List UInt8) (h : decodeHeader lead xs = .ok (sid, rest)) :
    decodeHeader lead (xs ++ tail) = .ok (sid, rest ++ tail) :=
  Silmaril.Proofs.Net.WebTransport.Stream.decodeHeader_local tail h

theorem sessionDatagram_spec {sid : Nat} (h : validSessionId sid = true) (payload : List UInt8) :
    (sessionDatagram sid payload).streamId = sid ∧ (sessionDatagram sid payload).Valid :=
  Datagram.ofStream_spec h payload

/-! ## Known answers -/

/-- Both `0x54` and `0x41` take two bytes (they exceed 63). -/
theorem uniHeader_zero : uniHeader 0 = [0x40, 0x54, 0x00] := by rfl
theorem bidiHeader_four : bidiHeader 4 = [0x40, 0x41, 0x04] := by rfl

theorem reliableSize_sample : reliableSize (bidiHeader 4) 10 = 13 := by rfl

/-- Stream 2 is a client-initiated unidirectional stream: not a session (§4). -/
example : decodeUniHeader [0x40, 0x54, 0x02, 0xff] = .error (.protocol .idError) := by rfl

/-- A request stream starting with a HEADERS frame (type `0x01`) is plain HTTP/3. -/
example : decodeBidiHeader [0x01, 0x05, 0, 0, 0, 0, 0] = .error (.other 0x01) := by rfl

/-- A header cut short. -/
example : decodeBidiHeader [0x40, 0x41] = .error .incomplete := by rfl

example : checkFrameType bidiSignal = .error .frameUnexpected ∧ checkFrameType 0x00 = .ok () :=
  ⟨rfl, rfl⟩

end Silmaril.Net.WebTransport
