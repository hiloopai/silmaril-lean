module

public import Silmaril.Net.Quic.Frame.Defs
import Silmaril.Proofs.Net.Quic.Frame

@[expose] public section

/-!
# QUIC frames: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Quic/Frame.lean`):

* `decode_encode`: every valid frame of RFC 9000 §19 and RFC 9221 §4 is read back from its
  encoding, and the reader stops exactly where the encoding ends, provided that a frame
  without a Length field ("extends to the end of the packet") is followed by nothing;
* `readFrame_encode`: the same through the error-reporting reader;
* `decodePayload_encode`: a nonempty list of valid frames in which only the last may lack a
  length decodes back from the concatenated payload (§12.4); `decodePayload_empty`: an empty
  payload is PROTOCOL_VIOLATION;
* `readFrame_unknown`: an unknown frame type is FRAME_ENCODING_ERROR (§12.4);
* rejections the RFC assigns to FRAME_ENCODING_ERROR: `maxStreams_reject`,
  `streamsBlocked_reject` (above `2^60`, §19.11, §19.14), `newToken_empty_reject` (§19.7),
  `stream_overflow_reject` (offset plus length above `2^62 - 1`, §19.8).

CHECKED by evaluation: hand-encoded frames from the §19 layouts (STREAM with every
combination of the OFF/LEN/FIN bits, RESET_STREAM, STOP_SENDING, MAX_STREAMS, CONNECTION_CLOSE
of both types, ACK with ranges and ECN counts, NEW_CONNECTION_ID, DATAGRAM), an ACK range that
goes negative (§19.3.1), a non-minimal frame type encoding, and whole payloads.
-/

namespace Silmaril.Net.Quic.Frame

theorem decode_encode (f : Frame) (hv : f.Valid) (rest : List UInt8)
    (hr : f.toEnd = true → rest = []) : decode (encode f ++ rest) = some (f, rest) :=
  Silmaril.Proofs.Net.Quic.Frame.decode_encode f hv rest hr

theorem decode_encode_self (f : Frame) (hv : f.Valid) : decode (encode f) = some (f, []) := by
  simpa using decode_encode f hv [] (fun _ => rfl)

theorem readFrame_encode (f : Frame) (hv : f.Valid) (rest : List UInt8)
    (hr : f.toEnd = true → rest = []) : readFrame (encode f ++ rest) = .ok (f, rest) := by
  simp only [readFrame, decode_encode f hv rest hr]

theorem encode_ne_nil (f : Frame) : encode f ≠ [] :=
  Silmaril.Proofs.Net.Quic.Frame.encode_ne_nil f

theorem decodePayload_encode (fs : List Frame) (hne : fs ≠ []) (h : PayloadOk fs) :
    decodePayload (encodePayload fs) = .ok fs :=
  Silmaril.Proofs.Net.Quic.Frame.decodePayload_encode fs hne h

theorem decodePayload_empty : decodePayload [] = .error .protocolViolation := rfl

theorem decodeBody_unknown {t : Nat} (h : knownType t = false) (xs : List UInt8) :
    decodeBody t xs = none :=
  Silmaril.Proofs.Net.Quic.Frame.decodeBody_unknown h xs

theorem readFrame_unknown {t : Nat} (ht : VarInt.Valid t) (h : knownType t = false)
    (xs : List UInt8) : readFrame (vi t ++ xs) = .error .frameEncodingError := by
  simp only [readFrame, Silmaril.Proofs.Net.Quic.Frame.decode_unknown ht h xs]

theorem maxStreams_reject {m : Nat} (hm : VarInt.Valid m) (hl : maxStreamsLimit < m)
    (d : Dir) (rest : List UInt8) : decode (encode (.maxStreams d m) ++ rest) = none :=
  Silmaril.Proofs.Net.Quic.Frame.maxStreams_reject hm hl d rest

theorem streamsBlocked_reject {m : Nat} (hm : VarInt.Valid m) (hl : maxStreamsLimit < m)
    (d : Dir) (rest : List UInt8) : decode (encode (.streamsBlocked d m) ++ rest) = none :=
  Silmaril.Proofs.Net.Quic.Frame.streamsBlocked_reject hm hl d rest

theorem newToken_empty_reject (rest : List UInt8) :
    decode (encode (.newToken []) ++ rest) = none :=
  Silmaril.Proofs.Net.Quic.Frame.newToken_empty_reject rest

theorem stream_overflow_reject {i o : Nat} {d : List UInt8} (hi : VarInt.Valid i)
    (ho : VarInt.Valid o) (hd : VarInt.Valid d.length) (hl : VarInt.maxValue < o + d.length)
    (fin : Bool) (rest : List UInt8) :
    decode (encode (.stream i (some o) true fin d) ++ rest) = none :=
  Silmaril.Proofs.Net.Quic.Frame.stream_overflow_reject hi ho hd hl fin rest

/-! ## Known answers, hand-encoded from the §19 layouts -/

/-- STREAM 0x0f (OFF, LEN, FIN): stream 4, offset 5, length 2, data "hi"; a PING follows. -/
example : decode [0x0f, 0x04, 0x05, 0x02, 0x68, 0x69, 0x01] =
    some (.stream 4 (some 5) true true [0x68, 0x69], [0x01]) := by decide

/-- STREAM 0x08 (no bits): offset 0, the data runs to the end of the packet. -/
example : decode [0x08, 0x00, 0x61, 0x62, 0x63] =
    some (.stream 0 none false false [0x61, 0x62, 0x63], []) := by decide

/-- STREAM 0x0b (LEN, FIN), empty data: the end of stream 0 at offset 0. -/
example : encode (.stream 0 none true true []) = [0x0b, 0x00, 0x00] := by decide

/-- The eight STREAM types (§19.8: "0b00001XXX"). -/
example : [none, some 0].flatMap (fun off => [false, true].flatMap fun len =>
    [false, true].map fun fin => streamType off len fin) =
      [0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f] := by decide

/-- RESET_STREAM on stream 0 with application error 0x010c (H3_REQUEST_CANCELLED, a two-byte
varint `0x41 0x0c`) and final size 100 (`0x40 0x64`). -/
example : encode (.resetStream 0 0x010c 100) = [0x04, 0x00, 0x41, 0x0c, 0x40, 0x64] := by decide

example : decode [0x05, 0x02, 0x41, 0x0c] = some (.stopSending 2 0x010c, []) := by decide

/-- MAX_STREAMS (unidirectional) 3, the limit of the §19.11 example. -/
example : decode [0x13, 0x03] = some (.maxStreams .uni 3, []) := by decide

/-- MAX_STREAMS of `2^60 + 1` (an eight-byte varint) is rejected (§19.11). -/
example : readFrame [0x12, 0xd0, 0, 0, 0, 0, 0, 0, 0x01] = .error .frameEncodingError := by
  rfl

/-- MAX_STREAMS of exactly `2^60` is accepted. -/
example : decode [0x12, 0xd0, 0, 0, 0, 0, 0, 0, 0] = some (.maxStreams .bidi (2 ^ 60), []) := by
  decide

/-- CONNECTION_CLOSE 0x1c: FLOW_CONTROL_ERROR, triggered by a STREAM frame (0x08), no reason. -/
example : encode (.connectionClose TransportError.flowControlError.code 0x08 []) =
    [0x1c, 0x03, 0x08, 0x00] := by decide

/-- CONNECTION_CLOSE 0x1d: application error 0x0100 (H3_NO_ERROR), reason "bye". -/
example : decode [0x1d, 0x41, 0x00, 0x03, 0x62, 0x79, 0x65] =
    some (.applicationClose 0x0100 [0x62, 0x79, 0x65], []) := by decide

/-- ACK 0x03: largest 10, delay 0, one extra range, first range 2 (packets 8–10), gap 1 and
length 3 (packets 2–5), ECN counts 1, 2, 3. -/
example : decode [0x03, 0x0a, 0x00, 0x01, 0x02, 0x01, 0x03, 0x01, 0x02, 0x03] =
    some (.ack 10 0 2 [⟨1, 3⟩] (some ⟨1, 2, 3⟩), []) := by decide

/-- An ACK range below packet 0 is FRAME_ENCODING_ERROR (§19.3.1): first range 6 > largest 5. -/
example : readFrame [0x02, 0x05, 0x00, 0x00, 0x06] = .error .frameEncodingError := by rfl

/-- An ACK announcing more ranges than the packet carries (§20.1 FRAME_ENCODING_ERROR). -/
example : readFrame [0x02, 0x05, 0x00, 0x05, 0x00, 0x00, 0x00] = .error .frameEncodingError := by
  rfl

/-- NEW_CONNECTION_ID with a 4-byte connection ID and a 16-byte reset token. -/
example : (decode ([0x18, 0x01, 0x00, 0x04, 1, 2, 3, 4] ++ List.replicate 16 7)).map (·.1) =
    some (.newConnectionId 1 0 [1, 2, 3, 4] (List.replicate 16 7)) := by decide

/-- NEW_CONNECTION_ID with Retire Prior To above the Sequence Number is rejected (§19.15). -/
example : decode ([0x18, 0x01, 0x02, 0x04, 1, 2, 3, 4] ++ List.replicate 16 7) = none := by
  decide

/-- NEW_CONNECTION_ID with a connection ID of length 0 is rejected (§19.15: "Values less than 1
and greater than 20 are invalid"). -/
example : decode ([0x18, 0x01, 0x00, 0x00] ++ List.replicate 16 7) = none := by decide

/-- DATAGRAM 0x31 with length 2, and 0x30 extending to the end of the packet (RFC 9221 §4). -/
example : decode [0x31, 0x02, 0xaa, 0xbb, 0x01] = some (.datagram true [0xaa, 0xbb], [0x01]) := by
  decide
example : decode [0x30, 0xaa, 0xbb, 0x01] = some (.datagram false [0xaa, 0xbb, 0x01], []) := by
  decide

/-- The unknown type 0x1f is FRAME_ENCODING_ERROR (§12.4). -/
example : readFrame [0x1f] = .error .frameEncodingError := by rfl

/-- A two-byte encoding of PING (`0x4001`) is accepted: the §12.4 MAY is not taken. -/
example : decode [0x40, 0x01] = some (.ping, []) := by decide

/-- A payload: PING, two PADDING, then a STREAM frame without length. -/
example : decodePayload [0x01, 0x00, 0x00, 0x08, 0x00, 0x61, 0x62] =
    .ok [.ping, .padding, .padding, .stream 0 none false false [0x61, 0x62]] := by rfl

/-- A payload whose middle frame is truncated. -/
example : decodePayload [0x01, 0x04, 0x00] = .error .frameEncodingError := by rfl

example : encodePayload [.ping, .maxData 1000, .datagram false [1, 2]] =
    [0x01, 0x10, 0x43, 0xe8, 0x30, 1, 2] := by decide

/-- Table 3: STREAM is not allowed in Initial packets, CRYPTO not in 0-RTT, and only the
transport CONNECTION_CLOSE in Handshake packets. -/
example : (stream 0 none true false []).allowedIn .initial = false ∧
    (crypto 0 []).allowedIn .zeroRtt = false ∧
    (connectionClose 0 0 []).allowedIn .handshake = true ∧
    (applicationClose 0 []).allowedIn .handshake = false := by decide

/-- A client receiving STREAM data on its own unidirectional stream 2 (§19.8). -/
example : (stream 2 none true false []).directionError .client = some .streamStateError := by
  decide

end Silmaril.Net.Quic.Frame
