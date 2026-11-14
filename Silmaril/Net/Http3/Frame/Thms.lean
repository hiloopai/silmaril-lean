module

public import Silmaril.Net.Http3.Frame.Defs
import Silmaril.Proofs.Net.Http3.Frame

@[expose] public section

/-!
# HTTP/3 frames: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Http3/Frame.lean`):

* `readRaw_encodeRaw`: a raw frame with in-range fields, within the buffering limit, reads
  back exactly, and the reader stops at its end (RFC 9114 §7.1);
* `readRaw_ok`: whatever `readRaw` returns has a payload within the limit and in range, and
  consumes a non-empty prefix of the input — frame buffering is bounded by the caller's limit
  (§10.5);
* `readRawAll_flatMap`: concatenated frames read back as the list of frames (a stream);
* `ofRaw_toRaw`, `decodeFrame_encode`: every valid typed frame (§7.2) round trips through
  its payload layout, including SETTINGS lists, PUSH_PROMISE's push ID prefix, reserved
  HTTP/2 types and unknown/extension types;
* `decodeParams_encodeParams`: SETTINGS payloads round trip;
* `isGrease_iff`, `apply_grease`: the reserved code points are exactly `0x1f * N + 0x21`, and
  a grease setting never changes the interpreted `Settings` (§7.2.4.1: "MUST NOT consider such
  settings to have any meaning").

CHECKED (`rfl`): a SETTINGS frame, the rejection of HTTP/2-reserved and duplicate setting
identifiers (`H3_SETTINGS_ERROR`), of a CANCEL_PUSH payload with extra bytes and of a
truncated SETTINGS parameter (`H3_FRAME_ERROR`), an over-limit frame, unknown and reserved
types, a boolean setting out of range, and the interpretation of unknown error codes.
-/

namespace Silmaril.Net.Http3

open Silmaril.Net.Quic

theorem readRaw_encodeRaw {f : RawFrame} (hf : f.Valid) {maxPayload : Nat}
    (hmax : f.payload.length ≤ maxPayload) (rest : List UInt8) :
    readRaw maxPayload (encodeRaw f ++ rest) = .ok (f, rest) :=
  Silmaril.Proofs.Net.Http3.Frame.readRaw_encodeRaw hf hmax rest

theorem readRaw_ok {maxPayload : Nat} {xs rest : List UInt8} {r : RawFrame}
    (h : readRaw maxPayload xs = .ok (r, rest)) :
    r.payload.length ≤ maxPayload ∧ rest.length < xs.length ∧ rest <:+ xs ∧ r.Valid :=
  Silmaril.Proofs.Net.Http3.Frame.readRaw_ok h

theorem readRawAll_flatMap {maxPayload : Nat} (fs : List RawFrame)
    (hv : ∀ f ∈ fs, f.Valid ∧ f.payload.length ≤ maxPayload) :
    readRawAll maxPayload (fs.flatMap encodeRaw) = .ok fs :=
  Silmaril.Proofs.Net.Http3.Frame.readRawAllFuel_flatMap fs hv _ (Nat.le_refl _)

theorem decodeParams_encodeParams {ps : List (Nat × Nat)}
    (hv : ∀ p ∈ ps, VarInt.Valid p.1 ∧ VarInt.Valid p.2) (hok : paramsOk ps = true) :
    decodeParams (encodeParams ps) = .ok ps :=
  Silmaril.Proofs.Net.Http3.Frame.decodeParams_encodeParams hv hok

theorem ofRaw_toRaw {f : Frame} (hf : f.Valid) : Frame.ofRaw f.toRaw = .ok f :=
  Silmaril.Proofs.Net.Http3.Frame.ofRaw_toRaw hf

theorem toRaw_valid {f : Frame} (hf : f.Valid) : f.toRaw.Valid :=
  Silmaril.Proofs.Net.Http3.Frame.toRaw_valid hf

theorem decodeFrame_encode {f : Frame} (hf : f.Valid) {maxPayload : Nat}
    (hmax : f.toRaw.payload.length ≤ maxPayload) (rest : List UInt8) :
    decodeFrame maxPayload (f.encode ++ rest) = .ok (f, rest) :=
  Silmaril.Proofs.Net.Http3.Frame.decodeFrame_encode hf hmax rest

theorem isGrease_iff (m : Nat) : isGrease m = true ↔ ∃ n, m = grease n :=
  Silmaril.Proofs.Net.Http3.Frame.isGrease_iff m

/-- A grease setting is ignored by the interpretation (§7.2.4.1). -/
theorem apply_grease (s : Settings) (n v : Nat) : s.apply (grease n, v) = .ok s :=
  Silmaril.Proofs.Net.Http3.Frame.apply_unknown s v
    (Silmaril.Proofs.Net.Http3.Frame.grease_not_known n)

/-! ## Known answers -/

/-- `SETTINGS { MAX_FIELD_SECTION_SIZE = 4096, QPACK_BLOCKED_STREAMS = 16, 0x21 = 0 }`. -/
theorem settings_sample :
    decodeFrame 1024 [0x04, 0x07, 0x06, 0x50, 0x00, 0x07, 0x10, 0x21, 0x00] =
      .ok (.settings [(6, 4096), (7, 16), (0x21, 0)], []) := by rfl

theorem settings_sample_encode :
    (Frame.settings [(6, 4096), (7, 16), (0x21, 0)]).encode =
      [0x04, 0x07, 0x06, 0x50, 0x00, 0x07, 0x10, 0x21, 0x00] := by rfl

theorem settings_sample_interpret :
    Settings.ofParams [(6, 4096), (7, 16), (0x21, 0)] =
      .ok { maxFieldSectionSize := some 4096, qpackBlockedStreams := 16 } := by rfl

/-- HTTP/2's SETTINGS_ENABLE_PUSH (`0x02`) is reserved in HTTP/3 (§7.2.4.1). -/
theorem settings_h2_reserved :
    decodeFrame 1024 [0x04, 0x02, 0x02, 0x00] = .error (.protocol .settingsError) := by rfl

theorem settings_duplicate :
    decodeFrame 1024 [0x04, 0x04, 0x06, 0x01, 0x06, 0x02] = .error (.protocol .settingsError) := by
  rfl

theorem settings_truncated :
    decodeFrame 1024 [0x04, 0x01, 0x06] = .error (.protocol .frameError) := by rfl

/-- §7.1: a payload with bytes after its fields is `H3_FRAME_ERROR`. -/
theorem cancelPush_extra :
    decodeFrame 1024 [0x03, 0x02, 0x05, 0x00] = .error (.protocol .frameError) := by rfl

theorem goaway_sample : decodeFrame 1024 [0x07, 0x01, 0x04] = .ok (.goaway 4, []) := by rfl

theorem data_incomplete : decodeFrame 1024 [0x00, 0x05, 0x68, 0x69] = .error (.read .incomplete) := by
  rfl

theorem data_tooLarge : decodeFrame 4 [0x00, 0x05, 0x68, 0x69] = .error (.read .tooLarge) := by rfl

/-- HTTP/2's PRIORITY type is kept as reserved, for the stream layer to reject. -/
theorem priority_reserved : decodeFrame 1024 [0x02, 0x00] = .ok (.h2Reserved 2 [], []) := by rfl

/-- A grease frame type (`0x21`) is unknown and kept for the stream layer to skip. -/
theorem grease_frame : decodeFrame 1024 [0x21, 0x01, 0xff] = .ok (.unknown 0x21 [0xff], []) := by
  rfl

theorem h3Datagram_bad_value :
    Settings.ofParams [(settingH3Datagram, 2)] = .error .settingsError := by rfl

theorem interpret_unknown : ErrorCode.interpret 0x21 = .noError := by rfl

theorem interpret_known : ErrorCode.interpret 0x010a = .missingSettings := by rfl

end Silmaril.Net.Http3
