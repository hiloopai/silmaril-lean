module

public import Silmaril.Net.Http2.Frame.Defs
import Silmaril.Proofs.Net.Http2.Frame

@[expose] public section

/-!
# HTTP/2 frames: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Http2/Frame.lean`):

* `decodeHeader_encodeHeader`: a frame header whose fields fit their widths (§4.1) is read
  back from its 9 octets, and the reader stops after them;
* `readFrame_encodeFrame`: a frame within `SETTINGS_MAX_FRAME_SIZE` (§4.2) is read back from
  any stream it starts, and reading stops exactly where the next frame starts;
* `readFrame_sound`: a frame that is read has exactly the announced payload length and never
  exceeds the maximum frame size (the §4.2 bound that limits per-frame buffering);
* `FrameType.ofCode_code`, `ErrorCode.ofCode_code`: the type and error registries are
  injective on their codes.
-/

namespace Silmaril.Net.Http2

theorem length_encodeHeader (h : FrameHeader) : (encodeHeader h).length = 9 :=
  Silmaril.Proofs.Net.Http2.length_encodeHeader h

theorem decodeHeader_encodeHeader (h : FrameHeader) (hv : h.Valid) (rest : List UInt8) :
    decodeHeader (encodeHeader h ++ rest) = some (h, rest) :=
  Silmaril.Proofs.Net.Http2.decodeHeader_encodeHeader h hv rest

theorem readFrame_encodeFrame (m : Nat) (f : Frame) (hv : f.Valid) (hm : f.header.length ≤ m)
    (rest : List UInt8) : readFrame m (encodeFrame f ++ rest) = .ok (f, rest) :=
  Silmaril.Proofs.Net.Http2.readFrame_encodeFrame m f hv hm rest

theorem readFrame_sound {m : Nat} {xs : List UInt8} {f : Frame} {rest : List UInt8}
    (h : readFrame m xs = .ok (f, rest)) :
    f.payload.length = f.header.length ∧ f.header.length ≤ m :=
  Silmaril.Proofs.Net.Http2.readFrame_sound h

theorem FrameType.ofCode_code (t : FrameType) : FrameType.ofCode t.code = some t := by
  cases t <;> rfl

theorem ErrorCode.ofCode_code (e : ErrorCode) : ErrorCode.ofCode e.code = some e := by
  cases e <;> rfl

/-! Examples, checked by evaluation. -/

/-- A SETTINGS frame with the ACK flag and no payload (§6.5). -/
example : encodeHeader ⟨0, FrameType.settings.code, flagAck, 0⟩ = [0, 0, 0, 4, 1, 0, 0, 0, 0] := by
  decide +kernel

/-- The reserved bit is ignored on receipt (§4.1). -/
example : decodeHeader [0, 0, 0, 8, 0, 0x80, 0, 0, 1] = some (⟨0, 8, 0, 1⟩, []) := by
  decide +kernel

/-- A 16385-octet frame against the default maximum of 16384 (§4.2, §6.5.2). -/
example : (match readFrame 16384 (encodeHeader ⟨16385, 0, 0, 1⟩) with
    | .error e => e == .frameSize | .ok _ => false) = true := by
  decide +kernel

/-- An unknown frame type is ignored by the caller (§5.5). -/
example : FrameType.ofCode 0x10 = none := by decide

/-- The client preface is 24 octets (§3.4). -/
example : clientPreface.length = 24 := by decide +kernel

end Silmaril.Net.Http2
