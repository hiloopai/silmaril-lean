module

public import Silmaril.Net.WebSocket.Frame.Defs
import Silmaril.Proofs.Net.WebSocket.Frame

@[expose] public section

/-!
# WebSocket frames: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/WebSocket/Frame.lean`):

* **Masking is an involution** (`applyMask_applyMask`, RFC 6455 §5.3: "The same algorithm
  applies regardless of the direction of the translation"), preserves length, depends on the
  offset modulo 4 only, and composes over concatenation (`applyMask_append`): a payload may
  be masked fragment by fragment if each piece starts at its offset.
* **Codec round trip** (`decode_encode`): a valid frame within the recipient's limit is read
  back from any stream it starts, and the reader stops exactly after it.
* **Unambiguity** (`decode_sound`): whatever the reader accepts is a valid frame within the
  limit, and the octets it consumed are exactly that frame's encoding. With the round trip,
  valid frames and their encodings are in bijection: the strict reader rejects every
  non-minimal length (§5.2).
* **Control frames are small** (`controlOk_length`): a control frame that respects §5.5 is at
  most 131 octets on the wire (2 header octets, a 4-octet key, 125 octets of payload).
* **Close bodies** (`decodeClose_encodeClose`, `decodeClose_sound`): the §5.5.1 body codec is
  a bijection between valid bodies and the bodies the reader accepts.

CHECKED (`decide`): the examples of RFC 6455 §5.7.
-/

namespace Silmaril.Net.WebSocket

/-- Big-endian octets read back (for `Silmaril.Net.Http2.beBytes`/`beValue`; a candidate for
`Silmaril.Net.Wire`, see docs/projects/websocket-tls.md). -/
theorem beValue_beBytes (k x : Nat) (hx : x < 256 ^ k) :
    Silmaril.Net.Http2.beValue (Silmaril.Net.Http2.beBytes k x) = x :=
  Silmaril.Proofs.Net.WebSocket.beValue_beBytes k x hx

theorem beBytes_beValue (xs : List UInt8) :
    Silmaril.Net.Http2.beBytes xs.length (Silmaril.Net.Http2.beValue xs) = xs :=
  Silmaril.Proofs.Net.WebSocket.beBytes_beValue xs

theorem beValue_lt (xs : List UInt8) : Silmaril.Net.Http2.beValue xs < 256 ^ xs.length :=
  Silmaril.Proofs.Net.WebSocket.beValue_lt xs

theorem applyMask_applyMask (k : MaskKey) (off : Nat) (xs : List UInt8) :
    applyMask k off (applyMask k off xs) = xs :=
  Silmaril.Proofs.Net.WebSocket.applyMask_applyMask k off xs

theorem length_applyMask (k : MaskKey) (off : Nat) (xs : List UInt8) :
    (applyMask k off xs).length = xs.length :=
  Silmaril.Proofs.Net.WebSocket.length_applyMask k off xs

theorem applyMask_append (k : MaskKey) (off : Nat) (xs ys : List UInt8) :
    applyMask k off (xs ++ ys) = applyMask k off xs ++ applyMask k (off + xs.length) ys :=
  Silmaril.Proofs.Net.WebSocket.applyMask_append k off xs ys

theorem applyMask_mod (k : MaskKey) (off : Nat) (xs : List UInt8) :
    applyMask k (off % 4) xs = applyMask k off xs :=
  Silmaril.Proofs.Net.WebSocket.applyMask_mod k off xs

theorem maskWith_maskWith (k : Option MaskKey) (xs : List UInt8) :
    maskWith k (maskWith k xs) = xs :=
  Silmaril.Proofs.Net.WebSocket.maskWith_maskWith k xs

theorem decode_encode (m : Nat) (f : Frame) (hv : f.Valid) (hm : f.payload.length ≤ m)
    (rest : List UInt8) : decode m (encode f ++ rest) = .ok (f, rest) :=
  Silmaril.Proofs.Net.WebSocket.decode_encode m f hv hm rest

theorem decode_sound {m : Nat} {xs : List UInt8} {f : Frame} {rest : List UInt8}
    (h : decode m xs = .ok (f, rest)) :
    f.Valid ∧ f.payload.length ≤ m ∧ xs = encode f ++ rest :=
  Silmaril.Proofs.Net.WebSocket.decode_sound h

/-- Two valid frames with the same encoding are equal. -/
theorem encode_injective {f g : Frame} (hf : f.Valid) (hg : g.Valid)
    (h : encode f = encode g) : f = g := by
  have e := decode_encode (max f.payload.length g.payload.length) f hf (Nat.le_max_left _ _) []
  rw [h, decode_encode _ g hg (Nat.le_max_right _ _)] at e
  cases e; rfl

theorem controlOk_length (f : Frame) (h : f.controlOk = true) (hc : isControl f.opcode = true) :
    (encode f).length ≤ 131 :=
  Silmaril.Proofs.Net.WebSocket.controlOk_length f h hc

theorem decodeClose_encodeClose (c : Option (Nat × List UInt8)) (hv : CloseBody.Valid c) :
    decodeClose (encodeClose c) = some c :=
  Silmaril.Proofs.Net.WebSocket.decodeClose_encodeClose c hv

theorem decodeClose_sound {b : List UInt8} {c : Option (Nat × List UInt8)}
    (h : decodeClose b = some c) : encodeClose c = b ∧ CloseBody.Valid c :=
  Silmaril.Proofs.Net.WebSocket.decodeClose_sound h

/-! ## RFC 6455 §5.7 examples -/

/-- "Hello" as ASCII octets. -/
def hello : List UInt8 := [0x48, 0x65, 0x6c, 0x6c, 0x6f]

/-- The key of the masked examples. -/
def exampleKey : MaskKey := ⟨0x37, 0xfa, 0x21, 0x3d⟩

/-- "A single-frame unmasked text message". -/
example : encode ⟨true, 0, opText, none, hello⟩ = [0x81, 0x05, 0x48, 0x65, 0x6c, 0x6c, 0x6f] := by
  decide

/-- "A single-frame masked text message". -/
example : encode ⟨true, 0, opText, some exampleKey, hello⟩ =
    [0x81, 0x85, 0x37, 0xfa, 0x21, 0x3d, 0x7f, 0x9f, 0x4d, 0x51, 0x58] := by
  decide

/-- The reader recovers the masked message and its key. -/
example : decode 125 [0x81, 0x85, 0x37, 0xfa, 0x21, 0x3d, 0x7f, 0x9f, 0x4d, 0x51, 0x58] =
    .ok (⟨true, 0, opText, some exampleKey, hello⟩, []) := by
  rfl

/-- "A fragmented unmasked text message": `Hel` then `lo`. -/
example : encode ⟨false, 0, opText, none, [0x48, 0x65, 0x6c]⟩ = [0x01, 0x03, 0x48, 0x65, 0x6c] ∧
    encode ⟨true, 0, opContinuation, none, [0x6c, 0x6f]⟩ = [0x80, 0x02, 0x6c, 0x6f] := by
  decide

/-- "Unmasked Ping request and masked Ping response" (the response is a Pong). -/
example : encode ⟨true, 0, opPing, none, hello⟩ = [0x89, 0x05, 0x48, 0x65, 0x6c, 0x6c, 0x6f] ∧
    encode ⟨true, 0, opPong, some exampleKey, hello⟩ =
      [0x8a, 0x85, 0x37, 0xfa, 0x21, 0x3d, 0x7f, 0x9f, 0x4d, 0x51, 0x58] := by
  decide

/-- "256 bytes binary message in a single unmasked frame": `0x82 0x7E 0x0100`. -/
example : (encode ⟨true, 0, opBinary, none, List.replicate 256 0⟩).take 4 =
    [0x82, 0x7e, 0x01, 0x00] := by
  decide +kernel

/-- "64KiB binary message in a single unmasked frame": `0x82 0x7F 0x0000000000010000`. -/
example : lengthCode 65536 = (127, [0, 0, 0, 0, 0, 1, 0, 0]) := by decide

/-- A 5-octet payload with a 16-bit length is not minimal and is rejected (§5.2). -/
example : decode 125 [0x81, 0x7e, 0x00, 0x05, 0x48, 0x65, 0x6c, 0x6c, 0x6f] =
    .error .nonMinimalLength := by
  rfl

/-- A 64-bit length with its most significant bit set is rejected (§5.2). -/
example : decode 125 [0x82, 0x7f, 0x80, 0, 0, 0, 0, 0, 0, 0] = .error .lengthMsb := by rfl

/-- A Close body with code 1000 ("normal closure") and no reason (§7.4.1). -/
example : encodeClose (some (1000, [])) = [0x03, 0xe8] ∧
    decodeClose [0x03, 0xe8] = some (some (1000, [])) := by
  decide

/-- 1005 ("no status received") must not be sent; a peer that sends it is rejected. -/
example : decodeClose [0x03, 0xed] = none := by decide

end Silmaril.Net.WebSocket
