module

public import Silmaril.Net.Http2.Frame.Defs

@[expose] public section

/-!
# WebSocket frames (RFC 6455 §5)

The base framing protocol of RFC 6455 §5.2:

```
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-------+-+-------------+-------------------------------+
|F|R|R|R| opcode|M| Payload len |    Extended payload length    |
|I|S|S|S|  (4)  |A|     (7)     |             (16/64)           |
|N|V|V|V|       |S|             |   (if payload len==126/127)   |
| |1|2|3|       |K|             |                               |
+-+-+-+-+-------+-+-------------+ - - - - - - - - - - - - - - - +
|     Extended payload length continued, if payload len == 127  |
+ - - - - - - - - - - - - - - - +-------------------------------+
|                               |Masking-key, if MASK set to 1  |
+-------------------------------+-------------------------------+
| Masking-key (continued)       |          Payload Data         |
+-------------------------------- - - - - - - - - - - - - - - - +
```

* `Frame`: FIN, the three RSV bits (as one number `rsv < 8`), the opcode (`< 16`), the
  masking key if the MASK bit is set, and the **unmasked** application payload.
* `encode`: the octets of a frame. The payload length uses "the minimal number of bytes"
  (§5.2): 7 bits up to 125, `126` and 16 bits up to 65535, `127` and 64 bits (most
  significant bit 0) above. The payload is masked on the wire when a key is present (§5.3).
* `decode maxPayload`: the strict reader. It rejects non-minimal length encodings and a
  64-bit length with its most significant bit set (both are "MUST" rules on the sender in
  §5.2; rejecting them on receipt is this module's documented choice, so that a frame has
  exactly one encoding), and payloads longer than `maxPayload` (a recipient limit, §10.4).
* **Masking (§5.3).** `applyMask key off data`: octet `i` of `data` is XORed with octet
  `(off + i) mod 4` of the key ("j = i MOD 4; transformed-octet-i = original-octet-i XOR
  masking-key-octet-j"). The same function unmasks (`Frame.Thms.applyMask_applyMask`), and
  masking a concatenation is masking the pieces at shifted offsets
  (`applyMask_append`), which is how a streaming implementation masks a payload in pieces.
* **Opcodes (§5.2, §11.8).** `0x0` continuation, `0x1` text, `0x2` binary, `0x8` close,
  `0x9` ping, `0xA` pong; `0x3`–`0x7` and `0xB`–`0xF` are reserved. Control frames are the
  opcodes with the most significant bit set (§5.5): `isControl`.
* **Control frames (§5.5).** "All control frames MUST have a payload length of 125 bytes
  or less and MUST NOT be fragmented": `Frame.controlOk`.
* **Direction (§5.1, §5.3).** "a client MUST mask all frames that it sends to the server"
  and "A server MUST NOT mask any frames that it sends to the client": `Frame.maskOk`.

Security notes (RFC 6455 §10.3): masking is not a confidentiality or integrity
mechanism. Its purpose is that an attacker who controls a client script cannot choose the
octets a vulnerable intermediary sees; that relies on the key being unpredictable
("The masking key needs to be unpredictable", §5.3, §10.3), which is an **assumption on
the client's randomness source**, not something this module can prove. The proved facts
here are functional: the codec is a bijection between valid frames and their encodings.

Theorems: `Silmaril.Net.WebSocket.Frame.Thms`.
-/

namespace Silmaril.Net.WebSocket

open Silmaril.Net.Http2 (beBytes beValue)

/-! ## Opcodes (§5.2, §11.8) -/

def opContinuation : Nat := 0x0
def opText : Nat := 0x1
def opBinary : Nat := 0x2
def opClose : Nat := 0x8
def opPing : Nat := 0x9
def opPong : Nat := 0xA

/-- Control frames: the most significant bit of the opcode is set (§5.5). -/
def isControl (op : Nat) : Bool := 8 ≤ op

/-- The opcodes RFC 6455 defines; the others are reserved for further frames (§5.2). -/
def isDefinedOpcode (op : Nat) : Bool := [0x0, 0x1, 0x2, 0x8, 0x9, 0xA].contains op

/-- Data frames that start a message (§5.6): text or binary. -/
def isDataStart (op : Nat) : Bool := op == opText || op == opBinary

/-! ## Masking (§5.3) -/

/-- A 32-bit masking key, as its four octets in wire order. -/
structure MaskKey where
  k0 : UInt8
  k1 : UInt8
  k2 : UInt8
  k3 : UInt8
  deriving DecidableEq, Repr, Inhabited

/-- Octet `j mod 4` of the key. -/
def MaskKey.at (k : MaskKey) (j : Nat) : UInt8 :=
  match j % 4 with
  | 0 => k.k0
  | 1 => k.k1
  | 2 => k.k2
  | _ => k.k3

/-- The four octets of the key, in wire order. -/
def MaskKey.bytes (k : MaskKey) : List UInt8 := [k.k0, k.k1, k.k2, k.k3]

/-- Mask (or unmask) `data`, whose first octet is octet `off` of the payload (§5.3). -/
def applyMask (k : MaskKey) : Nat → List UInt8 → List UInt8
  | _, [] => []
  | off, b :: bs => (b ^^^ k.at off) :: applyMask k (off + 1) bs

/-- Mask with an optional key: no key, no change. -/
def maskWith : Option MaskKey → List UInt8 → List UInt8
  | none, data => data
  | some k, data => applyMask k 0 data

/-! ## Frames -/

/-- A WebSocket frame (§5.2). `payload` is the application payload, unmasked. -/
structure Frame where
  fin : Bool
  /-- RSV1, RSV2, RSV3 as the number `4·RSV1 + 2·RSV2 + RSV3`. -/
  rsv : Nat
  opcode : Nat
  /-- The masking key; `none` when the MASK bit is 0. -/
  mask : Option MaskKey
  payload : List UInt8
  deriving DecidableEq, Repr, Inhabited

/-- The largest payload length a frame can carry: the 64-bit length has its most significant
bit 0 (§5.2). -/
def maxLength : Nat := 2 ^ 63

/-- The fields fit their widths. -/
def Frame.Valid (f : Frame) : Prop := f.rsv < 8 ∧ f.opcode < 16 ∧ f.payload.length < maxLength

instance (f : Frame) : Decidable f.Valid := by unfold Frame.Valid; infer_instance

/-- §5.5: a control frame has at most 125 octets of payload and FIN set. -/
def Frame.controlOk (f : Frame) : Bool := !isControl f.opcode || (f.fin && f.payload.length ≤ 125)

/-- Who sends a frame. -/
inductive Role where
  | client | server
  deriving DecidableEq, Repr, Inhabited

/-- §5.1: clients mask every frame, servers mask none. -/
def Frame.maskOk (r : Role) (f : Frame) : Bool :=
  match r with
  | .client => f.mask.isSome
  | .server => f.mask.isNone

/-! ## Encoding (§5.2) -/

/-- The 7-bit payload length code and the extended length octets (minimal, §5.2). -/
def lengthCode (n : Nat) : Nat × List UInt8 :=
  if n ≤ 125 then (n, [])
  else if n < 65536 then (126, beBytes 2 n)
  else (127, beBytes 8 n)

/-- First octet: FIN, RSV1–3, opcode. -/
def byte0 (f : Frame) : UInt8 := (f.fin.toNat * 128 + f.rsv * 16 + f.opcode).toUInt8

/-- The octets of a frame. -/
def encode (f : Frame) : List UInt8 :=
  byte0 f ::
    ((if f.mask.isSome then 128 else 0) + (lengthCode f.payload.length).1).toUInt8 ::
    ((lengthCode f.payload.length).2 ++ ((f.mask.map MaskKey.bytes).getD [] ++
      maskWith f.mask f.payload))

/-! ## Decoding -/

/-- Why a reader stops. `incomplete` asks for more input; the others are protocol errors
(the connection is failed, §7.1.7). -/
inductive DecodeError where
  | incomplete
  /-- A length that has a shorter encoding (§5.2: "the minimal number of bytes MUST be
  used"). -/
  | nonMinimalLength
  /-- A 64-bit length with its most significant bit set (§5.2). -/
  | lengthMsb
  /-- A payload above the recipient's limit (§10.4). -/
  | tooLarge
  deriving DecidableEq, Repr

/-- Read the payload length after the 7-bit code `code`. -/
def readLength (code : Nat) (xs : List UInt8) : Except DecodeError (Nat × List UInt8) :=
  if code ≤ 125 then .ok (code, xs)
  else if code = 126 then
    if xs.length < 2 then .error .incomplete
    else
      let n := beValue (xs.take 2)
      if n ≤ 125 then .error .nonMinimalLength else .ok (n, xs.drop 2)
  else
    if xs.length < 8 then .error .incomplete
    else
      let n := beValue (xs.take 8)
      if maxLength ≤ n then .error .lengthMsb
      else if n < 65536 then .error .nonMinimalLength
      else .ok (n, xs.drop 8)

/-- Read the masking key if the MASK bit is set. -/
def readKey (masked : Bool) (xs : List UInt8) : Option (Option MaskKey × List UInt8) :=
  if masked then
    match xs with
    | a :: b :: c :: d :: rest => some (some ⟨a, b, c, d⟩, rest)
    | _ => none
  else some (none, xs)

/-- Read one frame whose payload is at most `maxPayload` octets. -/
def decode (maxPayload : Nat) : List UInt8 → Except DecodeError (Frame × List UInt8)
  | b0 :: b1 :: xs =>
    match readLength (b1.toNat % 128) xs with
    | .error e => .error e
    | .ok (len, ys) =>
      if maxPayload < len then .error .tooLarge
      else
        match readKey (b1.toNat / 128 == 1) ys with
        | none => .error .incomplete
        | some (key, zs) =>
          if zs.length < len then .error .incomplete
          else
            .ok (⟨b0.toNat / 128 == 1, b0.toNat / 16 % 8, b0.toNat % 16, key,
              maskWith key (zs.take len)⟩, zs.drop len)
  | _ => .error .incomplete

/-- Decode a stream of complete frames (fuel: one frame per octet at most). -/
def decodeAll (maxPayload : Nat) : Nat → List UInt8 → Except DecodeError (List Frame)
  | _, [] => .ok []
  | 0, _ => .error .incomplete
  | fuel + 1, xs =>
    match decode maxPayload xs with
    | .error e => .error e
    | .ok (f, rest) => match decodeAll maxPayload fuel rest with
      | .error e => .error e
      | .ok fs => .ok (f :: fs)

/-! ## Close frame bodies (§5.5.1, §7.4) -/

/-- Status codes a peer may put in a Close frame (§7.4.1, §7.4.2, and the IANA "WebSocket
Close Code Number Registry" entries 1012–1014): 1000–1003, 1007–1014, and 3000–4999.
1004 is reserved, and 1005, 1006 and 1015 "MUST NOT be set as a status code in a Close
control frame by an endpoint". -/
def isSendableCloseCode (c : Nat) : Bool :=
  (1000 ≤ c && c ≤ 1003) || (1007 ≤ c && c ≤ 1014) || (3000 ≤ c && c ≤ 4999)

/-- UTF-8 validity of a reason (§5.5.1: "the body … is not guaranteed to be human readable",
but "the data MUST be UTF-8"); the same check as `Silmaril.Unicode.utf8?` (core's
`String.fromUTF8?`). -/
def isUtf8 (xs : List UInt8) : Bool := (String.fromUTF8? xs.toByteArray).isSome

/-- A Close frame body: empty, or a status code and a UTF-8 reason (§5.5.1). -/
def encodeClose : Option (Nat × List UInt8) → List UInt8
  | none => []
  | some (code, reason) => beBytes 2 code ++ reason

/-- Read a Close frame body. A one-octet body, an unsendable code, or a reason that is not
UTF-8 is a protocol error (§7.4.1 1002, §8.1 1007). -/
def decodeClose : List UInt8 → Option (Option (Nat × List UInt8))
  | [] => some none
  | [_] => none
  | a :: b :: reason =>
    let code := beValue [a, b]
    if isSendableCloseCode code && isUtf8 reason then some (some (code, reason)) else none

/-- A Close body that a sender may put on the wire: a sendable code and a UTF-8 reason. The
§5.5 limit of 125 octets on control payloads is the frame's (`Frame.controlOk`); with a code,
it leaves 123 octets for the reason. -/
def CloseBody.Valid : Option (Nat × List UInt8) → Prop
  | none => True
  | some (code, reason) => isSendableCloseCode code = true ∧ isUtf8 reason = true

end Silmaril.Net.WebSocket
