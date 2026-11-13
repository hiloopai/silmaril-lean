module

public import Silmaril.Net.Http2.Frame.Defs
public import Silmaril.Net.Http.Field.Defs

@[expose] public section

/-!
# The TLS record header (RFC 8446 §5.1) and telling TLS from cleartext HTTP

Every TLS record starts with a 5-octet header:

```
struct {
    ContentType type;                     /* 20 change_cipher_spec, 21 alert,
                                             22 handshake, 23 application_data,
                                             24 heartbeat (RFC 6520) */
    ProtocolVersion legacy_record_version;
    uint16 length;
    opaque fragment[TLSPlaintext.length];
} TLSPlaintext;
```

"The length MUST NOT exceed 2^14 bytes" for plaintext records, and 2^14 + 256 for
`TLSCiphertext` (RFC 8446 §5.1, §5.2). `encodeHeader`/`decodeHeader` are that layout; the reader
rejects unknown content types and lengths above the limit it is given.

**Direct TLS versus cleartext on one listener.** A server that accepts both TLS and cleartext
HTTP on one port (or must reject one of them) decides on the first octet: a TLS record starts
with a content type below `0x21`, an HTTP/1.1 request line with a method token whose octets are
`tchar`s (RFC 9112 §3, RFC 9110 §5.6.2), and the HTTP/2 cleartext preface with `P`
(RFC 9113 §3.4). `Record.Thms.tls_not_token` proves the first two are disjoint, reusing the
`tchar` check of the HTTP semantics track. This is how `https`-only servers detect a cleartext
request (and, for example, answer 400) and why an `http` request can never be mistaken for a
ClientHello. It is a statement about octets, not about security.

Not modelled here: the handshake messages (ClientHello and its extensions), the key schedule,
and record protection; see docs/projects/crypto.md for their milestones.
-/

namespace Silmaril.Net.Tls

open Silmaril.Net.Http2 (beBytes beValue)

/-- The content types of RFC 8446 §5.1 and RFC 6520. -/
def contentTypes : List Nat := [20, 21, 22, 23, 24]

/-- The handshake content type, which the ClientHello uses. -/
def handshakeType : Nat := 22

/-- A record header. -/
structure RecordHeader where
  type : Nat
  version : Nat
  length : Nat
  deriving DecidableEq, Repr

/-- The plaintext limit (RFC 8446 §5.1). -/
def maxPlaintext : Nat := 2 ^ 14

/-- The ciphertext limit (RFC 8446 §5.2). -/
def maxCiphertext : Nat := 2 ^ 14 + 256

/-- A header the writer may send: a known content type, a 16-bit version, a length within
`limit`. -/
def RecordHeader.Valid (limit : Nat) (h : RecordHeader) : Prop :=
  h.type ∈ contentTypes ∧ h.version < 2 ^ 16 ∧ h.length ≤ limit ∧ limit < 2 ^ 16

def encodeHeader (h : RecordHeader) : List UInt8 :=
  h.type.toUInt8 :: (beBytes 2 h.version ++ beBytes 2 h.length)

/-- Read a record header whose length is at most `limit`. -/
def decodeHeader (limit : Nat) : List UInt8 → Option (RecordHeader × List UInt8)
  | t :: v0 :: v1 :: l0 :: l1 :: rest =>
    let len := beValue [l0, l1]
    if contentTypes.contains t.toNat && len ≤ limit then
      some (⟨t.toNat, beValue [v0, v1], len⟩, rest)
    else none
  | _ => none

/-- The first octet of a cleartext HTTP/1.1 request, if it starts with a method token. -/
def startsWithToken (xs : List UInt8) : Bool :=
  match xs with
  | b :: _ => Silmaril.Net.Http.Field.isTchar b
  | [] => false

end Silmaril.Net.Tls
