module

public import Silmaril.Net.Http1.Fields.Defs
public import Silmaril.Crypto.SHA1.Defs
public import Silmaril.Encoding.Base64

@[expose] public section

/-!
# The WebSocket opening handshake over HTTP/1.1 (RFC 6455 §4, RFC 9110 §7.8)

The opening handshake is an HTTP/1.1 Upgrade (RFC 9110 §7.8): the client sends a `GET` with
`Upgrade: websocket` and `Connection: Upgrade`, and the server answers `101 Switching
Protocols`; the octets after the response's empty line are WebSocket frames
(`Silmaril.Net.WebSocket.Frame`). Heads are those of `Silmaril.Net.Http1` (RFC 9112), used
as an API: this module only reads and builds `RequestHead`/`ResponseHead` values.

* `readOffer`: the server's reading of a client handshake (§4.2.1): method `GET`, HTTP/1.1 or
  later, one `Host`, an `Upgrade` list containing `websocket` and a `Connection` list containing
  `Upgrade` (both ASCII case-insensitive), one `Sec-WebSocket-Key` that is the base64 encoding
  of 16 octets, and `Sec-WebSocket-Version: 13`. Any failure is a `HandshakeError`; a version
  mismatch is answered by `versionRejection` (§4.4: `426 Upgrade Required` with
  `Sec-WebSocket-Version: 13`).
* `acceptOf key`: `base64(SHA-1(key ++ "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"))` (§4.2.2
  step 5.4), with SHA-1 from `Silmaril.Crypto.SHA1` and base64 from `Silmaril.Base64` (RFC 4648
  §4, padded).
* `respond offer selected`: the server's `101` response (§4.2.2), optionally selecting one of
  the offered subprotocols.
* `checkResponse key offered`: the client's checks of §4.1 (status `101`, `Upgrade` and
  `Connection` tokens, `Sec-WebSocket-Accept` equal to `acceptOf key`, no extension that was
  not offered — this client offers none — and a subprotocol, if any, among those offered).
* `clientRequest`: the client's handshake request (§4.1).

**Security assumptions (RFC 6455 §10).** The handshake is not authentication. The accept value
only shows that the server read a WebSocket handshake (it defeats cross-protocol confusion
with non-WebSocket servers, §1.3); it is not a MAC, and SHA-1's weaknesses are irrelevant to
this purpose. The key MUST be "randomly selected" (§4.1, §10.3); this module takes the key as an
input and states no property of its randomness. Origin checks (`Origin`, §10.2), cookies and
authentication are application policy, outside this model. Confidentiality and integrity need
`wss` (TLS, `Silmaril.Net.Tunnel.Transport`), whose guarantees are assumed, not proved.

Field lookup, the list syntax (`#rule`, RFC 9110 §5.6.1) and token tests are the shared API of
the HTTP/1.1 track (`Silmaril.Net.Http1.Fields`: `fieldValues`, `fieldElements`,
`fieldHasToken`, all case-insensitive on names); names and literals are `Http1.ascii`.
-/

namespace Silmaril.Net.WebSocket.Handshake

open Silmaril.Net.Http1

/-- The GUID of §1.3 and §4.2.2. -/
def guid : List UInt8 := ascii "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"

/-- The octets of an ASCII character list. -/
def charBytes (cs : List Char) : List UInt8 := cs.map fun c => c.toNat.toUInt8

/-- The characters of octets (Latin-1, which is ASCII on the base64 alphabet). -/
def byteChars (xs : List UInt8) : List Char := xs.map fun b => Char.ofNat b.toNat

/-- A key is the base64 encoding of 16 octets (§4.1 item 7, §11.3.1). -/
def validKey (key : List UInt8) : Bool :=
  match Silmaril.Base64.decodeChars .std true (byteChars key) with
  | some nonce => nonce.length == 16
  | none => false

/-- The key for a 16-octet nonce: its padded base64 encoding. -/
def keyOf (nonce : List UInt8) : List UInt8 :=
  charBytes (Silmaril.Base64.encodeChars .std true nonce)

/-- `Sec-WebSocket-Accept` for `key` (§4.2.2). -/
def acceptOf (key : List UInt8) : List UInt8 :=
  charBytes (Silmaril.Base64.encodeChars .std true (Silmaril.Crypto.sha1 (key ++ guid)))

/-- What a server learns from a valid client handshake. -/
structure Offer where
  host : List UInt8
  target : List UInt8
  key : List UInt8
  /-- `Sec-WebSocket-Protocol` elements, in order (§4.1 item 10, §11.3.4). -/
  protocols : List (List UInt8)
  deriving DecidableEq, Repr

/-- Why a handshake is refused. -/
inductive HandshakeError where
  | notGet | oldVersion | host | upgrade | connection | key | wsVersion
  /-- Client side: a status other than 101. -/
  | status (code : Nat)
  | accept | extension | protocol
  deriving DecidableEq, Repr

/-- The server's reading of a client handshake (§4.2.1). -/
def readOffer (h : RequestHead) : Except HandshakeError Offer :=
  let fs := h.fields
  if h.line.method != ascii "GET" then .error .notGet
  else if !(h.line.version.major > 1 || (h.line.version.major == 1 && 1 ≤ h.line.version.minor))
    then .error .oldVersion
  else match fieldValues fs (ascii "Host") with
    | [host] =>
      if !fieldHasToken fs (ascii "Upgrade") (ascii "websocket") then .error .upgrade
      else if !fieldHasToken fs (ascii "Connection") (ascii "Upgrade") then .error .connection
      else match fieldValues fs (ascii "Sec-WebSocket-Key") with
        | [key] =>
          if !validKey key then .error .key
          else if fieldValues fs (ascii "Sec-WebSocket-Version") != [ascii "13"] then
            .error .wsVersion
          else .ok ⟨host, h.line.target, key,
            fieldElements fs (ascii "Sec-WebSocket-Protocol")⟩
        | _ => .error .key
    | _ => .error .host

/-- §4.4: the answer to an unsupported `Sec-WebSocket-Version`. -/
def versionRejection : ResponseHead :=
  ⟨⟨Version.http11, 426, ascii "Upgrade Required"⟩,
    [⟨ascii "Sec-WebSocket-Version", ascii "13"⟩]⟩

/-- The server's `101` response (§4.2.2). -/
def respond (o : Offer) (selected : Option (List UInt8)) : ResponseHead :=
  ⟨⟨Version.http11, 101, ascii "Switching Protocols"⟩,
    [⟨ascii "Upgrade", ascii "websocket"⟩, ⟨ascii "Connection", ascii "Upgrade"⟩,
     ⟨ascii "Sec-WebSocket-Accept", acceptOf o.key⟩] ++
    selected.toList.map fun p => ⟨ascii "Sec-WebSocket-Protocol", p⟩⟩

/-- The client's handshake request (§4.1), offering `protocols` (one field line each). -/
def clientRequest (o : Offer) : RequestHead :=
  ⟨⟨ascii "GET", o.target, Version.http11⟩,
    [⟨ascii "Host", o.host⟩, ⟨ascii "Upgrade", ascii "websocket"⟩,
     ⟨ascii "Connection", ascii "Upgrade"⟩, ⟨ascii "Sec-WebSocket-Key", o.key⟩,
     ⟨ascii "Sec-WebSocket-Version", ascii "13"⟩] ++
    o.protocols.map fun p => ⟨ascii "Sec-WebSocket-Protocol", p⟩⟩

/-- The client's checks of the server's response (§4.1, "the client MUST validate the server's
response as follows"); the selected subprotocol. -/
def checkResponse (key : List UInt8) (offered : List (List UInt8)) (r : ResponseHead) :
    Except HandshakeError (Option (List UInt8)) :=
  let fs := r.fields
  if r.line.code != 101 then .error (.status r.line.code)
  else if !fieldHasToken fs (ascii "Upgrade") (ascii "websocket") then .error .upgrade
  else if !fieldHasToken fs (ascii "Connection") (ascii "Upgrade") then .error .connection
  else if fieldValues fs (ascii "Sec-WebSocket-Accept") != [acceptOf key] then .error .accept
  else if !(fieldValues fs (ascii "Sec-WebSocket-Extensions")).isEmpty then .error .extension
  else match fieldValues fs (ascii "Sec-WebSocket-Protocol") with
    | [] => .ok none
    | [p] => if offered.contains p then .ok (some p) else .error .protocol
    | _ => .error .protocol

end Silmaril.Net.WebSocket.Handshake
