module

public import Silmaril.Net.Http2.Fields.Defs
public import Silmaril.Net.Http2.Frame.Defs
public import Silmaril.Net.Http.Uri.Defs

@[expose] public section

/-!
# CONNECT tunnels and extended CONNECT (RFC 9110 §9.3.6, RFC 9113 §8.5, RFC 8441, RFC 9220)

Three ways of turning an HTTP request into a byte tunnel, which this module keeps apart:

1. **CONNECT over HTTP/1.1** (RFC 9110 §9.3.6, RFC 9112 §3.2.3). The target is in
   authority-form, `uri-host ":" port` (`isAuthorityForm`; the port is required). After a 2xx
   response the connection is a tunnel to that authority; the response has no content and
   "A server MUST NOT send any Transfer-Encoding or Content-Length header fields in a 2xx
   (Successful) response to CONNECT" (`connectResponseOk`).
2. **CONNECT over HTTP/2** (RFC 9113 §8.5) and HTTP/3 (RFC 9114 §4.4): `:method` CONNECT with
   `:authority` only, no `:scheme` and no `:path`. The tunnel is one stream. This is the
   classic case of `Silmaril.Net.Http2.validRequest` (HTTP/2 track).
3. **Extended CONNECT** (RFC 8441 for HTTP/2, RFC 9220 for HTTP/3): a new `:protocol`
   pseudo-header names the protocol spoken on the tunnel (`websocket` for WebSockets), and
   `:scheme` and `:path` are present ("On requests that contain the :protocol pseudo-header
   field, the :scheme and :path pseudo-header fields of the target URI … MUST also be
   included", RFC 8441 §4). A client MUST NOT send `:protocol` unless the server sent
   `SETTINGS_ENABLE_CONNECT_PROTOCOL` (0x08) with value 1 (RFC 8441 §3; the same setting
   identifier in HTTP/3, RFC 9220 §3). The value is 0 or 1, and "A sender MUST NOT send a
   SETTINGS_ENABLE_CONNECT_PROTOCOL parameter with the value of 0 after previously sending a
   value of 1" (`applyEnableConnect`).

For WebSockets over extended CONNECT (`validWebSocketRequest`), `:protocol` is `websocket`;
the `Sec-WebSocket-Key`/`Sec-WebSocket-Accept` exchange of RFC 6455 is not used ("the
:protocol pseudo-header field" supersedes it, RFC 8441 §5) and the server answers 2xx (`200`)
instead of `101`. The frames that follow on the stream are RFC 6455 frames
(`Silmaril.Net.WebSocket.Frame`), with the same masking rules.

Fields are the decoded field sections of the HTTP/2 track (`List Silmaril.Net.Hpack.Entry`).
HTTP/3 field sections, once decoded by QPACK (QUIC/HTTP/3 track), have the same shape; the
rules here take only that list and a flag for the setting, so they apply to both versions.
-/

namespace Silmaril.Net.Tunnel

open Silmaril.Net.Hpack (ascii Entry)
open Silmaril.Net.Http2

/-! ## CONNECT over HTTP/1.1 -/

/-- `authority-form = uri-host ":" port` (RFC 9112 §3.2.3), with a registered name or an
IPv4 address as host and a non-empty decimal port. IP-literals are not covered. -/
def isAuthorityForm (t : List UInt8) : Bool :=
  t.contains 0x3a &&
    let (portRev, hostRev) := breakColon t.reverse
    !portRev.isEmpty && Silmaril.Net.Http.Uri.isPort portRev.reverse &&
      !hostRev.isEmpty && Silmaril.Net.Http.Uri.isRegName hostRev.reverse

/-- A 2xx response to CONNECT carries neither `Content-Length` nor `Transfer-Encoding`
(RFC 9110 §9.3.6). Field names are compared in lower case. -/
def connectResponseOk (status : Nat) (fieldNames : List (List UInt8)) : Bool :=
  !(200 ≤ status && status < 300) ||
    fieldNames.all fun n => n != ascii "content-length" && n != ascii "transfer-encoding"

/-! ## Extended CONNECT (RFC 8441, RFC 9220) -/

/-- `SETTINGS_ENABLE_CONNECT_PROTOCOL` (RFC 8441 §3, RFC 9220 §3). -/
def settingEnableConnectProtocol : Nat := 0x08

/-- Apply a received `SETTINGS_ENABLE_CONNECT_PROTOCOL` value to the current state (whether
the peer has enabled extended CONNECT). -/
def applyEnableConnect (enabled : Bool) (value : Nat) : Except ErrorCode Bool :=
  if value == 1 then .ok true
  else if value == 0 then (if enabled then .error .protocolError else .ok false)
  else .error .protocolError

/-- The request pseudo-header fields with `:protocol`. -/
def extendedPseudo : List (List UInt8) := requestPseudo ++ [ascii ":protocol"]

/-- An extended CONNECT request header section, given whether the peer enabled it. -/
def validExtendedConnect (enabled : Bool) (fs : List Entry) : Bool :=
  enabled && validSection extendedPseudo fs &&
    pseudoValues fs ":method" == [ascii "CONNECT"] &&
    (pseudoValues fs ":protocol").length == 1 &&
    (pseudoValues fs ":authority").length == 1 &&
    (pseudoValues fs ":scheme").length == 1 &&
    match pseudoValues fs ":path" with
    | [p] => !p.isEmpty
    | _ => false

/-- The values of the regular field `n` (lower case, as HTTP/2 requires, RFC 9113 §8.2.1). -/
def fieldValues (fs : List Entry) (n : String) : List (List UInt8) :=
  (fs.filter fun e => e.name == ascii n).map Entry.value

/-- A WebSocket bootstrap over extended CONNECT (RFC 8441 §5, RFC 9220 §3): `:protocol` is
`websocket`, and `sec-websocket-version`, if present, is `13`. -/
def validWebSocketRequest (enabled : Bool) (fs : List Entry) : Bool :=
  validExtendedConnect enabled fs && pseudoValues fs ":protocol" == [ascii "websocket"] &&
    (fieldValues fs "sec-websocket-version").all (· == ascii "13")

/-- The server accepts the tunnel with a 2xx status (RFC 8441 §5, RFC 9110 §9.3.6). -/
def tunnelAccepted (respFields : List Entry) : Bool :=
  validResponse respFields &&
    match pseudoValues respFields ":status" with
    | [s] => s.length == 3 && s.head? == some 0x32
    | _ => false

/-! ## Examples (RFC 8441 §5.1) -/

/-- The request of RFC 8441 §5.1. -/
def rfc8441Request : List Entry :=
  [⟨ascii ":method", ascii "CONNECT"⟩, ⟨ascii ":protocol", ascii "websocket"⟩,
   ⟨ascii ":scheme", ascii "https"⟩, ⟨ascii ":path", ascii "/chat"⟩,
   ⟨ascii ":authority", ascii "server.example.com"⟩,
   ⟨ascii "sec-websocket-protocol", ascii "chat, superchat"⟩,
   ⟨ascii "sec-websocket-extensions", ascii "permessage-deflate"⟩,
   ⟨ascii "sec-websocket-version", ascii "13"⟩,
   ⟨ascii "origin", ascii "http://www.example.com"⟩]

/-- The response of RFC 8441 §5.1. -/
def rfc8441Response : List Entry :=
  [⟨ascii ":status", ascii "200"⟩, ⟨ascii "sec-websocket-protocol", ascii "chat"⟩]

end Silmaril.Net.Tunnel
