module

public import Silmaril.Net.Http3.ExtendedConnect.Defs
import Silmaril.Proofs.Net.Http3.ExtendedConnect

@[expose] public section

/-!
# Extended CONNECT: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Http3/ExtendedConnect.lean`):

* `validRequest_of_hasProtocol`: the plain request rules reject every request carrying
  `:protocol` (it is an unknown pseudo-header field to them, RFC 9113 §8.3); this is why the
  extension needs the opt-in setting (RFC 8441 §3);
* `validRequestExt_disabled`: when the server has not sent `SETTINGS_ENABLE_CONNECT_PROTOCOL =
  1`, the extended rules are exactly the plain rules: the extension is conservative;
* `validExtendedConnect_disabled`: no extended CONNECT is valid without the setting;
* `validExtendedConnect_spec`: a valid extended CONNECT has method CONNECT, a `:protocol`, and
  one `:scheme` and one `:path` (RFC 8441 §4);
* `validRequest_stripProtocol`: removing `:protocol` from a valid extended CONNECT never gives a
  valid plain CONNECT (or any valid request): plain CONNECT forbids `:scheme` and `:path`
  (RFC 9113 §8.5, RFC 9114 §4.4), so the two request forms cannot be confused.

CHECKED: the RFC 8441 §5.1 example (as an HTTP/3 request, RFC 9220 §3), a WebTransport request,
and requests violating each rule.
-/

namespace Silmaril.Net.Http3

open Silmaril.Net.Hpack Silmaril.Net.Http2

theorem validRequest_of_hasProtocol {fs : List Entry} (h : hasProtocol fs = true) :
    validRequest fs = false :=
  Silmaril.Proofs.Net.Http3.ExtendedConnect.validRequest_of_hasProtocol h

theorem validRequestExt_disabled (fs : List Entry) : validRequestExt false fs = validRequest fs :=
  Silmaril.Proofs.Net.Http3.ExtendedConnect.validRequestExt_disabled fs

theorem validExtendedConnect_disabled (fs : List Entry) : validExtendedConnect false fs = false := by
  simp [validExtendedConnect]

theorem validExtendedConnect_spec {en : Bool} {fs : List Entry}
    (h : validExtendedConnect en fs = true) :
    en = true ∧ pseudoValues fs ":method" = [ascii "CONNECT"] ∧ hasProtocol fs = true ∧
      (pseudoValues fs ":scheme").length = 1 ∧ (pseudoValues fs ":path").length = 1 :=
  Silmaril.Proofs.Net.Http3.ExtendedConnect.validExtendedConnect_spec h

theorem validRequest_stripProtocol {en : Bool} {fs : List Entry}
    (h : validExtendedConnect en fs = true) : validRequest (stripProtocol fs) = false :=
  Silmaril.Proofs.Net.Http3.ExtendedConnect.validRequest_stripProtocol h

theorem validRequestExt_of_not_hasProtocol {en : Bool} {fs : List Entry}
    (h : hasProtocol fs = false) : validRequestExt en fs = validRequest fs := by
  simp [validRequestExt, h]

/-! ## Examples, checked by evaluation -/

/-- The fields of a request from strings. -/
def connectFields (xs : List (String × String)) : List Entry :=
  xs.map fun (n, v) => Entry.ofStrings n v

/-- RFC 8441 §5.1 (WebSockets), the same in HTTP/3 (RFC 9220 §3). -/
def websocketRequest : List Entry := connectFields
  [(":method", "CONNECT"), (":protocol", "websocket"), (":scheme", "https"), (":path", "/chat"),
   (":authority", "server.example.com"), ("sec-websocket-protocol", "chat, superchat"),
   ("sec-websocket-extensions", "permessage-deflate"), ("sec-websocket-version", "13"),
   ("origin", "http://www.example.com")]

example : validExtendedConnect true websocketRequest = true := by decide +kernel
/-- Not without the server's SETTINGS_ENABLE_CONNECT_PROTOCOL. -/
example : validRequestExt false websocketRequest = false := by decide +kernel

/-- A plain CONNECT is unaffected by the extension. -/
example : validRequestExt true (connectFields [(":method", "CONNECT"),
    (":authority", "example.org:443")]) = true := by decide +kernel

/-- `:protocol` only with CONNECT. -/
example : validRequestExt true (connectFields [(":method", "GET"), (":protocol", "websocket"),
    (":scheme", "https"), (":path", "/chat")]) = false := by decide +kernel

/-- Extended CONNECT needs `:scheme` and `:path`. -/
example : validRequestExt true (connectFields [(":method", "CONNECT"),
    (":protocol", "websocket"), (":authority", "server.example.com")]) = false := by
  decide +kernel

/-- `:protocol` is single valued. -/
example : validRequestExt true (connectFields [(":method", "CONNECT"),
    (":protocol", "websocket"), (":protocol", "webtransport-h3"), (":scheme", "https"),
    (":path", "/chat")]) = false := by decide +kernel

end Silmaril.Net.Http3
