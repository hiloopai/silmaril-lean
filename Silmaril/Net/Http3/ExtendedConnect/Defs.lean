module

public import Silmaril.Net.Http2.Fields.Defs

@[expose] public section

/-!
# Extended CONNECT (RFC 8441 §4, RFC 9220 §3)

RFC 8441 §4 extends CONNECT for HTTP/2, and RFC 9220 §3 carries it to HTTP/3: "The semantics
of the pseudo-header fields and setting are identical to those in HTTP/2 as defined in
[RFC8441]. … The SETTINGS_ENABLE_CONNECT_PROTOCOL value is 0x08 (decimal 8), as in HTTP/2."
The extension:

* "A new pseudo-header field :protocol MAY be included on request HEADERS indicating the
  desired protocol to be spoken on the tunnel created by CONNECT. The pseudo-header field is
  single valued and contains a value from the 'Hypertext Transfer Protocol (HTTP) Upgrade Token
  Registry'" (RFC 8441 §4);
* "On requests that contain the :protocol pseudo-header field, the :scheme and :path
  pseudo-header fields of the target URI … MUST also be included." (§4) Plain CONNECT omits
  them (RFC 9113 §8.5, RFC 9114 §4.4);
* the `:authority` field is then read as in an ordinary request (RFC 9113 §8.3.1), not as the
  tunnel's destination;
* "Upon receipt of SETTINGS_ENABLE_CONNECT_PROTOCOL with a value of 1, a client MAY use the
  Extended CONNECT" (RFC 8441 §3); without it, "a non-supporting peer would detect a malformed
  request".

HTTP/3's request pseudo-header rules (RFC 9114 §4.3.1, §4.4) are those of HTTP/2 (RFC 9113
§8.3.1, §8.5), so the plain rules are `Silmaril.Net.Http2.validRequest` over decoded field
lists (`Silmaril.Net.Hpack.Entry`; QPACK decodes to the same name/value pairs). This module adds:

* `validExtendedConnect enabled fs`: a well-formed extended CONNECT request, given whether the
  server sent `SETTINGS_ENABLE_CONNECT_PROTOCOL = 1` (`enabled`; see
  `Silmaril.Net.Http3.Settings.enableConnectProtocol`);
* `validRequestExt enabled fs`: the request rule of an endpoint implementing the extension:
  extended CONNECT when `:protocol` is present, the plain rules otherwise.

The protocol value is checked to be non-empty; that it names a registered upgrade token (and
the 501 answer for unsupported ones, RFC 9220 §3) is the server's business.
-/

namespace Silmaril.Net.Http3

open Silmaril.Net.Hpack Silmaril.Net.Http2

/-- The pseudo-header fields allowed in an extended CONNECT request. -/
def extendedConnectPseudo : List (List UInt8) := requestPseudo ++ [ascii ":protocol"]

/-- The request carries a `:protocol` pseudo-header field. -/
def hasProtocol (fs : List Entry) : Bool := !(pseudoValues fs ":protocol").isEmpty

/-- A well-formed extended CONNECT request (RFC 8441 §4, RFC 9220 §3), sent to a server that
announced `SETTINGS_ENABLE_CONNECT_PROTOCOL = 1` (`enabled`): `:method` is CONNECT, exactly one
non-empty `:protocol`, `:scheme` and `:path` present (with a non-empty path for `http` and
`https`, RFC 9113 §8.3.1), `:authority` at most once, and the field rules of RFC 9113 §8.2–§8.3
(through `Http2.validSection`). -/
def validExtendedConnect (enabled : Bool) (fs : List Entry) : Bool :=
  enabled && validSection extendedConnectPseudo fs &&
    pseudoValues fs ":method" == [ascii "CONNECT"] &&
    match pseudoValues fs ":protocol", pseudoValues fs ":scheme", pseudoValues fs ":path" with
    | [pr], [s], [p] => !pr.isEmpty && !((s == ascii "http" || s == ascii "https") && p.isEmpty)
    | _, _, _ => false

/-- The request rule of an endpoint implementing extended CONNECT: a request with `:protocol`
must be a valid extended CONNECT; any other request follows the plain rules. -/
def validRequestExt (enabled : Bool) (fs : List Entry) : Bool :=
  if hasProtocol fs then validExtendedConnect enabled fs else validRequest fs

/-- The request with its `:protocol` field removed (the plain CONNECT a non-supporting peer
might mistake it for). -/
def stripProtocol (fs : List Entry) : List Entry :=
  fs.filter fun e => e.name != ascii ":protocol"

end Silmaril.Net.Http3
