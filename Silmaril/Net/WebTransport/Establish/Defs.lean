module

public import Silmaril.Net.Http3.ExtendedConnect.Defs
public import Silmaril.Net.Http3.Datagram.Defs

@[expose] public section

/-!
# WebTransport over HTTP/3: session establishment (draft-ietf-webtrans-http3-17 §3, §4.6,
§4.7, §5.1, §5.2, §5.5, §9.2)

Codepoints are those of draft -17 (in WG Last Call, not an RFC) and may change before RFC
publication. Earlier drafts' codepoints, and the draft-version negotiation of §7.1 (which the
RFC editor is to remove), are not modelled.

**Settings (§3.1, §5.5, §9.2).** `SETTINGS_WT_ENABLED` (`0x20b8933b`, default 0),
`SETTINGS_WT_INITIAL_MAX_STREAMS_UNI` (`0x2b64`), `SETTINGS_WT_INITIAL_MAX_STREAMS_BIDI`
(`0x2b65`) and `SETTINGS_WT_INITIAL_MAX_DATA` (`0x2b61`), all default 0, read from the raw
SETTINGS list (`Silmaril.Net.Http3.decodeParams`, which already rejects duplicates).
"Clients MUST treat values greater than '1' as a connection error of type H3_SETTINGS_ERROR.
… SETTINGS_WT_ENABLED has no meaning when sent by a client; a server MUST ignore it."

**Requirements (§3.1).** "In summary, servers supporting WebTransport over HTTP/3 send: A
SETTINGS_WT_ENABLED setting with a value of '1'; A SETTINGS_ENABLE_CONNECT_PROTOCOL setting with
a value of '1'; A SETTINGS_H3_DATAGRAM setting with a value of 1; A max_datagram_frame_size
transport parameter with a value greater than 0; An empty reset_stream_at transport parameter.
Clients supporting WebTransport over HTTP/3 send: A SETTINGS_H3_DATAGRAM setting with a value of
1; A max_datagram_frame_size transport parameter with a value greater than 0; An empty
reset_stream_at transport parameter." (`serverRequirementsMet`, `clientRequirementsMet`.) "A
client MUST NOT establish WebTransport sessions if the server's SETTINGS do not have correct
values for every required setting" and must wait for them (§4.6); after GOAWAY it "cannot
initiate CONNECT requests for new WebTransport sessions on that HTTP/3 connection" (§4.7):
`clientMayEstablish`.

**The CONNECT request (§3.2).** "The :protocol pseudo-header field ([RFC8441]) MUST be set to
webtransport-h3. The :scheme field MUST be https. Both the :authority and the :path value MUST be
set … If the WebTransport session is coming from a browser client, an Origin header [RFC6454]
MUST be provided": `validSessionRequest`, on top of `Http3.validExtendedConnect`. "From the
client's perspective, a WebTransport session is established when the client receives a 2xx
response"; a 3xx is not followed: `responseOutcome`.

**Flow control negotiation (§5.1, §5.2).** Flow control is enabled when both endpoints send a
non-zero value for one of the three initial-limit settings (`flowControlEnabled`). "If flow
control is not enabled, clients MUST NOT attempt to establish more than one simultaneous
WebTransport session. A server that receives more than one session … MUST reset the excessive
CONNECT streams with a H3_REQUEST_REJECTED status": `admitSession`.

**Assumed (abstract).** The QUIC transport parameters are inputs (`TransportParams`); TLS,
RESET_STREAM_AT itself, application protocol negotiation (§3.3, Structured Fields), priorities
(§3.4) and keying material exporters (§4.8) are not modelled.
-/

namespace Silmaril.Net.WebTransport

open Silmaril.Net.Hpack Silmaril.Net.Http2 Silmaril.Net.Http3

def settingWtEnabled : Nat := 0x20b8933b
def settingWtInitialMaxStreamsUni : Nat := 0x2b64
def settingWtInitialMaxStreamsBidi : Nat := 0x2b65
def settingWtInitialMaxData : Nat := 0x2b61

/-- The `webtransport-h3` upgrade token (§9.1). -/
def upgradeToken : String := "webtransport-h3"

/-- Which end of the HTTP/3 connection. -/
inductive Role where
  | client
  | server
  deriving DecidableEq, Repr, Inhabited

/-- The WebTransport settings of one endpoint, with their defaults. -/
structure WtSettings where
  /-- `SETTINGS_WT_ENABLED = 1` (meaningful from a server only). -/
  enabled : Bool := false
  initialMaxStreamsUni : Nat := 0
  initialMaxStreamsBidi : Nat := 0
  initialMaxData : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- The peer's WebTransport settings, read by an endpoint of role `receiver` from the peer's
SETTINGS parameters (§3.1, §5.5). -/
def WtSettings.ofParams (receiver : Role) (ps : List (Nat × Nat)) :
    Except Http3.ErrorCode WtSettings :=
  let enabled : Except Http3.ErrorCode Bool :=
    match receiver with
    | .server => .ok false
    | .client =>
      match lookupParam ps settingWtEnabled with
      | none => .ok false
      | some v => if v = 0 then .ok false else if v = 1 then .ok true else .error .settingsError
  enabled.map fun e =>
    { enabled := e
      initialMaxStreamsUni := (lookupParam ps settingWtInitialMaxStreamsUni).getD 0
      initialMaxStreamsBidi := (lookupParam ps settingWtInitialMaxStreamsBidi).getD 0
      initialMaxData := (lookupParam ps settingWtInitialMaxData).getD 0 }

/-- The QUIC transport parameters WebTransport needs (RFC 9221 §3; draft-ietf-quic-reliable-
stream-reset §3). -/
structure TransportParams where
  maxDatagramFrameSize : Nat := 0
  /-- The (empty) `reset_stream_at` transport parameter was sent. -/
  resetStreamAt : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- What one endpoint announced: its HTTP/3 SETTINGS, WebTransport settings and transport
parameters. -/
structure Advertised where
  h3 : Http3.Settings := {}
  wt : WtSettings := {}
  tp : TransportParams := {}
  deriving DecidableEq, Repr, Inhabited

/-- The requirements a server's announcements must meet (§3.1). -/
def serverRequirementsMet (a : Advertised) : Bool :=
  a.wt.enabled && a.h3.enableConnectProtocol && a.h3.h3Datagram &&
    quicDatagramsSupported a.tp.maxDatagramFrameSize && a.tp.resetStreamAt

/-- The requirements a client's announcements must meet (§3.1). -/
def clientRequirementsMet (a : Advertised) : Bool :=
  a.h3.h3Datagram && quicDatagramsSupported a.tp.maxDatagramFrameSize && a.tp.resetStreamAt

/-- A client may send a WebTransport CONNECT: it has the server's SETTINGS (§4.6), they meet the
requirements (§3.1), and no GOAWAY has been received (§4.7). -/
def clientMayEstablish (server : Option Advertised) (goawayReceived : Bool) : Bool :=
  match server with
  | none => false
  | some a => serverRequirementsMet a && !goawayReceived

/-- The server treats WebTransport sessions as malformed once the client's SETTINGS (or
transport parameters) arrive without the required values (§3.1). -/
def serverRejectsSessions (client : Option Advertised) : Bool :=
  match client with
  | none => false
  | some a => !clientRequirementsMet a

/-! ## The extended CONNECT request (§3.2) -/

/-- A WebTransport session request, sent to a server whose `SETTINGS_ENABLE_CONNECT_PROTOCOL` is
`enabled`: a valid extended CONNECT (RFC 9220) with `:protocol = webtransport-h3`,
`:scheme = https`, a non-empty `:authority` and `:path`, and an `origin` field if the client is
a browser. -/
def validSessionRequest (enabled fromBrowser : Bool) (fs : List Entry) : Bool :=
  validExtendedConnect enabled fs &&
    pseudoValues fs ":protocol" == [ascii upgradeToken] &&
    pseudoValues fs ":scheme" == [ascii "https"] &&
    (match pseudoValues fs ":authority" with
     | [a] => !a.isEmpty
     | _ => false) &&
    (!fromBrowser || fs.any (·.name == ascii "origin"))

/-- What a response to a session request means for the client (§3.2). -/
inductive ResponseOutcome where
  /-- 2xx: the session is established (and the Capsule Protocol is in use). -/
  | established
  /-- 3xx: a redirect, which "The WebTransport client MUST NOT automatically follow". -/
  | redirect
  /-- Anything else: the session is rejected (e.g. 403 failed origin check, 405 resource does
  not support WebTransport, 429 rate limited, 501 unsupported protocol). -/
  | rejected
  deriving DecidableEq, Repr

def responseOutcome (status : Nat) : ResponseOutcome :=
  if 200 ≤ status && status < 300 then .established
  else if 300 ≤ status && status < 400 then .redirect
  else .rejected

/-! ## Flow control negotiation (§5.1, §5.2) -/

/-- An endpoint declares its intent to use flow control by sending a non-zero initial limit. -/
def WtSettings.declaresFlowControl (s : WtSettings) : Bool :=
  s.initialMaxStreamsUni != 0 || s.initialMaxStreamsBidi != 0 || s.initialMaxData != 0

/-- "If both endpoints take at least one of these actions, flow control is enabled". -/
def flowControlEnabled (a b : WtSettings) : Bool := a.declaresFlowControl && b.declaresFlowControl

/-- Whether a server admits one more session when `active` sessions are open: without flow
control, only one (§5.1: "MUST reset the excessive CONNECT streams with a H3_REQUEST_REJECTED"). -/
def admitSession (flowControl : Bool) (active : Nat) : Except Http3.ErrorCode Unit :=
  if !flowControl && 1 ≤ active then .error .requestRejected else .ok ()

end Silmaril.Net.WebTransport
