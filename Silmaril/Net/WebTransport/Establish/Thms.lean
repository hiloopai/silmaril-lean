module

public import Silmaril.Net.WebTransport.Establish.Defs
public import Silmaril.Net.Http3.ExtendedConnect.Thms

@[expose] public section

/-!
# WebTransport session establishment: theorems (draft-ietf-webtrans-http3-17)

PROVED (standard axioms; the proofs are short and inline):

* `validSessionRequest_extended`, `validSessionRequest_enabled`: a WebTransport session request
  is a valid extended CONNECT, and is only valid when the server sent
  `SETTINGS_ENABLE_CONNECT_PROTOCOL = 1` (§3.1, RFC 9220 §3);
* `validSessionRequest_not_plain`: it is never a valid plain request (RFC 9114 §4.3.1) — an
  HTTP/3 server without the extension rejects it as malformed;
* `ofParams_server`: a server ignores `SETTINGS_WT_ENABLED` from a client (§3.1);
  `ofParams_client_bad`: a client rejects a value above 1 with `H3_SETTINGS_ERROR`;
* `clientMayEstablish_spec`: a client only opens sessions once the server's SETTINGS and
  transport parameters meet every requirement of §3.1, and not after GOAWAY (§4.7);
* `flowControlEnabled_comm`: flow control is enabled symmetrically (§5.1);
  `admitSession_second`: without it, a second simultaneous session is `H3_REQUEST_REJECTED`.

CHECKED: a session request, the requests that miss each requirement, SETTINGS lists.
-/

namespace Silmaril.Net.WebTransport

open Silmaril.Net.Hpack Silmaril.Net.Http2 Silmaril.Net.Http3

theorem validSessionRequest_extended {en b : Bool} {fs : List Entry}
    (h : validSessionRequest en b fs = true) : validExtendedConnect en fs = true := by
  simp only [validSessionRequest, Bool.and_eq_true] at h; exact h.1.1.1.1

theorem validSessionRequest_enabled {en b : Bool} {fs : List Entry}
    (h : validSessionRequest en b fs = true) : en = true :=
  (validExtendedConnect_spec (validSessionRequest_extended h)).1

theorem validSessionRequest_not_plain {en b : Bool} {fs : List Entry}
    (h : validSessionRequest en b fs = true) : validRequest fs = false :=
  validRequest_of_hasProtocol (validExtendedConnect_spec (validSessionRequest_extended h)).2.2.1

theorem ofParams_server (ps : List (Nat × Nat)) :
    ∃ s, WtSettings.ofParams .server ps = .ok s ∧ s.enabled = false := ⟨_, rfl, rfl⟩

theorem ofParams_client_bad {ps : List (Nat × Nat)} {v : Nat}
    (hl : lookupParam ps settingWtEnabled = some v) (hv : 1 < v) :
    WtSettings.ofParams .client ps = .error .settingsError := by
  simp [WtSettings.ofParams, hl, show v ≠ 0 by omega, show v ≠ 1 by omega, Except.map]

theorem clientMayEstablish_spec {s : Option Advertised} {g : Bool}
    (h : clientMayEstablish s g = true) :
    ∃ a, s = some a ∧ serverRequirementsMet a = true ∧ g = false := by
  cases s <;> simp_all [clientMayEstablish]

theorem flowControlEnabled_comm (a b : WtSettings) :
    flowControlEnabled a b = flowControlEnabled b a := by
  simp [flowControlEnabled, Bool.and_comm]

theorem admitSession_second {n : Nat} (h : 1 ≤ n) :
    admitSession false n = .error .requestRejected := by
  simp [admitSession, h]

/-! ## Examples, checked by evaluation -/

/-- The fields of a request from strings. -/
def sessionFields (xs : List (String × String)) : List Entry :=
  xs.map fun (n, v) => Entry.ofStrings n v

/-- A browser's WebTransport session request (§3.2). -/
def sampleRequest : List Entry := sessionFields
  [(":method", "CONNECT"), (":protocol", "webtransport-h3"), (":scheme", "https"),
   (":authority", "example.com"), (":path", "/wt"), ("origin", "https://example.com")]

example : validSessionRequest true true sampleRequest = true := by decide +kernel
/-- Not before the server's SETTINGS_ENABLE_CONNECT_PROTOCOL. -/
example : validSessionRequest false true sampleRequest = false := by decide +kernel
/-- A browser must send `origin`. -/
example : validSessionRequest true true (sessionFields [(":method", "CONNECT"),
    (":protocol", "webtransport-h3"), (":scheme", "https"), (":authority", "example.com"),
    (":path", "/wt")]) = false := by decide +kernel
/-- `:scheme` must be `https`. -/
example : validSessionRequest true false (sessionFields [(":method", "CONNECT"),
    (":protocol", "webtransport-h3"), (":scheme", "http"), (":authority", "example.com"),
    (":path", "/wt")]) = false := by decide +kernel
/-- `:authority` must be set. -/
example : validSessionRequest true false (sessionFields [(":method", "CONNECT"),
    (":protocol", "webtransport-h3"), (":scheme", "https"), (":path", "/wt")]) = false := by
  decide +kernel
/-- Another upgrade token is not a WebTransport session. -/
example : validSessionRequest true false (sessionFields [(":method", "CONNECT"),
    (":protocol", "websocket"), (":scheme", "https"), (":authority", "example.com"),
    (":path", "/wt")]) = false := by decide +kernel

/-- A server's SETTINGS as read by a client. -/
example : WtSettings.ofParams .client [(0x08, 1), (0x33, 1), (0x20b8933b, 1), (0x2b65, 16),
    (0x2b61, 65536)] =
      .ok { enabled := true, initialMaxStreamsBidi := 16, initialMaxData := 65536 } := rfl

example : WtSettings.ofParams .client [(0x20b8933b, 2)] = .error .settingsError := rfl

/-- The HTTP/3 settings a WebTransport server sends (§3.1). -/
def sampleH3 : Http3.Settings := { enableConnectProtocol := true, h3Datagram := true }

/-- A server announcing everything §3.1 requires. -/
example : serverRequirementsMet
    ⟨sampleH3, { enabled := true }, { maxDatagramFrameSize := 65535, resetStreamAt := true }⟩ =
      true := by decide

/-- Without `reset_stream_at`, it does not qualify. -/
example : serverRequirementsMet
    ⟨sampleH3, { enabled := true }, { maxDatagramFrameSize := 65535 }⟩ = false := by decide

example : responseOutcome 200 = .established ∧ responseOutcome 302 = .redirect ∧
    responseOutcome 405 = .rejected := ⟨rfl, rfl, rfl⟩

end Silmaril.Net.WebTransport
