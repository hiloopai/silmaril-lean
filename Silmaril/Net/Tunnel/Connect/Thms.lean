module

public import Silmaril.Net.Tunnel.Connect.Defs

@[expose] public section

/-!
# CONNECT and extended CONNECT: theorems

PROVED (standard axioms):

* `extended_requires_setting`: without `SETTINGS_ENABLE_CONNECT_PROTOCOL = 1` from the peer, no
  section is a valid extended CONNECT (RFC 8441 §3);
* `applyEnableConnect_sticky`: once enabled, the setting stays enabled or the connection
  fails with `PROTOCOL_ERROR` (RFC 8441 §3);
* `extended_not_classic`: **an extended CONNECT is malformed to an endpoint without RFC 8441**:
  it fails the RFC 9113 request rules of the HTTP/2 track (`Http2.validRequest`), because
  `:protocol` is an unknown pseudo-header field there (RFC 9113 §8.3). An old server rejects it
  instead of opening a plain tunnel, which is why RFC 8441 needs no new error handling;
* `websocket_is_extended`: a WebSocket bootstrap is an extended CONNECT;
* `validExtendedConnect_http3`: this module's (sender-side, stricter) rule implies the HTTP/3
  track's `Http3.validExtendedConnect`, so what this track builds is accepted there;
  `settingEnableConnectProtocol_eq`: both tracks use identifier 0x08.

CHECKED (`decide`): the RFC 8441 §5.1 request and response; authority-form targets.
-/

namespace Silmaril.Net.Tunnel

open Silmaril.Net.Hpack (ascii Entry)
open Silmaril.Net.Http2

theorem extended_requires_setting (fs : List Entry) : validExtendedConnect false fs = false := rfl

theorem applyEnableConnect_sticky {v : Nat} {b : Bool} (h : applyEnableConnect true v = .ok b) :
    b = true := by
  unfold applyEnableConnect at h
  split at h
  · cases h; rfl
  · split at h <;> simp at h

theorem mem_of_pseudoValues {fs : List Entry} {n : String} {v : List UInt8}
    (h : v ∈ pseudoValues fs n) : (⟨ascii n, v⟩ : Entry) ∈ fs := by
  simp only [pseudoValues, List.mem_map, List.mem_filter, beq_iff_eq] at h
  obtain ⟨e, ⟨he, hn⟩, rfl⟩ := h
  rw [← hn]
  exact he

theorem extended_not_classic {b : Bool} {fs : List Entry} (h : validExtendedConnect b fs = true) :
    validRequest fs = false := by
  simp only [validExtendedConnect, Bool.and_eq_true, beq_iff_eq] at h
  have hp : (pseudoValues fs ":protocol").length = 1 := h.1.1.1.1.2
  obtain ⟨v, hv⟩ : ∃ v, v ∈ pseudoValues fs ":protocol" := by
    match hq : pseudoValues fs ":protocol" with
    | [v] => exact ⟨v, by simp⟩
    | [] | _ :: _ :: _ => rw [hq] at hp; simp at hp
  have hmem := mem_of_pseudoValues hv
  have hk : pseudoKnownOnce requestPseudo fs = false := by
    simp only [pseudoKnownOnce, Bool.and_eq_false_iff]
    left
    simp only [List.all_eq_false, List.mem_map, List.mem_filter]
    refine ⟨ascii ":protocol", ⟨⟨ascii ":protocol", v⟩, ⟨hmem, rfl⟩, rfl⟩, by decide⟩
  simp [validRequest, validSection, hk]

theorem websocket_is_extended {b : Bool} {fs : List Entry}
    (h : validWebSocketRequest b fs = true) : validExtendedConnect b fs = true := by
  simp only [validWebSocketRequest, Bool.and_eq_true] at h
  exact h.1.1

theorem settingEnableConnectProtocol_eq : settingEnableConnectProtocol = 0x08 := rfl

theorem validExtendedConnect_http3 {b : Bool} {fs : List Entry}
    (h : validExtendedConnect b fs = true) : Silmaril.Net.Http3.validExtendedConnect b fs = true := by
  simp only [validExtendedConnect, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hb, hs⟩, hm⟩, hpr⟩, -⟩, hsc⟩, hpa⟩, hall⟩ := h
  unfold Silmaril.Net.Http3.validExtendedConnect
  simp only [hb, hs, hm, Bool.true_and, beq_self_eq_true]
  match hq : pseudoValues fs ":protocol", hq2 : pseudoValues fs ":scheme",
      hq3 : pseudoValues fs ":path", hpa with
  | [pr], [s], [p], hpa =>
    rw [hq] at hall
    simp only [List.all_cons, List.all_nil, Bool.and_true] at hall
    simp only [Bool.not_eq_true'] at hpa
    simp [hall] at hpa ⊢
    exact Or.inr hpa
  | [], _, _, _ | _ :: _ :: _, _, _, _ => rw [hq] at hpr; simp at hpr
  | [_], [], _, _ | [_], _ :: _ :: _, _, _ => rw [hq2] at hsc; simp at hsc
  | [_], [_], [], hpa | [_], [_], _ :: _ :: _, hpa => simp at hpa

/-! ## Examples -/

example : validWebSocketRequest true rfc8441Request = true := by decide
example : validWebSocketRequest false rfc8441Request = false := by decide
example : validRequest rfc8441Request = false := by decide
example : tunnelAccepted rfc8441Response = true := by decide
/-- An empty `:protocol` is not an upgrade token. -/
example : validExtendedConnect true [⟨ascii ":method", ascii "CONNECT"⟩, ⟨ascii ":protocol", []⟩,
    ⟨ascii ":scheme", ascii "https"⟩, ⟨ascii ":path", ascii "/"⟩,
    ⟨ascii ":authority", ascii "a"⟩] = false := by
  decide

/-- A classic HTTP/2 CONNECT (RFC 9113 §8.5) is valid there and is not extended. -/
example : validRequest [⟨ascii ":method", ascii "CONNECT"⟩,
    ⟨ascii ":authority", ascii "server.example.com:443"⟩] = true ∧
    validExtendedConnect true [⟨ascii ":method", ascii "CONNECT"⟩,
    ⟨ascii ":authority", ascii "server.example.com:443"⟩] = false := by
  decide

/-- RFC 9110 §9.3.6: `CONNECT server.example.com:80 HTTP/1.1`. -/
example : isAuthorityForm (ascii "server.example.com:80") = true := by decide
example : isAuthorityForm (ascii "server.example.com") = false := by decide
example : isAuthorityForm (ascii "/index.html") = false := by decide

example : connectResponseOk 200 [ascii "content-length"] = false ∧
    connectResponseOk 407 [ascii "content-length"] = true := by
  decide

end Silmaril.Net.Tunnel
