module

public import Silmaril.Net.WebSocket.Handshake.Defs
public import Silmaril.Net.Http1.Fields.Thms
public import Silmaril.Crypto.SHA1.Thms

@[expose] public section

/-!
# The WebSocket opening handshake: theorems

PROVED (standard axioms):

* `checkResponse_respond`: **the server's response passes the client's checks** (§4.1,
  §4.2.2): for every offer and every selection among the offered subprotocols (or none), the
  client accepts `respond` and learns the selection.
* `checkResponse_sound`: what the client accepts has status 101, exactly one
  `Sec-WebSocket-Accept` equal to `acceptOf key`, and a subprotocol among those offered.
* `readOffer_clientRequest`: **the server reads back what the client sent**: for a valid key
  and subprotocols that are tokens (RFC 6455 §4.1 item 10; through
  `Http1.flatMap_listElements_tokens`), `readOffer (clientRequest o) = .ok o`.
* `readOffer_sound`: an offer the server accepts has a key that decodes to 16 octets.

CHECKED by the kernel: the RFC 6455 §1.3/§4.2.2 example (`Sec-WebSocket-Key:
dGhlIHNhbXBsZSBub25jZQ==` gives `Sec-WebSocket-Accept: s3pPLMBiTxaQ9kYGzzhZRbK+xOo=`), and the
example key is a valid 16-octet nonce. The end-to-end run over the HTTP/1.1 parser and
serializer is in `Silmaril.Net.WebSocket.Examples`.
-/

namespace Silmaril.Net.WebSocket.Handshake

open Silmaril.Net.Http1

theorem tok_websocket :
    (listElements (ascii "websocket")).any
      (fun e => lower e == lower (ascii "websocket")) = true := by
  decide +kernel
theorem tok_upgrade :
    (listElements (ascii "Upgrade")).any (fun e => lower e == lower (ascii "Upgrade")) = true := by
  decide +kernel

section respond

variable (o : Offer) (sel : Option (List UInt8))

theorem values_respond_upgrade :
    fieldValues (respond o sel).fields (ascii "Upgrade") = [ascii "websocket"] := by
  cases sel <;> rfl
theorem values_respond_connection :
    fieldValues (respond o sel).fields (ascii "Connection") = [ascii "Upgrade"] := by
  cases sel <;> rfl
theorem values_respond_accept :
    fieldValues (respond o sel).fields (ascii "Sec-WebSocket-Accept") = [acceptOf o.key] := by
  cases sel <;> rfl
theorem values_respond_extensions :
    fieldValues (respond o sel).fields (ascii "Sec-WebSocket-Extensions") = [] := by
  cases sel <;> rfl
theorem values_respond_protocol :
    fieldValues (respond o sel).fields (ascii "Sec-WebSocket-Protocol") = sel.toList := by
  cases sel <;> rfl

end respond

theorem checkResponse_respond (o : Offer) (sel : Option (List UInt8))
    (hs : ∀ p, sel = some p → o.protocols.contains p = true) :
    checkResponse o.key o.protocols (respond o sel) = .ok sel := by
  have hcode : (respond o sel).line.code = 101 := rfl
  simp only [checkResponse, fieldHasToken, fieldElements, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, hcode, values_respond_upgrade, values_respond_connection,
    values_respond_accept, values_respond_extensions, values_respond_protocol,
    tok_websocket, tok_upgrade,
    bne_self_eq_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.isEmpty_nil]
  cases sel with
  | none => rfl
  | some p =>
    have := hs p rfl
    simp only [Option.toList_some, this, ↓reduceIte]

theorem checkResponse_sound {key : List UInt8} {offered : List (List UInt8)} {r : ResponseHead}
    {sel : Option (List UInt8)} (h : checkResponse key offered r = .ok sel) :
    r.line.code = 101 ∧ fieldValues r.fields (ascii "Sec-WebSocket-Accept") = [acceptOf key] ∧
      ∀ p, sel = some p → p ∈ offered := by
  unfold checkResponse at h
  by_cases hc : r.line.code = 101
  swap; · simp [hc] at h
  by_cases hu : fieldHasToken r.fields (ascii "Upgrade") (ascii "websocket") = true
  swap; · simp [hc, hu] at h
  by_cases hn : fieldHasToken r.fields (ascii "Connection") (ascii "Upgrade") = true
  swap; · simp [hc, hu, hn] at h
  by_cases ha : fieldValues r.fields (ascii "Sec-WebSocket-Accept") = [acceptOf key]
  swap; · simp [hc, hu, hn, ha] at h
  by_cases he : (fieldValues r.fields (ascii "Sec-WebSocket-Extensions")).isEmpty = true
  swap; · simp [hc, hu, hn, ha, he] at h
  simp only [hc, hu, hn, ha, he, bne_self_eq_false, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte] at h
  refine ⟨hc, ha, ?_⟩
  intro p hp
  subst hp
  split at h
  · cases h
  · split at h
    · next hm => cases h; simpa using hm
    · cases h
  · cases h

theorem readOffer_sound {h : RequestHead} {o : Offer} (hr : readOffer h = .ok o) :
    validKey o.key = true ∧ h.line.method = ascii "GET" := by
  unfold readOffer at hr
  by_cases hm : h.line.method = ascii "GET"
  swap; · simp [hm] at hr
  refine ⟨?_, hm⟩
  simp only [hm, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hr
  split at hr
  · cases hr
  · split at hr
    · split at hr
      · cases hr
      · split at hr
        · cases hr
        · split at hr
          · next key _ =>
            by_cases hk : validKey key = true
            · simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hr
              split at hr
              · cases hr
              · cases hr; exact hk
            · simp [hk] at hr
          · cases hr
    · cases hr

/-- The fixed fields of `clientRequest`. -/
def fixedFields (o : Offer) : List FieldLine :=
  [⟨ascii "Host", o.host⟩, ⟨ascii "Upgrade", ascii "websocket"⟩,
   ⟨ascii "Connection", ascii "Upgrade"⟩, ⟨ascii "Sec-WebSocket-Key", o.key⟩,
   ⟨ascii "Sec-WebSocket-Version", ascii "13"⟩]

theorem values_clientRequest (o : Offer) (n : List UInt8)
    (hn : lower (ascii "Sec-WebSocket-Protocol") ≠ lower n) :
    fieldValues (clientRequest o).fields n = fieldValues (fixedFields o) n := by
  simp only [clientRequest, fieldValues, List.filterMap_append, List.filterMap_map,
    fixedFields]
  have : (List.filterMap ((fun f : FieldLine => if lower f.name = lower n then
      some f.value else none) ∘ fun p => (⟨ascii "Sec-WebSocket-Protocol", p⟩ : FieldLine))
      o.protocols) = [] := by
    simp [hn]
  rw [this, List.append_nil]

theorem values_clientRequest_protocol (o : Offer) :
    fieldValues (clientRequest o).fields (ascii "Sec-WebSocket-Protocol") = o.protocols := by
  simp only [clientRequest, fieldValues, List.filterMap_append, List.filterMap_map]
  have h1 : List.filterMap (fun f : FieldLine =>
      if lower f.name = lower (ascii "Sec-WebSocket-Protocol") then some f.value else none)
      (fixedFields o) = [] := rfl
  simp only [fixedFields] at h1
  rw [h1]
  simp

theorem readOffer_clientRequest (o : Offer) (hk : validKey o.key = true)
    (hp : ∀ p ∈ o.protocols, IsToken p) : readOffer (clientRequest o) = .ok o := by
  have eH : fieldValues (clientRequest o).fields (ascii "Host") = [o.host] :=
    (values_clientRequest o (ascii "Host") (by decide)).trans rfl
  have eU : fieldValues (clientRequest o).fields (ascii "Upgrade") = [ascii "websocket"] :=
    (values_clientRequest o (ascii "Upgrade") (by decide)).trans rfl
  have eC : fieldValues (clientRequest o).fields (ascii "Connection") = [ascii "Upgrade"] :=
    (values_clientRequest o (ascii "Connection") (by decide)).trans rfl
  have eK : fieldValues (clientRequest o).fields (ascii "Sec-WebSocket-Key") = [o.key] :=
    (values_clientRequest o (ascii "Sec-WebSocket-Key") (by decide)).trans rfl
  have eV : fieldValues (clientRequest o).fields (ascii "Sec-WebSocket-Version") = [ascii "13"] :=
    (values_clientRequest o (ascii "Sec-WebSocket-Version") (by decide)).trans rfl
  have hv : (clientRequest o).line.version = Version.http11 := rfl
  have hm : (clientRequest o).line.method = ascii "GET" := rfl
  simp only [readOffer, fieldHasToken, fieldElements, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, eH, eU, eC, eK, eV, values_clientRequest_protocol,
    flatMap_listElements_tokens hp, hk, hv, hm, tok_websocket,
    tok_upgrade, bne_self_eq_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    show (decide (Version.http11.major > 1) || Version.http11.major == 1 &&
      decide (1 ≤ Version.http11.minor)) = true by decide]
  rfl

/-! ## RFC 6455 examples -/

/-- §1.3, §4.2.2: the example key and accept value. -/
theorem accept_rfc6455 :
    acceptOf (ascii "dGhlIHNhbXBsZSBub25jZQ==") = ascii "s3pPLMBiTxaQ9kYGzzhZRbK+xOo=" := by
  decide +kernel

/-- The example key is the base64 encoding of a 16-octet nonce (`the sample nonce`). -/
theorem validKey_rfc6455 : validKey (ascii "dGhlIHNhbXBsZSBub25jZQ==") = true := by
  decide +kernel

/-- A key that encodes 15 octets is refused (§4.1 item 7). -/
example : validKey (ascii "dGhlIHNhbXBsZSBub25jZQ") = false := by decide +kernel

end Silmaril.Net.WebSocket.Handshake
