module

public import Silmaril.Servers.Wire1.Defs
public import Mathlib.Data.List.Forall2
import Silmaril.Proofs.Servers.Wire1.Basic

/-!
# HTTP/1.1 framing of a connection: round trips

PROVED (standard axioms):

* `toToken_ofToken`, `method_toRequest`: the method of a wire request, read and written back,
  is the token sent.
* **`requests_encode`**: requests sent back to back on a connection, each with a valid head and
  a body fitting the framing it announces, are framed back into exactly those requests.
* **`responses_encode`**: responses sent back to back, each valid and fitting the framing its
  head announces after its request's method, are framed back into exactly those responses.
* **`connLog_encode`**: the exchanges of a connection whose received and sent octets are such
  encodings are the requests paired with the responses, in order.
-/

@[expose] public section

namespace Silmaril.Servers.Wire1

open Silmaril.Net Silmaril.Net.Http1 Silmaril.Servers.Platform

theorem toToken_ofToken (t : List UInt8) : (Http.Method.ofToken t).toToken = t :=
  Proofs.Servers.Wire1.toToken_ofToken t

theorem method_toRequest (m : WireReq) : (toRequest m).method.toToken = m.1.line.method :=
  toToken_ofToken _

/-- **Round trip of the requests of a connection.** -/
theorem requests_encode (ms : List WireReq) (hv : ∀ m ∈ ms, ReqOk m) :
    requests (encRequests ms) = ms.map toRequest := by
  have := Proofs.Servers.Wire1.parseRequests_encode ms [] _ hv
    (Nat.le_succ_of_le (Proofs.Servers.Wire1.length_le_encRequests ms))
  simp only [List.nil_append, List.length_nil] at this
  simp only [requests, this]

/-- **Round trip of the responses of a connection**, to the requests `rs` in order. -/
theorem responses_encode (rs : List Http.Request) (ms : List WireResp)
    (hf : List.Forall₂ (fun r m => RespOk r.method.toToken m) rs ms) :
    responses rs (encResponses ms) = ms.map toResponse := by
  have := Proofs.Servers.Wire1.parseResponses_encode (List.forall₂_map_left_iff.mpr hf) []
  simp only [List.nil_append, List.length_nil] at this
  simp only [responses, this]

/-- **The exchanges of an encoded connection**: on a connection that received the requests
`ms` and sent the responses `xs`, back to back, the exchanges are the pairs, in order. -/
theorem connLog_encode {tr : List SockEv} {c : ConnId} {ms : List WireReq}
    {xs : List WireResp} (hr : received c tr = encRequests ms)
    (hs : sent c tr = encResponses xs) (hv : ∀ m ∈ ms, ReqOk m)
    (hx : List.Forall₂ (fun r m => RespOk r.method.toToken m) (ms.map toRequest) xs) :
    connLog framing tr c = (ms.map toRequest).zip (xs.map toResponse) := by
  show (requests (received c tr)).zip (responses (requests (received c tr)) (sent c tr)) = _
  rw [hr, hs, requests_encode ms hv, responses_encode _ _ hx]

end Silmaril.Servers.Wire1
