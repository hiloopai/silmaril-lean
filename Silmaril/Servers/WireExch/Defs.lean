module

public import Silmaril.Servers.Wire1.Defs
public import Silmaril.Servers.Http.Defs

/-!
# HTTP/1.1 exchanges: interim responses and close-delimited bodies

`Silmaril.Servers.Wire1` reads one response per request and so counts an interim (`1xx`)
response as the answer, and its round trips exclude close-delimited bodies. This module reads
whole **exchanges** (RFC 9110 §15.2, RFC 9112 §9.3, §6.3):

* after a request, any number of **interim** responses (`isInterim`: status `1xx` other than
  `101 Switching Protocols`, which ends the exchange because the connection changes protocol),
  then one **final** response (`parseExch`);
* a final response whose body is delimited by closing the connection (`BodyLength.close`,
  §6.3 rule 8) is complete only once the server has closed the connection: `closed` says
  whether it has; before that the exchange is not read.

`exchanges closed rs bs` reads the exchanges of a connection whose requests are `rs` and whose
sent octets are `bs`, as values of `Http.exchSig` (interim responses, final response);
`framingC closed` is the `Platform.Framing` of the final responses; `connLogX tr c` reads the
exchanges of connection `c` of a socket trace, closed when the trace has the server's `close`
of `c`.

The round trips are in `Thms`: exchanges whose interim responses are valid and bodiless, and
whose finals fit their framing, are read back (`exchanges_encode`); a last final response with
a close-delimited body is read back once the connection is closed (`exchanges_encode_close`)
and is not read before (`exchanges_encode_open`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Servers.WireExch

open Silmaril.Net Silmaril.Net.Http1 Silmaril.Servers.Wire1 Silmaril.Servers.Platform

/-- An interim response: `1xx` other than `101`. -/
def isInterim (m : WireResp) : Bool := m.1.line.code / 100 == 1 && m.1.line.code != 101

/-- A close-delimited body. -/
def isCloseBody : Http1.Body → Bool
  | .close _ => true
  | _ => false

/-- **One exchange's responses** at `i`, to a request with method `meth`: interim responses,
then the final one, and the position after it. Each interim response must advance; a final
response with a close-delimited body counts only if the connection is `closed`. -/
def parseExch (bs : ByteArray) (closed : Bool) (meth : List UInt8) :
    Nat → Nat → Option (List WireResp × WireResp × Nat)
  | 0, _ => none
  | fuel + 1, i =>
    match parseResponseAt meth bs i with
    | .err _ => none
    | .ok m k =>
      if isInterim m then
        if i < k then (parseExch bs closed meth fuel k).map fun r => (m :: r.1, r.2)
        else none
      else if isCloseBody m.2 && !closed then none
      else some ([], m, k)

/-- The exchanges at `i`, one per request method, stopping at the first incomplete one. -/
def parseExchs (bs : ByteArray) (closed : Bool) : List (List UInt8) → Nat → List (List WireResp × WireResp)
  | [], _ => []
  | meth :: ms, i =>
    match parseExch bs closed meth (bs.size + 1) i with
    | some (is, f, k) => (is, f) :: parseExchs bs closed ms k
    | none => []

/-- **The exchanges of a connection**: interim and final responses to the requests `rs`, from
the sent octets `bs`. -/
def exchanges (closed : Bool) (rs : List Http.Request) (bs : List UInt8) :
    List (List Http.Response × Http.Response) :=
  (parseExchs ⟨bs.toArray⟩ closed (rs.map fun r => r.method.toToken) 0).map
    fun x => (x.1.map toResponse, toResponse x.2)

/-- **The HTTP/1.1 framing with interim responses skipped**: the final responses. -/
def framingC (closed : Bool) : Framing :=
  ⟨requests, fun rs bs => (exchanges closed rs bs).map Prod.snd⟩

/-- Whether the server closed connection `c` in a socket trace. -/
def closedOn (c : ConnId) (tr : List SockEv) : Bool := tr.contains (.close c)

/-- **The exchanges of a connection of a socket trace**, interim responses included. -/
def connLogX (tr : List SockEv) (c : ConnId) : List (Http.Request × (List Http.Response × Http.Response)) :=
  let rs := requests (received c tr)
  rs.zip (exchanges (closedOn c tr) rs (sent c tr))

/-- The octets of an exchange's responses. -/
def encExch (x : List WireResp × WireResp) : List UInt8 := encResponses x.1 ++ encResponse x.2.1 x.2.2

/-- The octets of exchanges back to back. -/
def encExchs (xs : List (List WireResp × WireResp)) : List UInt8 := xs.flatMap encExch

/-- An interim response that reads back: valid, interim, no body. -/
def InterimOk (m : WireResp) : Prop := m.1.Valid ∧ isInterim m = true ∧ m.2 = .none

/-- An exchange that reads back after a request with method `meth`: its interim responses
read back and its final response is not interim and fits its framing. -/
def ExchOk (meth : List UInt8) (x : List WireResp × WireResp) : Prop :=
  (∀ m ∈ x.1, InterimOk m) ∧ isInterim x.2 = false ∧ RespOk meth x.2

/-- A final response delimited by closing the connection: a valid, non-interim head whose
framing after `meth` is `close`, and a close-delimited body. -/
def CloseOk (meth : List UInt8) (m : WireResp) : Prop :=
  m.1.Valid ∧ isInterim m = false ∧
    responseBodyLength meth m.1.line.code m.1.fields = .close ∧ ∃ b, m.2 = .close b

end Silmaril.Servers.WireExch
