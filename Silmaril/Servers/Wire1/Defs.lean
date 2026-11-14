module

public import Silmaril.Servers.Platform.Defs
public import Silmaril.Net.Http1.Framing.Defs

/-!
# HTTP/1.1 framing of a connection, as a `Platform.Framing`

The instance of `Silmaril.Servers.Platform.Framing` given by the HTTP/1.1 message syntax and
framing of `Silmaril.Net.Http1` (RFC 9112):

* `toRequest`, `toResponse` read a wire message (an `Http1` head and a framed body) as the
  version-independent message of `Silmaril.Net.Http` (RFC 9110 §6): the method token is read
  by `Method.ofToken`; the request target, as sent, becomes the path-with-query (origin form,
  RFC 9112 §3.2.1; the `Host` field stays a header); the content is the body's payload
  (chunks concatenated, RFC 9112 §7.1.3) and the trailers are the chunked trailer section.
  The framing fields `Content-Length` and `Transfer-Encoding` are dropped: they describe the
  wire form of the content, not the content (RFC 9110 §6.4.1, §8.6; RFC 9112 §6.1).
* `parseRequests` reads consecutive requests from the start of a connection, each one where
  the previous one ended (persistent connections, RFC 9112 §9.3), and stops at the first
  incomplete or invalid one. `parseResponses` reads one response per request, in order
  (RFC 9112 §9.3.2), using each request's method for the body length (§6.3 rule 1: no body
  after `HEAD`).
* `framing`: the two together.

The round trips are in `Thms`: requests encoded back to back are read back as themselves
(`requests_encode`), likewise responses (`responses_encode`), so the exchanges of a
connection whose octets are such encodings are the pairs of messages (`connLog_encode`).

Not modelled: interim (`1xx`) responses, which this reading counts as the response to a
request (`Silmaril.Servers.Http.exchSig` is the view that separates them); absolute-form and
authority-form targets (read as path-with-query octets); close-delimited response bodies,
which the round trips exclude (`Body.Fits`); `CONNECT` tunnels.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Servers.Wire1

open Silmaril.Net Silmaril.Net.Http1 Silmaril.Parse.ByteParse

/-- A wire request: its head and framed body. -/
abbrev WireReq : Type := RequestHead × Http1.Body

/-- A wire response: its head and framed body. -/
abbrev WireResp : Type := ResponseHead × Http1.Body

/-- A framing field: `Content-Length` or `Transfer-Encoding` (compared case-insensitively). -/
def isFraming (f : FieldLine) : Bool :=
  lower f.name == contentLengthName || lower f.name == transferEncodingName

/-- The field lines of a wire message, without the framing fields, as a field section. -/
def fieldSection (fs : List FieldLine) : Http.Field.Section :=
  (fs.filter fun f => !isFraming f).map fun f => ⟨f.name, f.value⟩

/-- The trailer section of a body: the chunked trailers, if any. -/
def trailers : Http1.Body → Http.Field.Section
  | .chunked c => fieldSection c.trailers
  | _ => []

/-- **A wire request read as an RFC 9110 request.** -/
def toRequest (m : WireReq) : Http.Request :=
  ⟨⟨Http.Method.ofToken m.1.line.method, ⟨none, none, some m.1.line.target⟩⟩,
    fieldSection m.1.fields, m.2.payload, trailers m.2⟩

/-- **A wire response read as an RFC 9110 response.** -/
def toResponse (m : WireResp) : Http.Response :=
  ⟨m.1.line.code, fieldSection m.1.fields, m.2.payload, trailers m.2⟩

/-- The requests at `i` and after, at most `fuel` of them: each read where the previous one
ended; reading stops at the first message that is incomplete or invalid, or that would not
advance. -/
def parseRequests (bs : ByteArray) : Nat → Nat → List WireReq
  | 0, _ => []
  | fuel + 1, i =>
    if i < bs.size then
      match parseRequestAt bs i with
      | .ok m k => if i < k then m :: parseRequests bs fuel k else []
      | .err _ => []
    else []

/-- The responses at `i` and after, one for each request method in order; reading stops at
the first response that is incomplete or invalid. -/
def parseResponses (bs : ByteArray) : List Bytes → Nat → List WireResp
  | [], _ => []
  | method :: ms, i =>
    match parseResponseAt method bs i with
    | .ok m k => m :: parseResponses bs ms k
    | .err _ => []

/-- The requests of a connection's received octets. -/
def requests (bs : List UInt8) : List Http.Request :=
  (parseRequests ⟨bs.toArray⟩ (bs.length + 1) 0).map toRequest

/-- The responses of a connection's sent octets, to the requests `rs` in order. -/
def responses (rs : List Http.Request) (bs : List UInt8) : List Http.Response :=
  (parseResponses ⟨bs.toArray⟩ (rs.map fun r => r.method.toToken) 0).map toResponse

/-- **The HTTP/1.1 framing of a connection.** -/
def framing : Platform.Framing := ⟨requests, responses⟩

/-- The octets of requests sent back to back on a connection. -/
def encRequests (ms : List WireReq) : List UInt8 := ms.flatMap fun m => encRequest m.1 m.2

/-- The octets of responses sent back to back on a connection. -/
def encResponses (ms : List WireResp) : List UInt8 := ms.flatMap fun m => encResponse m.1 m.2

/-- A wire request that reads back: a valid head, and a body fitting the framing the head
announces. -/
def ReqOk (m : WireReq) : Prop := m.1.Valid ∧ m.2.Fits (requestBodyLength m.1.fields)

/-- A wire response that reads back after a request with method token `method`. -/
def RespOk (method : Bytes) (m : WireResp) : Prop :=
  m.1.Valid ∧ m.2.Fits (responseBodyLength method m.1.line.code m.1.fields)

end Silmaril.Servers.Wire1
