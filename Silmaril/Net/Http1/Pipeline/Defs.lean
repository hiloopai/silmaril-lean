module

public import Silmaril.Net.Http1.Request.Defs

/-!
# Persistent connections and pipelining (RFC 9112 §9.3, §9.3.2, §9.6; RFC 9110 §15.2)

**Server.** `serve cfg H n bs i` runs a server on the octets `bs` of one connection, from
position `i`: it reads a request as its `Profile` frames it (`parseRequestWith`), checks it
(`checkRequest`), answers it with the handler `H`, and goes on with the next request only if
the connection persists (`Context.persistent` and `keepOpen`). It stops at the end of the
input (`eof`), when the connection closes (`closed`), or on a request it rejects
(`rejected status`; RFC 9112 §9.3: a server answers an invalid request and closes). Responses
are produced in the order of the requests, which is what pipelining needs (§9.3.2: "A
server MUST send its responses to those requests in the same order that the requests were
received"). `n` bounds the number of requests.

**Client.** `readResponse method bs n i` reads the responses to one request: interim `1xx`
responses (except `101`, which ends HTTP/1.1 on the connection), then the final response
(RFC 9110 §15.2: "A client MUST be able to parse one or more 1xx responses received prior to
a final response"). `readResponses` reads the responses to a pipeline of requests, given
their methods (the framing of a response depends on the request method, RFC 9112 §6.3 rule 1).

The laws (`Pipeline.Thms`): a pipeline of valid persistent requests is served request by
request, in order, whatever follows; after a request that closes the connection nothing more
is read (so octets smuggled after it are never seen); the responses to a pipeline are read
back in order, interim responses included.
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse

/-- A handler: the response to a checked request. -/
abbrev Handler := RequestHead → Body → Context → ResponseHead × Body

/-- One exchange of a connection. -/
structure Exchange1 where
  request : RequestHead
  body : Body
  context : Context
  response : ResponseHead
  responseBody : Body

/-- Why a server stopped reading a connection. -/
inductive Stop where
  /-- The input ended between requests. -/
  | eof
  /-- The connection does not persist after the last exchange. -/
  | closed
  /-- A request was rejected with this status, then the connection closed. -/
  | rejected (status : Nat)
  /-- The bound on the number of requests was reached. -/
  | fuel
  deriving DecidableEq, Repr

/-- The response sent for a rejected request: no content, `Connection: close`. -/
def errorResponse (status : Nat) : ResponseHead × Body :=
  (⟨⟨Version.http11, status, []⟩,
    [⟨ascii "Connection", closeOption⟩, ⟨ascii "Content-Length", ascii "0"⟩]⟩, .content [])

/-- Serve a connection (see the module documentation). -/
def serve (cfg : ServerConfig) (H : Handler) : Nat → ByteArray → Nat → List Exchange1 × Stop
  | 0, _, _ => ([], .fuel)
  | n + 1, bs, i =>
    if bs.size ≤ i then ([], .eof) else
    match parseRequestWith cfg.profile bs i with
    | .err _ => ([], .rejected 400)
    | .ok (h, b) k =>
      match checkRequest cfg h with
      | .error e => ([], .rejected e.status)
      | .ok c =>
        let x : Exchange1 := ⟨h, b, c, (H h b c).1, (H h b c).2⟩
        if c.persistent && keepOpen cfg.keepAlive h (H h b c).1 then
          let r := serve cfg H n bs k
          (x :: r.1, r.2)
        else ([x], .closed)

/-- The octets the server writes. -/
def serveOutput (r : List Exchange1 × Stop) : Bytes :=
  (r.1.map fun x => encResponse x.response x.responseBody).flatten ++
    match r.2 with
    | .rejected s => encResponse (errorResponse s).1 (errorResponse s).2
    | _ => []

/-! ## Client -/

/-- An interim response: `1xx` other than `101` (RFC 9110 §15.2). -/
def isInterim (code : Nat) : Bool := code / 100 == 1 && code != 101

/-- Read the interim responses and the final response to a request with method `method`. -/
def readResponse (method : Bytes) (bs : ByteArray) :
    Nat → Nat → Res (List ResponseHead × ResponseHead × Body)
  | 0, i => .err ⟨i, .other "too many interim responses"⟩
  | n + 1, i =>
    match parseResponseAt method bs i with
    | .err e => .err e
    | .ok (h, b) j =>
      if isInterim h.line.code then
        match readResponse method bs n j with
        | .ok (is, f, fb) k => .ok (h :: is, f, fb) k
        | .err e => .err e
      else .ok ([], h, b) j

/-- The responses to one request, as octets. -/
def encResponses (is : List ResponseHead) (f : ResponseHead) (fb : Body) : Bytes :=
  (is.map encResponseHead).flatten ++ encResponse f fb

/-- Read the responses to pipelined requests with methods `ms`, each with at most `n` interim
responses. -/
def readResponses (bs : ByteArray) (n : Nat) :
    List Bytes → Nat → Res (List (List ResponseHead × ResponseHead × Body))
  | [], i => .ok [] i
  | m :: ms, i =>
    match readResponse m bs (n + 1) i with
    | .err e => .err e
    | .ok r j =>
      match readResponses bs n ms j with
      | .ok rs k => .ok (r :: rs) k
      | .err e => .err e

/-- A client may retry a request automatically after a connection failure only if its method is
idempotent (RFC 9112 §9.3.1: "A user agent MUST NOT automatically retry a request with a
non-idempotent method"; idempotence from RFC 9110 §9.2.2). -/
def mayAutoRetry (method : Bytes) : Bool := (Http.Method.ofToken method).isIdempotent

/-- A request the server accepts and after which it keeps the connection open. -/
def KeptOpen (cfg : ServerConfig) (H : Handler) (h : RequestHead) (b : Body) : Prop :=
  ∃ c, checkRequest cfg h = .ok c ∧ (c.persistent && keepOpen cfg.keepAlive h (H h b c).1) = true

/-- The responses to one request are well formed: valid interim responses, then a valid final
response whose body fits the framing for the request method. -/
def ResponsesFit (method : Bytes) (is : List ResponseHead) (f : ResponseHead) (fb : Body) : Prop :=
  (∀ i ∈ is, i.Valid ∧ isInterim i.line.code = true) ∧ f.Valid ∧ isInterim f.line.code = false ∧
    fb.Fits (responseBodyLength method f.line.code f.fields)

end Silmaril.Net.Http1
