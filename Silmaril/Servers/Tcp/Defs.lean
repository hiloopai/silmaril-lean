module

public import Silmaril.Servers.Transport.Defs
public import Silmaril.Servers.Wire1.Defs
public import Silmaril.Servers.WasiExamples.Defs

/-!
# HTTP over a TCP byte stream: readings, protocol selection, and implementing an HTTP server

An HTTP server on a port is, at its sockets, a set of transport traces
(`Silmaril.Servers.Transport`). This module reads such traces as HTTP request/response traces
of the server core, and states when a TCP-level server implements an HTTP-level one.

**Level.** Everything is stated over the *socket API*: the reliable in-order byte stream of
`Net.Tcp.Service` (RFC 9293 §2.2). No theorem here concerns segments, retransmission or the
handshake (`Net.Tcp.Transfer`): a result about a TCP-level server assumes its sockets behave as
the API says.

## Reading HTTP/1.1 off a connection, with what is left over

`h1Read bs` reads consecutive HTTP/1.1 requests from the octets `bs` received on a connection
(RFC 9112 §9.3, persistent connections) and returns a `Transport.Parse`: the requests, the
octets after the last complete one (`rest`), and whether reading stopped before the end
(`err`): an incomplete request (more octets may come) and a malformed one both stop the
reading there, and both leave their octets in `rest`. The messages agree with the reading of
`Servers.Wire1` (`Thms.h1Read_msgs`); encoded valid requests are read back with nothing left
over (`Thms.h1Read_encode`); every message read is valid (`Thms.h1Read_valid`).

## Protocol selection (an assumption, `Transport.Select`)

`select sel alpn bs` decides from the first octets `bs` of a connection which protocol it
speaks (`Proto`): HTTP/1.1, HTTP/2, or `refused` (a connection error). `none` means not yet
decided (the octets so far are a proper prefix of the HTTP/2 preface).

* `http1`: always HTTP/1.1 (no negotiation; an HTTP/2 client is not served as HTTP/2,
  `Thms.select_http1_ne_h2`).
* `h2PriorKnowledge` (RFC 9113 §3.3): HTTP/2 when the connection starts with the preface
  `h2Preface` (§3.4), refused otherwise.
* `sniffPreface`: HTTP/2 on the preface, HTTP/1.1 on anything else. The `h2c` upgrade
  (RFC 7540 §3.2, removed in RFC 9113) is **not** modelled.
* `alpn ids`: under TLS, by the ALPN id negotiated in the handshake (RFC 7301), `h2` or
  `http/1.1` among `ids`; without ALPN, HTTP/1.1. The TLS layer itself is an **assumption**:
  that it delivers the plaintext octets in order and reports the negotiated id. No TLS model is
  refined here.

A decision, once made, does not change as more octets arrive (`Thms.select_mono`).

## Reading a server's traces as HTTP traces

`h1Reading sel alpn p` is a partial observation map (`Transport.PMap`) from transport traces to
core traces over RFC 9110 messages (`Servers.Http.sig`). It is defined when every connection
opened on port `p` is selected as HTTP/1.1; it is **undefined** as soon as one is HTTP/2,
refused or undecided (HTTP/2 framing is not read here: `Net.Http2` models frames, but no
reading of HTTP/2 exchanges into the core exists yet). On each connection `c`, the `k`-th
request read (identity `⟨c, k⟩`) is paired with the `k`-th response read from the octets sent
(`Wire1.responses`, which uses the request's method for the response's framing); the order of
events across connections is not observed (connections are listed in order of opening).

## Implementing an HTTP server

For a reading `ρ`, a transport model `T` and a core model `M`:

* `AtMost ρ T M`: every HTTP trace read off `T` is a trace of `M` (`ρ.image T ⊆ M`);
* `AtLeast ρ T M`: every trace of `M` is read off some trace of `T` (`M ⊆ ρ.image T`);
* `Exactly ρ T M`: both.

The direction is trace inclusion, implementation first for `AtMost`.

## Example: hello over TCP

`helloTcp p` is a TCP-level server: on every connection opened on `p`, the octets received are
complete valid requests (not `HEAD` or `CONNECT`) and the octets sent are one `helloWire`
response per request (`200`, `content-type: text/plain`, `content-length: 5`, `hello`). It
describes the server at points where every request read has been answered. `Thms` proves that
it implements **at most** the `wasi:http` `hello` component's per-request HTTP server (the
denotation of its core module over typed hosts), and **at least** every single-exchange trace of
a valid request.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Servers.Tcp

open Silmaril.Servers.Transport Silmaril.Servers.Wire1
open Silmaril.Net.Http1
open Silmaril.Net.Http (Request Response)

/-! ## HTTP/1.1 off a connection -/

/-- The consecutive requests at `i` and after, at most `fuel` of them, with the position where
reading stopped. -/
def readReqs (bs : ByteArray) : Nat → Nat → List WireReq × Nat
  | 0, i => ([], i)
  | fuel + 1, i =>
    if i < bs.size then
      match parseRequestAt bs i with
      | .ok m k => if i < k then ((readReqs bs fuel k).1.cons m, (readReqs bs fuel k).2) else ([], i)
      | .err _ => ([], i)
    else ([], i)

/-- **Reading HTTP/1.1 requests off a connection**, with leftover octets and an error flag. -/
def h1Read (bs : List UInt8) : Parse WireReq :=
  let r := readReqs ⟨bs.toArray⟩ (bs.length + 1) 0
  ⟨r.1, bs.drop r.2, decide (r.2 < bs.length)⟩

/-! ## Protocol selection -/

/-- The application protocol of a connection. -/
inductive Proto where
  | h1
  | h2
  | refused
  deriving DecidableEq, Repr

/-- The HTTP/2 connection preface (RFC 9113 §3.4): `PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n`. -/
def h2Preface : List UInt8 :=
  [0x50, 0x52, 0x49, 0x20, 0x2a, 0x20, 0x48, 0x54, 0x54, 0x50, 0x2f, 0x32, 0x2e, 0x30,
   0x0d, 0x0a, 0x0d, 0x0a, 0x53, 0x4d, 0x0d, 0x0a, 0x0d, 0x0a]

/-- The ALPN id of HTTP/2 over TLS, `h2` (RFC 9113 §3.2). -/
def alpnH2 : List UInt8 := [0x68, 0x32]

/-- The ALPN id of HTTP/1.1, `http/1.1` (RFC 7301 §6). -/
def alpnH1 : List UInt8 := [0x68, 0x74, 0x74, 0x70, 0x2f, 0x31, 0x2e, 0x31]

/-- **Protocol selection** from the first octets (and the ALPN id under TLS); `none`: not yet
decided. -/
def select : Select → Option (List UInt8) → List UInt8 → Option Proto
  | .http1, _, _ => some .h1
  | .h2PriorKnowledge, _, bs =>
    if h2Preface <+: bs then some .h2 else if bs <+: h2Preface then none else some .refused
  | .sniffPreface, _, bs =>
    if h2Preface <+: bs then some .h2 else if bs <+: h2Preface then none else some .h1
  | .alpn ids, a, _ =>
    match a with
    | none => some .h1
    | some id =>
      if id ∈ ids ∧ id = alpnH2 then some .h2
      else if id ∈ ids ∧ id = alpnH1 then some .h1 else some .refused

/-! ## Reading transport traces as HTTP traces -/

/-- The answered exchanges of a connection: the `k`-th request with the `k`-th response. -/
def pairs (c : Conn) : Nat → List Request → List Response → List (ReqId × Request × Response)
  | k, r :: rs, x :: xs => (⟨c, k⟩, r, x) :: pairs c (k + 1) rs xs
  | _, _, _ => []

/-- The requests of a connection not answered yet. -/
def pending (c : Conn) : Nat → List Request → List Response → List (ReqId × Request)
  | k, _ :: rs, _ :: xs => pending c (k + 1) rs xs
  | k, r :: rs, [] => (⟨c, k⟩, r) :: pending c (k + 1) rs []
  | _, [], _ => []

/-- The HTTP events of a connection: the answered exchanges, then the pending requests. -/
def connTrace (c : Conn) (rs : List Request) (xs : List Response) : Servers.Trace Http.sig :=
  Trace.seq (A := Http.sig) (pairs c 0 rs xs) ++ (pending c 0 rs xs).map fun p => .recv p.1 p.2

/-- The HTTP/1.1 trace of the connections on port `p`. -/
def h1Trace {Addr : Type} (p : Port) (t : TTrace Addr) : Servers.Trace Http.sig :=
  (opened p t).flatMap fun c =>
    let rs := requests (streamIn c t)
    connTrace c rs (responses rs (streamOut c t))

/-- **The HTTP/1.1 reading of port `p`**, defined when every connection on `p` is selected as
HTTP/1.1. -/
def h1Reading {Addr : Type} (sel : Select) (alpn : Option (List UInt8)) (p : Port) :
    PMap (TTrace Addr) (Servers.Trace Http.sig) := fun t =>
  if (opened p t).all (fun c => select sel alpn (streamIn c t) == some .h1) then some (h1Trace p t)
  else none

/-! ## Implementing an HTTP server -/

/-- Every HTTP trace read off `T` is one of `M`. -/
def AtMost {Addr : Type} {A : Servers.Sig} (ρ : PMap (TTrace Addr) (Servers.Trace A))
    (T : TModel Addr) (M : Servers.Model A) : Prop := ∀ t ∈ ρ.image T, M.Tr t

/-- Every trace of `M` is read off some trace of `T`. -/
def AtLeast {Addr : Type} {A : Servers.Sig} (ρ : PMap (TTrace Addr) (Servers.Trace A))
    (T : TModel Addr) (M : Servers.Model A) : Prop := ∀ t, M.Tr t → t ∈ ρ.image T

/-- Both. -/
def Exactly {Addr : Type} {A : Servers.Sig} (ρ : PMap (TTrace Addr) (Servers.Trace A))
    (T : TModel Addr) (M : Servers.Model A) : Prop := AtMost ρ T M ∧ AtLeast ρ T M

/-! ## Example: hello over TCP -/

/-- `200`, `content-type: text/plain`, `content-length: 5`, `hello`, on the wire. -/
def helloWire : WireResp :=
  (⟨⟨Version.http11, 200, ascii "OK"⟩,
    [⟨ascii "content-type", ascii "text/plain"⟩, ⟨ascii "content-length", ascii "5"⟩]⟩,
    .content (ascii "hello"))

/-- A request `helloTcp` serves: valid, and not `HEAD` or `CONNECT`. -/
def Served (m : WireReq) : Prop :=
  ReqOk m ∧ m.1.line.method ≠ methodHEAD ∧ m.1.line.method ≠ methodCONNECT

/-- **Hello over TCP on port `p`**: distinct connections, each carrying complete served
requests, each answered `helloWire`. -/
def helloTcp {Addr : Type} (p : Port) : TModel Addr := {t |
  (opened p t).Nodup ∧ ∀ c ∈ opened p t, ∃ ms : List WireReq, (∀ m ∈ ms, Served m) ∧
    streamIn c t = encRequests ms ∧ streamOut c t = encResponses (ms.map fun _ => helloWire)}

end Silmaril.Servers.Tcp
