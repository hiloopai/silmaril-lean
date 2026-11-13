module

public import Silmaril.Wasi.Versions.WitImport.PickRest.Defs
public import Silmaril.Wasi.Versions.Net.Defs
public import Silmaril.Wasi.Versions.P2.Io.Defs

@[expose] public section

/-!
# WASI 0.2 `wasi:http` response bodies, streams and trailers as a theory

Extends the outgoing HTTP slice of `Silmaril.Wasi.Versions.Net` (`httpTh W`) with the incoming
response body, checked against `specs/wasi/0.2.12/http/types.wit` and
`specs/wasi/0.2.12/io/streams.wit` (the same signatures as `specs/wasi/v0.2.9`):

* `[method]incoming-response.consume() -> result<incoming-body>` (`consume2`);
* `[method]incoming-body.stream() -> result<input-stream>` (`bodyStream2`; WIT name `%stream`);
* `[static]incoming-body.finish(this: incoming-body) -> future-trailers` (`bodyFinish2`);
* `[method]future-trailers.get() -> option<result<result<option<trailers>, error-code>>>`
  (`trGet2`);
* `[method]fields.entries() -> list<tuple<field-name, field-value>>` (`entries2`; `trailers`
  is `fields`, `field-name = string`, `field-value = list<u8>`);
* `wasi:io/streams` `[method]input-stream.read(len: u64)` and `blocking-read(len: u64)
  -> result<list<u8>, stream-error>` (`P2.isRead`, `P2.isBread`) on the body's stream.

## Webs with bodies

A **body web** `B : BWeb` answers a request (authority, path-with-query) with a response
(`BResp`: status, body bytes, optional trailers) or an `error-code`. `B.web : Web` forgets the
body and trailers. Trailers are lists of fields (`Fields`, names as character lists), encoded as
`fieldsV` and decoded by `fieldsOf`.

## The theory `bodyTh B`

A gated theory (`Net.gated`). Its state `BodySt` has the 0.2 HTTP state `base` (moved by
`httpNext` on every answer) and, per handle, the request key of incoming bodies (`bodies`),
of trailer futures (`ftr`) and of trailer resources (`trs`), and per input stream of a body its
key and the number of bytes delivered (`streams`). The check `bodyOk B` is `httpOk B.web` on
the base, and:

* `read`/`blocking-read(s, len)` of a body stream: `ok(bytes)` with `bytes` the next at most
  `len` bytes of the body; `error(closed)` only when the whole body was delivered;
  `error(last-operation-failed)` at any time (the stream is then forgotten); or a trap;
* `get` of a trailer future: `none` (not ready), `some(err)` (already retrieved),
  `some(ok(error(_)))` (the transfer failed), or `some(ok(ok(t)))` with `t` present exactly when
  the response has trailers;
* `entries` of a trailer resource: the response's trailers.

Nothing else is constrained (in particular `consume` and `stream` may fail, and a second
`stream` is not checked). The theory is loose in the timing: reads may deliver fewer bytes than
asked, zero included.

## Concrete host

`bodyImpl B`: as `httpImpl B.web` for the outgoing slice; fresh handles; every read delivers
`min len remaining` bytes and `error(closed)` at the end; trailer futures are ready at once.

**Not modelled**: the outgoing body (`outgoing-request.body`, `outgoing-body.write`/`finish`),
headers, `incoming-request`/`response-outparam` (the server side), `subscribe`, and the rule
that a body's stream must be dropped before `finish`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Fields -/

/-- A list of fields: names (as characters) and values. -/
abbrev Fields : Type := List (List Char × List (BitVec 8))

/-- The characters of a list of `char` values. -/
def charsOf : List Val → Option (List Char)
  | [] => some []
  | .char c :: t => (charsOf t).map (c :: ·)
  | _ => none

/-- The bytes of a list of `u8` values. -/
def u8sOf : List Val → Option (List (BitVec 8))
  | [] => some []
  | .u8 b :: t => (u8sOf t).map (b :: ·)
  | _ => none

/-- `tuple<field-name, field-value>`. -/
def fieldV (x : List Char × List (BitVec 8)) : Val := .record [.record (x.1.map .char), bytesV x.2]

/-- `list<tuple<field-name, field-value>>`. -/
def fieldsV (l : Fields) : Val := .record (l.map fieldV)

/-- Decode one field. -/
def fieldOf : Val → Option (List Char × List (BitVec 8))
  | .record [.record n, .record v] =>
    match charsOf n, u8sOf v with
    | some n', some v' => some (n', v')
    | _, _ => none
  | _ => none

/-- Decode a list of fields. -/
def fieldsOfL : List Val → Option Fields
  | [] => some []
  | x :: t =>
    match fieldOf x, fieldsOfL t with
    | some y, some l => some (y :: l)
    | _, _ => none

/-- Decode `list<tuple<field-name, field-value>>`. -/
def fieldsOf : Val → Option Fields
  | .record es => fieldsOfL es
  | _ => none

/-! ## Body webs -/

/-- A response: status, body and trailers. -/
structure BResp where
  /-- The status code. -/
  status : BitVec 16
  /-- The body bytes. -/
  body : List (BitVec 8)
  /-- The trailers, if any. -/
  trailers : Option Fields

/-- The outcome of a request with a body web. -/
inductive BOutcome where
  | resp (r : BResp)
  | error (k : Nat)

/-- A body web: the outcome of a request for an authority and a path-with-query. -/
abbrev BWeb : Type := Val → Val → BOutcome

/-- The web of status codes of a body web. -/
def BWeb.web (B : BWeb) : Web := fun a p =>
  match B a p with
  | .resp r => .status r.status
  | .error k => .error k

/-- The body of the response to the request `k` (empty for a failed request). -/
def BWeb.body (B : BWeb) (k : Val × Val) : List (BitVec 8) :=
  match B k.1 k.2 with
  | .resp r => r.body
  | .error _ => []

/-! ## Function names -/

/-- `wasi:http/types.[method]incoming-response.consume`. -/
def consume2 : FnName := ⟨"wasi:http/types", "[method]incoming-response.consume"⟩
/-- `wasi:http/types.[method]incoming-body.stream`. -/
def bodyStream2 : FnName := ⟨"wasi:http/types", "[method]incoming-body.stream"⟩
/-- `wasi:http/types.[static]incoming-body.finish`. -/
def bodyFinish2 : FnName := ⟨"wasi:http/types", "[static]incoming-body.finish"⟩
/-- `wasi:http/types.[method]future-trailers.get`. -/
def trGet2 : FnName := ⟨"wasi:http/types", "[method]future-trailers.get"⟩
/-- `wasi:http/types.[method]fields.entries`. -/
def entries2 : FnName := ⟨"wasi:http/types", "[method]fields.entries"⟩

/-- The body functions of this slice, **read from the vendored WIT**: the functions of the
imported tables `http2T` and `io2T` with the keys `WitImport.body2Keys`. Proofs that need the
members rewrite with `bodyFns2_eq`. -/
def bodyFns2 : Set FnName :=
  {f | f ∈ WitImport.pick (WitImport.names WitImport.http2T ++ WitImport.names WitImport.io2T)
    WitImport.body2Keys}

/-- **The imported body functions are the hand-written ones** (kernel-checked on the imported
tables). -/
theorem bodyFns2_eq :
    bodyFns2 = {consume2, bodyStream2, bodyFinish2, trGet2, entries2, P2.isRead, P2.isBread} := by
  ext f
  show f ∈ WitImport.pick (WitImport.names WitImport.http2T ++ WitImport.names WitImport.io2T)
    WitImport.body2Keys ↔ _
  rw [(show (WitImport.pick (WitImport.names WitImport.http2T ++ WitImport.names WitImport.io2T)
    WitImport.body2Keys).Perm
      [consume2, bodyStream2, bodyFinish2, trGet2, entries2, P2.isRead, P2.isBread] by
      decide +kernel).mem_iff]
  simp

/-- A body function, as a test. -/
def isBodyFn (f : FnName) : Bool :=
  f == consume2 || f == bodyStream2 || f == bodyFinish2 || f == trGet2 || f == entries2 ||
    f == P2.isRead || f == P2.isBread

/-- The 0.2 HTTP functions with bodies. -/
def httpBodyImports : Set FnName := httpImports ∪ bodyFns2

/-! ## The theory -/

/-- The state of the body theory. Every handle the host hands out is recorded, with its request
when the theory tracks it and `none` otherwise, so that a reused handle forgets the old one. -/
structure BodySt where
  /-- The state of the outgoing HTTP theory. -/
  base : HttpSt := HttpSt.init
  /-- The request of each incoming body. -/
  bodies : List (BitVec 32 × Option (Val × Val)) := []
  /-- The request of each body stream and the number of bytes it delivered. -/
  streams : List (BitVec 32 × Option ((Val × Val) × Nat)) := []
  /-- The request of each trailer future. -/
  ftr : List (BitVec 32 × Option (Val × Val)) := []
  /-- The request of each trailer resource. -/
  trs : List (BitVec 32 × Option (Val × Val)) := []

/-- `ok(handle)`. -/
def okHandle : Option (List Val) → Option (BitVec 32)
  | some [.variant 0 (some (.u32 h))] => some h
  | _ => none

/-- The number of bytes of an `ok(bytes)` answer of `read`. -/
def readCount : Option (List Val) → Option Nat
  | some [.variant 0 (some (.record vs))] => (u8sOf vs).map List.length
  | _ => none

/-- The answer `error(last-operation-failed(_))`. -/
def isFailed : Option (List Val) → Bool
  | some [.variant 1 (some (.variant 0 _))] => true
  | _ => false

/-- A read function. -/
def isReadFn (f : FnName) : Bool := f == P2.isRead || f == P2.isBread

/-- The trailer handle of a `get` answer `some(ok(ok(some(t))))`. -/
def trHandle : Option (List Val) → Option (BitVec 32)
  | some [.variant 1 (some (.variant 0 (some (.variant 0 (some (.variant 1 (some (.u32 t))))))))] =>
    some t
  | _ => none

/-- The body part of the next state. -/
def bodyStep (q : BodySt) (e : WEv) : BodySt :=
  match e with
  | .imp f (.u32 h :: _) r =>
    if f = consume2 then
      match okHandle r with
      | some b => { q with bodies := (b, lookup h q.base.resps) :: q.bodies }
      | none => q
    else if f = bodyStream2 then
      match okHandle r with
      | some s => { q with streams := (s, (lookup h q.bodies).join.map (·, 0)) :: q.streams }
      | none => q
    else if isReadFn f then
      match lookup h q.streams, readCount r with
      | some (some (k, n)), some c => { q with streams := (h, some (k, n + c)) :: q.streams }
      | some (some _), none =>
        if isFailed r then { q with streams := (h, none) :: q.streams } else q
      | _, _ => q
    else if f = bodyFinish2 then
      match r with
      | some [.u32 ft] => { q with ftr := (ft, (lookup h q.bodies).join) :: q.ftr }
      | _ => q
    else if f = trGet2 then
      match trHandle r with
      | some t => { q with trs := (t, (lookup h q.ftr).join) :: q.trs }
      | none => q
    else q
  | _ => q

/-- **The next state**: the outgoing HTTP state moves by `httpNext`, the body part by
`bodyStep`. -/
def bodyNext (q : BodySt) (e : WEv) : BodySt :=
  { bodyStep q e with base := httpNext q.base e }

/-- The `u64` length argument of a read. -/
def readLen (a : List Val) : Nat := P2.lenOf a

/-- A `read` answer for the remaining bytes `rest`. -/
def readOk (rest : List (BitVec 8)) (len : Nat) : Option (List Val) → Bool
  | none => true
  | some [.variant 0 (some (.record vs))] =>
    match u8sOf vs with
    | some bs => decide (bs.length ≤ len) && decide (bs = rest.take bs.length)
    | none => false
  | some [.variant 1 (some (.variant 1 none))] => rest.isEmpty
  | some [.variant 1 (some (.variant 0 _))] => true
  | _ => false

/-- A trailer-future answer for the trailers `tr` of a response. -/
def trailerOk (tr : Option Fields) : Option (List Val) → Bool
  | none => true
  | some [.variant 0 none] => true
  | some [.variant 1 (some (.variant 1 none))] => true
  | some [.variant 1 (some (.variant 0 (some (.variant 1 (some (.variant _ _))))))] => true
  | some [.variant 1 (some (.variant 0 (some (.variant 0 (some (.variant 0 none))))))] =>
    tr.isNone
  | some [.variant 1 (some (.variant 0 (some (.variant 0 (some (.variant 1 (some (.u32 _))))))))] =>
    tr.isSome
  | _ => false

/-- An `entries` answer for the trailers `tr`. -/
def entriesOk (tr : Option Fields) : Option (List Val) → Bool
  | none => true
  | some [x] => match tr with
    | some l => fieldsOf x == some l
    | none => true
  | _ => match tr with
    | some _ => false
    | none => true

/-- The trailers of the response to the request `k` (`none` for a failed request). -/
def BWeb.trailers (B : BWeb) (k : Val × Val) : Option Fields :=
  match B k.1 k.2 with
  | .resp r => r.trailers
  | .error _ => none

/-- The body part of the check. -/
def bodyCheck (B : BWeb) (q : BodySt) (e : WEv) : Bool :=
  match e with
  | .imp f (.u32 h :: a) r =>
    if isReadFn f then
      match lookup h q.streams with
      | some (some (k, n)) => readOk ((B.body k).drop n) (readLen (.u32 h :: a)) r
      | _ => true
    else if f = trGet2 then
      match lookup h q.ftr with
      | some (some k) => match B k.1 k.2 with
        | .resp _ => trailerOk (B.trailers k) r
        | .error _ => true
      | _ => true
    else if f = entries2 then
      match lookup h q.trs with
      | some (some k) => entriesOk (B.trailers k) r
      | _ => true
    else true
  | _ => true

/-- The check of an answer against the body web `B`. -/
def bodyOk (B : BWeb) (q : BodySt) (e : WEv) : Bool := httpOk B.web q.base e && bodyCheck B q e

/-- **The 0.2 HTTP theory with response bodies** of the body web `B`. -/
def bodyTh (B : BWeb) : Protocol BodySt WEv := gated {} bodyNext (bodyOk B)

/-! ## The concrete host -/

/-- The state after the answers `p`. -/
def bodyState (p : List WEv) : BodySt := p.foldl bodyNext {}

/-- A fresh handle. -/
def freshH (p : List WEv) : BitVec 32 := BitVec.ofNat 32 p.length

/-- The answer of a read of at most `len` bytes from `rest`. -/
def readAns (rest : List (BitVec 8)) (len : Nat) : Option (List Val) :=
  if rest.isEmpty then some [P2.errClosed] else some [okV (some (bytesV (rest.take len)))]

/-- The answer of `get` on a trailer future for the trailers `tr`. -/
def trailerAns (n : BitVec 32) : Option Fields → Option (List Val)
  | none => some [.variant 1 (some (okV (some (okV (some noneV)))))]
  | some _ => some [.variant 1 (some (okV (some (okV (some (.variant 1 (some (.u32 n))))))))]

/-- `some(err)`: already retrieved. -/
def retrievedV : Val := .variant 1 (some (.variant 1 none))

/-- The body functions of the concrete host. -/
def bodyAns (B : BWeb) (p : List WEv) (f : FnName) (a : List Val) : Option (List Val) :=
  if f = consume2 ∨ f = bodyStream2 then some [okV (some (.u32 (freshH p)))]
  else if f = bodyFinish2 then some [.u32 (freshH p)]
  else if isReadFn f then
    match lookup (selfH a) (bodyState p).streams with
    | some (some (k, n)) => readAns ((B.body k).drop n) (readLen a)
    | _ => some [P2.errClosed]
  else if f = trGet2 then
    match lookup (selfH a) (bodyState p).ftr with
    | some (some k) => trailerAns (freshH p) (B.trailers k)
    | _ => some [retrievedV]
  else
    match lookup (selfH a) (bodyState p).trs with
    | some (some k) => some [fieldsV ((B.trailers k).getD [])]
    | _ => some [fieldsV []]

/-- **The concrete 0.2 HTTP host with bodies** of the body web `B`. -/
def bodyImpl (B : BWeb) : Impl := fun p f a =>
  if isBodyFn f then bodyAns B p f a else httpImpl B.web p f a

end Silmaril.Wasi.Versions.Net
