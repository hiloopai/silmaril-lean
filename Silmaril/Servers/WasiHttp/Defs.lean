module

public import Silmaril.Servers.Calls.Defs
public import Silmaril.Wasi.Theory.Defs
public import Silmaril.Net.Http.Message.Defs

@[expose] public section

/-!
# The `wasi:http` proxy world: components as HTTP servers

The server side of `wasi:http` 0.2, checked against `specs/wasi/0.2.12/http/{proxy,handler,
types}.wit` and `specs/wasi/0.2.12/io/streams.wit`. A component of the `wasi:http/proxy`
world exports

* `wasi:http/incoming-handler.handle(request: incoming-request, response-out:
  response-outparam)` (`handleF`), called by the host once per incoming request.

This slice imports, from `wasi:http/types`:

* `[method]incoming-request.method() -> method` and `path-with-query() -> option<string>`
  (`reqMethod`, `reqPath`);
* `[constructor]fields()` and `[constructor]outgoing-response(headers: headers)` (`newFields`,
  `newResp`);
* `[method]outgoing-response.set-status-code(status-code: u16) -> result` and
  `body() -> result<outgoing-body>` (`setStatus`, `respBody`);
* `[method]outgoing-body.write() -> result<output-stream>` and `[static]outgoing-body.finish(
  this: outgoing-body, trailers: option<trailers>) -> result<_, error-code>` (`bodyWrite`,
  `bodyFinish`);
* `[static]response-outparam.set(param: response-outparam, response: result<outgoing-response,
  error-code>)` (`outSet`);

and from `wasi:io/streams` `[method]output-stream.blocking-write-and-flush` and
`[resource-drop]output-stream` (`Silmaril.Wasi.streamWrite`, `streamDrop`). The names follow
the unversioned 0.2 convention of `Silmaril.Wasi.Versions.Net`. Values are encoded as in
`Silmaril.Wasi.Theory`: handles as `u32`, `result` and `option` as variants (`ok`/`none` case
`0`), strings as records of `char`s, `method` by its WIT case number.

## Reading a component as an HTTP server

The interface is `httpIface`: requests and responses of `Silmaril.Net.Http` (RFC 9110 §6). A
completed call of `handle(r, o)` is read as one atomic exchange (`Silmaril.Servers.Calls`):

* **its response** (`respOf o`): the response passed to `response-outparam.set(o, ok(rh))`,
  with the status of the last accepted `set-status-code` on `rh` (default `200`, as the WIT
  says) and as content the bytes written through the output streams of the body of `rh`, which
  must be finished. Only the host's answers are read (`OSt`, `ostep`): a failed or ill-typed
  answer to one of the response's operations makes the response unobservable (`none`), as does
  a missing `set` or `finish`. Writes to other streams (stdout, say) are ignored. Header fields
  are not observed (the response's field section is empty).
* **its request**: any request consistent with what the host answered on `r`
  (`ReqOk`): the `method` and `path-with-query` answers on `r` encode the request's method and
  path. The rest of the request (headers, authority, content) is left open.

`wasiServer σ` is the server read from the component `σ` (`Calls.model`, with no theory of
the host). Its traces include every interaction with every host, since the imports of `σ` are
uninterpreted. A host whose request answers are not those of any request explains no trace.

**Not modelled**: request and response headers, request bodies (`consume`), trailers,
`send-informational`, the rule that `set` may be called once, resource drops other than the
output stream's, and concurrent export calls (a component body runs one call at a time).

A Silmaril addition.
-/

namespace Silmaril.Servers.WasiHttp

open Silmaril.Games Silmaril.Wasi Silmaril.Servers.Calls
open Silmaril.Wasm.Component (Val)
open Silmaril.Net.Http (Request Response Method)

/-! ## Functions and the world -/

/-- `wasi:http/incoming-handler.handle`. -/
def handleF : FnName := ⟨"wasi:http/incoming-handler", "handle"⟩
/-- `wasi:http/types.[method]incoming-request.method`. -/
def reqMethod : FnName := ⟨"wasi:http/types", "[method]incoming-request.method"⟩
/-- `wasi:http/types.[method]incoming-request.path-with-query`. -/
def reqPath : FnName := ⟨"wasi:http/types", "[method]incoming-request.path-with-query"⟩
/-- `wasi:http/types.[constructor]fields`. -/
def newFields : FnName := ⟨"wasi:http/types", "[constructor]fields"⟩
/-- `wasi:http/types.[constructor]outgoing-response`. -/
def newResp : FnName := ⟨"wasi:http/types", "[constructor]outgoing-response"⟩
/-- `wasi:http/types.[method]outgoing-response.set-status-code`. -/
def setStatus : FnName := ⟨"wasi:http/types", "[method]outgoing-response.set-status-code"⟩
/-- `wasi:http/types.[method]outgoing-response.body`. -/
def respBody : FnName := ⟨"wasi:http/types", "[method]outgoing-response.body"⟩
/-- `wasi:http/types.[method]outgoing-body.write`. -/
def bodyWrite : FnName := ⟨"wasi:http/types", "[method]outgoing-body.write"⟩
/-- `wasi:http/types.[static]outgoing-body.finish`. -/
def bodyFinish : FnName := ⟨"wasi:http/types", "[static]outgoing-body.finish"⟩
/-- `wasi:http/types.[static]response-outparam.set`. -/
def outSet : FnName := ⟨"wasi:http/types", "[static]response-outparam.set"⟩

/-- The imports of this slice, as a list. -/
def proxyList : List FnName :=
  [reqMethod, reqPath, newFields, newResp, setStatus, respBody, bodyWrite, bodyFinish, outSet,
    streamWrite, streamDrop]

/-- The imports of this slice. -/
def proxyImports : Set FnName := {f | f ∈ proxyList}

/-- **The proxy world slice**: the imports above, the export `handle`. -/
def proxyWorld : World := ⟨proxyImports, {handleF}⟩

/-! ## Encodings -/

/-- The WIT case number of a method (`variant method`, `other` last). -/
def methodV : Method → Val
  | .get => .variant 0 none
  | .head => .variant 1 none
  | .post => .variant 2 none
  | .put => .variant 3 none
  | .delete => .variant 4 none
  | .connect => .variant 5 none
  | .options => .variant 6 none
  | .trace => .variant 7 none
  | .patch => .variant 8 none
  | .other t => .variant 9 (some (.record (t.map fun b => .char (Char.ofNat b.toNat))))

/-- An `option<string>` of octets (each octet a `char`). -/
def pathV : Option (List UInt8) → Val
  | none => .variant 0 none
  | some p => .variant 1 (some (.record (p.map fun b => .char (Char.ofNat b.toNat))))

/-- The octets of the `char`s of a string (other values are skipped). -/
def octetsOf (cs : List Val) : List UInt8 :=
  cs.filterMap fun | .char c => some c.toNat.toUInt8 | _ => none

/-- The path read from an answer of `path-with-query`. -/
def pathOf : Option (List Val) → Option (List UInt8)
  | some [.variant 1 (some (.record cs))] => some (octetsOf cs)
  | _ => none

/-- The handle in an answer `h` or `ok(h)` (`0` otherwise). -/
def hOf : Option (List Val) → BitVec 32
  | some [.u32 h] => h
  | some [.variant 0 (some (.u32 h))] => h
  | _ => 0

/-- The response-outparam of the arguments of `handle`. -/
def outOf : List Val → BitVec 32
  | [_, .u32 o] => o
  | _ => 0

/-- The request handle of the arguments of `handle`. -/
def reqOf : List Val → BitVec 32
  | [.u32 r, _] => r
  | _ => 0

/-! ## The response of a call -/

/-- Association-list lookup. -/
def look {α : Type} (k : BitVec 32) : List (BitVec 32 × α) → Option α
  | [] => none
  | (k', v) :: l => if k' = k then some v else look k l

/-- What the answers of a call say about its responses. -/
structure OSt where
  /-- The accepted status of each outgoing response. -/
  status : List (BitVec 32 × BitVec 16) := []
  /-- The outgoing body of each outgoing response. -/
  body : List (BitVec 32 × BitVec 32) := []
  /-- The outgoing body of each output stream. -/
  stream : List (BitVec 32 × BitVec 32) := []
  /-- The bytes written to each outgoing body. -/
  bytes : List (BitVec 32 × List (BitVec 8)) := []
  /-- The finished outgoing bodies. -/
  fin : List (BitVec 32) := []
  /-- The outgoing response set for the call's outparam. -/
  set : Option (BitVec 32) := none

/-- An answer of `set-status-code`. -/
def oStatus (st : OSt) : List Val → Option (List Val) → Option OSt
  | [.u32 rh, .u16 s], some [.variant 0 none] => some { st with status := (rh, s) :: st.status }
  | _, _ => none

/-- An answer of `outgoing-response.body`. -/
def oBody (st : OSt) : List Val → Option (List Val) → Option OSt
  | [.u32 rh], some [.variant 0 (some (.u32 b))] => some { st with body := (rh, b) :: st.body }
  | _, _ => none

/-- An answer of `outgoing-body.write`. -/
def oWrite (st : OSt) : List Val → Option (List Val) → Option OSt
  | [.u32 b], some [.variant 0 (some (.u32 s))] => some { st with stream := (s, b) :: st.stream }
  | _, _ => none

/-- A write of `bytes` to the outgoing body `b`, answered `r`. -/
def oBytes (st : OSt) (b : BitVec 32) (bytes : List (BitVec 8)) : Option (List Val) → Option OSt
  | some [.variant 0 none] => some { st with bytes := (b, (look b st.bytes).getD [] ++ bytes) :: st.bytes }
  | _ => none

/-- An answer of `blocking-write-and-flush`: only writes to the streams of outgoing bodies
count. -/
def oStream (st : OSt) : List Val → Option (List Val) → Option OSt
  | [.u32 s, buf], r =>
    match look s st.stream with
    | some b => oBytes st b (bytesOf buf) r
    | none => some st
  | _, _ => some st

/-- An answer of `outgoing-body.finish`. -/
def oFinish (st : OSt) : List Val → Option (List Val) → Option OSt
  | [.u32 b, _], some [.variant 0 none] => some { st with fin := b :: st.fin }
  | _, _ => none

/-- An answer of `response-outparam.set`, for the outparam `o`. -/
def oSet (o : BitVec 32) (st : OSt) : List Val → Option (List Val) → Option OSt
  | [.u32 o', .variant 0 (some (.u32 rh))], some [] =>
    if o' = o then some { st with set := some rh } else some st
  | _, _ => none

/-- One answer of a call whose outparam is `o` (`none`: the response failed). -/
def ostep (o : BitVec 32) (st : OSt) : WEv → Option OSt
  | .imp f a r =>
    if f = setStatus then oStatus st a r
    else if f = respBody then oBody st a r
    else if f = bodyWrite then oWrite st a r
    else if f = streamWrite then oStream st a r
    else if f = bodyFinish then oFinish st a r
    else if f = outSet then oSet o st a r
    else some st
  | .req _ _ => some st
  | .call _ _ => some st
  | .ret _ _ _ => some st

/-- The response of a finished account `st`. -/
def OSt.resp (st : OSt) : Option Response :=
  match st.set with
  | none => none
  | some rh =>
    match look rh st.body with
    | none => none
    | some b =>
      if st.fin.contains b then
        some (Response.simple ((look rh st.status).getD 200).toNat
          (((look b st.bytes).getD []).map UInt8.ofBitVec))
      else none

/-- **The response of a call** whose outparam is `o`, from the events of the call. -/
def respOf (o : BitVec 32) (u : List WEv) : Option Response :=
  (u.foldlM (ostep o) {}).bind OSt.resp

/-! ## The request of a call -/

/-- An answer consistent with the request `q` on the request handle `r`. -/
def ReqOk (q : Request) (r : BitVec 32) : WEv → Prop
  | .imp f (.u32 r' :: _) res =>
    r' = r → (f = reqMethod → res = some [methodV q.method]) ∧
      (f = reqPath → res = some [pathV q.target.pathWithQuery])
  | _ => True

/-! ## Components as HTTP servers -/

/-- HTTP requests and responses (`Silmaril.Net.Http`). -/
def httpIface : Iface := ⟨Request, Response⟩

/-- A call of `handle` with a response. -/
def answered (c : Call) : Bool := c.fn == handleF && (respOf (outOf c.args) c.inner).isSome

/-- The exchange of a call of `handle(r, o)`. -/
def Obs (c : Call) (x : Exch httpIface) : Prop :=
  c.fn = handleF ∧ (∀ e ∈ c.inner, ReqOk x.1 (reqOf c.args) e) ∧
    respOf (outOf c.args) c.inner = some x.2

/-- **A proxy component read as an HTTP server.** -/
def wasiServer {X : Set FnName} (σ : Strategy (nsig proxyImports) (nsig X)) : Model httpIface :=
  model (fun _ => True) answered Obs σ

end Silmaril.Servers.WasiHttp
