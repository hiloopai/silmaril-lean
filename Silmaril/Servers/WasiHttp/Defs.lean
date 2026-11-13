module

public import Silmaril.Servers.Calls.Defs
public import Silmaril.Wasi.Theory.Defs
public import Silmaril.Net.Http.Message.Defs
public import Silmaril.Wasi.Versions.Net.Defs

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
* `[method]incoming-request.consume() -> result<incoming-body>` and
  `[method]incoming-body.stream() -> result<input-stream>` (`reqConsume`, `inStream`);
* `[method]incoming-request.headers() -> headers` (`reqHeaders`), and on header fields
  `[method]fields.get(name: field-name) -> list<field-value>` and `[method]fields.entries() ->
  list<tuple<field-name, field-value>>` (`fieldsGet`, `fieldsEntries`);
* `[constructor]fields()`, `[method]fields.append(name: field-name, value: field-value) ->
  result<_, header-error>` and `[constructor]outgoing-response(headers: headers)` (`newFields`,
  `fieldsAppend`, `newResp`);
* `[method]outgoing-response.set-status-code(status-code: u16) -> result` and
  `body() -> result<outgoing-body>` (`setStatus`, `respBody`);
* `[method]outgoing-body.write() -> result<output-stream>` and `[static]outgoing-body.finish(
  this: outgoing-body, trailers: option<trailers>) -> result<_, error-code>` (`bodyWrite`,
  `bodyFinish`);
* `[static]response-outparam.set(param: response-outparam, response: result<outgoing-response,
  error-code>)` (`outSet`);

and from `wasi:io/streams` `[method]output-stream.blocking-write-and-flush`,
`[resource-drop]output-stream` (`Silmaril.Wasi.streamWrite`, `streamDrop`) and
`[method]input-stream.blocking-read(len: u64) -> result<list<u8>, stream-error>` (`inRead`;
`stream-error` has the cases `last-operation-failed` (`0`) and `closed` (`1`)). The names follow
the unversioned 0.2 convention of `Silmaril.Wasi.Versions.Net`. Values are encoded as in
`Silmaril.Wasi.Theory`: handles as `u32`, `result` and `option` as variants (`ok`/`none` case
`0`), strings as records of `char`s (read back as octets by `octet`: a `char` beyond `U+00FF`
reads as `0xFF`, never as an ASCII octet), `method` by its WIT case number, a `field-value` as
the record of its `u8`s, a field line as the record of its name and value (`lineV`).

## Reading a component as an HTTP server

The interface is `httpIface`: requests and responses of `Silmaril.Net.Http` (RFC 9110 §6). A
completed call of `handle(r, o)` is read as one atomic exchange (`Silmaril.Servers.Calls`):

* **its response** (`respOf o`): the response passed to `response-outparam.set(o, ok(rh))`,
  with the status of the last accepted `set-status-code` on `rh` (default `200`, as the WIT
  says), as header section the lines accepted by `fields.append` on the fields `rh` was
  constructed from, in order, and as content the bytes written through the output streams of
  the body of `rh`, which must be finished. Only the host's answers are read (`OSt`, `ostep`): a
  failed or ill-typed answer to one of the response's operations (or to any `fields.append` of
  the call) makes the response unobservable (`none`), as does a missing `set` or `finish`.
  **`set` may be called once** (it consumes the outparam): a second `set` of the outparam makes
  the response unobservable. Writes to other streams (stdout, say) are ignored.
* **its request**: any request consistent with what the host answered on `r`: the `method`
  and `path-with-query` answers on `r` encode the request's method and path (`ReqOk`), and the
  `get` and `entries` answers on the headers taken from `r` are the request's field values for
  that name (case-insensitively) and its whole header section (`HdrOk`). The rest of the
  request (authority, content) is left open.

**With request bodies** (`wasiServerB`): the bytes the host delivers by `blocking-read` on the
input streams of the bodies consumed from `r` (`ISt`, `istep`) are, after every prefix of the
call, a prefix of the request's content, and all of it once a read answers `closed`
(`BodyOk`). `wasiServerB σ` refines `wasiServer σ`.

`wasiServer σ` is the server read from the component `σ` (`Calls.model`, with no theory of
the host). Its traces include every interaction with every host, since the imports of `σ` are
uninterpreted. A host whose request answers are not those of any request explains no trace.

**Not modelled**: headers added to a response after its construction
(`outgoing-response.headers`), `fields.set`/`delete`/`from-list`, trailers, `send-informational`,
resource drops other than the output stream's, and concurrent export calls (a component body
runs one call at a time).

## Linked systems

`linkServer η σ` is the server read from the system `Silmaril.Wasi.link η σ` of the component
`σ` over a host `η`: the exchanges of the component's calls in the plays that take part in the
link. It refines `wasiServer σ` (`Silmaril.Servers.WasiHttp.Thms`), so every specification
proved of `wasiServer σ` holds over every host.

A Silmaril addition.
-/

namespace Silmaril.Servers.WasiHttp

open Silmaril.Servers.Exchange
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

/-- `wasi:http/types.[method]incoming-request.headers`. -/
def reqHeaders : FnName := ⟨"wasi:http/types", "[method]incoming-request.headers"⟩
/-- `wasi:http/types.[method]fields.get`. -/
def fieldsGet : FnName := ⟨"wasi:http/types", "[method]fields.get"⟩
/-- `wasi:http/types.[method]fields.entries`. -/
def fieldsEntries : FnName := ⟨"wasi:http/types", "[method]fields.entries"⟩
/-- `wasi:http/types.[method]fields.append`. -/
def fieldsAppend : FnName := ⟨"wasi:http/types", "[method]fields.append"⟩

/-- `wasi:http/types.[method]incoming-request.consume`. -/
def reqConsume : FnName := ⟨"wasi:http/types", "[method]incoming-request.consume"⟩
/-- `wasi:http/types.[method]incoming-body.stream` (the WIT name is `%stream`). -/
def inStream : FnName := ⟨"wasi:http/types", "[method]incoming-body.stream"⟩
/-- `wasi:io/streams.[method]input-stream.blocking-read`. -/
def inRead : FnName := ⟨"wasi:io/streams", "[method]input-stream.blocking-read"⟩

/-- The imports of this slice, as a list. -/
def proxyList : List FnName :=
  [reqMethod, reqPath, newFields, newResp, setStatus, respBody, bodyWrite, bodyFinish, outSet,
    streamWrite, streamDrop, reqConsume, inStream, inRead, reqHeaders, fieldsGet, fieldsEntries,
    fieldsAppend]

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

/-- A `string` of octets (each octet a `char`). -/
def strV (p : List UInt8) : Val := .record (p.map fun b => .char (Char.ofNat b.toNat))

/-- An `option<string>` of octets. -/
def pathV : Option (List UInt8) → Val
  | none => .variant 0 none
  | some p => .variant 1 (some (strV p))

/-- The octet of a `char`: itself up to `U+00FF`, else `0xFF` (not an ASCII octet). -/
def octet (c : Char) : UInt8 := if c.toNat < 256 then c.toNat.toUInt8 else 255

/-- The octets of the `char`s of a string (other values are skipped). -/
def octetsOf (cs : List Val) : List UInt8 :=
  cs.filterMap fun | .char c => some (octet c) | _ => none

/-- A `field-value` (or any `list<u8>`) of octets. -/
def octV (v : List UInt8) : Val := bytesV (v.map UInt8.toBitVec)

/-- A field line: the tuple of its name and value. -/
def lineV (l : Silmaril.Net.Http.Field.Line) : Val := .record [strV l.name, octV l.value]

/-- A header section: the list of its lines. -/
def sectionV (s : Silmaril.Net.Http.Field.Section) : Val := .record (s.map lineV)

/-- A `list<field-value>`. -/
def valuesV (vs : List (List UInt8)) : Val := .record (vs.map octV)

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
  /-- The lines appended to each fields resource. -/
  fields : List (BitVec 32 × Silmaril.Net.Http.Field.Section) := []
  /-- The fields each outgoing response was constructed from. -/
  hdr : List (BitVec 32 × BitVec 32) := []

/-- An answer of `set-status-code`. -/
def oStatus (st : OSt) : List Val → Option (List Val) → Option OSt
  | [.u32 rh, .u16 s], some [.variant 0 none] => some { st with status := (rh, s) :: st.status }
  | _, _ => none

/-- An answer of `[constructor]outgoing-response`. -/
def oNew (st : OSt) : List Val → Option (List Val) → Option OSt
  | [.u32 fh], some [.u32 rh] => some { st with hdr := (rh, fh) :: st.hdr }
  | _, _ => none

/-- An answer of `fields.append`. -/
def oAppend (st : OSt) : List Val → Option (List Val) → Option OSt
  | [.u32 fh, .record cs, v], some [.variant 0 none] =>
    some { st with fields := (fh, ((look fh st.fields).getD []).append (octetsOf cs)
      ((bytesOf v).map UInt8.ofBitVec)) :: st.fields }
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

/-- An answer of `response-outparam.set`, for the outparam `o`: the outparam is consumed, so a
second `set` of it fails. -/
def oSet (o : BitVec 32) (st : OSt) : List Val → Option (List Val) → Option OSt
  | [.u32 o', .variant 0 (some (.u32 rh))], some [] =>
    if o' = o then (if st.set.isSome then none else some { st with set := some rh }) else some st
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
    else if f = newResp then oNew st a r
    else if f = fieldsAppend then oAppend st a r
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
        some ⟨((look rh st.status).getD 200).toNat,
          ((look rh st.hdr).bind fun fh => look fh st.fields).getD [],
          ((look b st.bytes).getD []).map UInt8.ofBitVec, []⟩
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

/-- The headers resources answered by `headers()` on the request handle `r`. -/
def reqHs (r : BitVec 32) (v : List WEv) : List (BitVec 32) :=
  v.filterMap fun
    | .imp f [.u32 r'] (some [.u32 h]) => if f = reqHeaders ∧ r' = r then some h else none
    | _ => none

/-- An answer consistent with the header section of the request `q`, on the headers
resources `hs` of the request. -/
def HdrAns (q : Request) (hs : List (BitVec 32)) : WEv → Prop
  | .imp f (.u32 h :: a) res =>
    h ∈ hs → (f = fieldsGet → ∀ cs, a = [.record cs] →
        res = some [valuesV (q.headers.values (octetsOf cs))]) ∧
      (f = fieldsEntries → a = [] → res = some [sectionV q.headers])
  | _ => True

/-- The header answers of a call on the request handle `r` are consistent with the request
`q`: each answer, given the headers resources taken from `r` before it. -/
def HdrOk (q : Request) (r : BitVec 32) (u : List WEv) : Prop :=
  ∀ v e w, u = v ++ e :: w → HdrAns q (reqHs r v) e

/-! ## Components as HTTP servers -/

/-- HTTP requests and responses (`Silmaril.Net.Http`). -/
def httpIface : Iface := ⟨Request, Response⟩

/-- A call of `handle` with a response. -/
def answered (c : Call) : Bool := c.fn == handleF && (respOf (outOf c.args) c.inner).isSome

/-- The exchange of a call of `handle(r, o)`. -/
def Obs (c : Call) (x : Exch httpIface) : Prop :=
  c.fn = handleF ∧ (∀ e ∈ c.inner, ReqOk x.1 (reqOf c.args) e) ∧
    HdrOk x.1 (reqOf c.args) c.inner ∧ respOf (outOf c.args) c.inner = some x.2

/-- **A proxy component read as an HTTP server.** -/
def wasiServer {X : Set FnName} (σ : Strategy (nsig proxyImports) (nsig X)) :
    Exchange.Model httpIface :=
  model (fun _ => True) answered Obs σ

/-! ## Request bodies -/

/-- What the answers of a call say about its request's content. -/
structure ISt where
  /-- The incoming bodies consumed from the request. -/
  bodies : List (BitVec 32) := []
  /-- The input streams of those bodies. -/
  streams : List (BitVec 32) := []
  /-- The bytes delivered on those streams. -/
  got : List (BitVec 8) := []
  /-- A read answered `closed`. -/
  closed : Bool := false

/-- An answer of `consume` on the request handle `r`. -/
def iConsume (r : BitVec 32) (st : ISt) : List Val → Option (List Val) → ISt
  | [.u32 r'], some [.variant 0 (some (.u32 b))] =>
    if r' = r then { st with bodies := b :: st.bodies } else st
  | _, _ => st

/-- An answer of `incoming-body.stream`. -/
def iStream (st : ISt) : List Val → Option (List Val) → ISt
  | [.u32 b], some [.variant 0 (some (.u32 s))] =>
    if st.bodies.contains b then { st with streams := s :: st.streams } else st
  | _, _ => st

/-- An answer of `blocking-read`. -/
def iRead (st : ISt) : List Val → Option (List Val) → ISt
  | .u32 s :: _, some [.variant 0 (some bs)] =>
    if st.streams.contains s then { st with got := st.got ++ bytesOf bs } else st
  | .u32 s :: _, some [.variant 1 (some (.variant 1 none))] =>
    if st.streams.contains s then { st with closed := true } else st
  | _, _ => st

/-- One answer of a call on the request handle `r`. -/
def istep (r : BitVec 32) (st : ISt) : WEv → ISt
  | .imp f a res =>
    if f = reqConsume then iConsume r st a res
    else if f = inStream then iStream st a res
    else if f = inRead then iRead st a res
    else st
  | .req _ _ => st
  | .call _ _ => st
  | .ret _ _ _ => st

/-- The delivered bytes are a prefix of `c`, and all of `c` once the body is closed. -/
def ISt.Ok (c : List (BitVec 8)) (st : ISt) : Prop := st.got <+: c ∧ (st.closed = true → st.got = c)

/-- The body reads of a call are consistent with the content of the request `q`. -/
def BodyOk (q : Request) (r : BitVec 32) (u : List WEv) : Prop :=
  ∀ v, v <+: u → (v.foldl (istep r) {}).Ok (q.content.map UInt8.toBitVec)

/-- The exchange of a call, reading request bodies. -/
def ObsB (c : Call) (x : Exch httpIface) : Prop := Obs c x ∧ BodyOk x.1 (reqOf c.args) c.inner

/-- **A proxy component read as an HTTP server, with request bodies.** -/
def wasiServerB {X : Set FnName} (σ : Strategy (nsig proxyImports) (nsig X)) :
    Exchange.Model httpIface :=
  model (fun _ => True) answered ObsB σ

/-! ## A reference host -/

/-- An answer of `blocking-read`. -/
def isReadAns : WEv → Bool
  | .imp f _ _ => decide (f = inRead)
  | _ => false

/-- The call `handle(0, 1)`. -/
def handleQ : (nsig proxyWorld.exports).Op := (⟨handleF, rfl⟩, [.u32 0, .u32 1])

/-- **A reference host** serving the request `q` on the request handle `0`: the getters answer
from `q` (`get` and `entries` from its header section, on any fields), constructors,
`headers`, `consume`, `stream`, `body` and `write` answer fresh handles, the first
`blocking-read` delivers the whole content and later ones answer `closed`, and the other
operations succeed. -/
def refHost (q : Request) : Impl := fun past f a =>
  if f = reqMethod then some [methodV q.method]
  else if f = reqPath then some [pathV q.target.pathWithQuery]
  else if f = fieldsGet then
    match a with
    | [_, .record cs] => some [valuesV (q.headers.values (octetsOf cs))]
    | _ => none
  else if f = fieldsEntries then some [sectionV q.headers]
  else if f = fieldsAppend then some [okV none]
  else if f = newFields ∨ f = newResp ∨ f = reqHeaders then
    some [.u32 (BitVec.ofNat 32 (past.length + 2))]
  else if f = respBody ∨ f = bodyWrite then some [okV (some (.u32 (BitVec.ofNat 32 (past.length + 2))))]
  else if f = setStatus ∨ f = streamWrite ∨ f = bodyFinish then some [okV none]
  else if f = streamDrop ∨ f = outSet then some []
  else if f = reqConsume ∨ f = inStream then
    some [okV (some (.u32 (BitVec.ofNat 32 (past.length + 2))))]
  else if f = inRead then
    if past.any isReadAns then some [errV (some (.variant 1 none))]
    else some [okV (some (bytesV (q.content.map UInt8.toBitVec)))]
  else none

/-- The response of the body `h` to the request `q` over the reference host. -/
def serveRef (h : Body proxyImports proxyWorld.exports) (q : Request) : Option Response :=
  respOf 1 (runP (refHost q) [] (h handleQ)).1

/-! ## Linked systems -/

/-- **The server of a linked system**: the exchanges of the component's calls in the plays of
`σ` that interact with a play of the host `η` (the plays behind `link η σ`). -/
def linkServer {Y : Silmaril.Games.Sig.{0}} {X : Set FnName} (η : Host Y proxyImports)
    (σ : Strategy (nsig proxyImports) (nsig X)) : Exchange.Model httpIface :=
  {t | ∃ s ∈ η, ∃ u ∈ σ, ∃ p, Zip s u p ∧
    List.Forall₂ Obs ((calls (wtrace u)).filter answered) t}

/-- The server of a linked system, reading request bodies. -/
def linkServerB {Y : Silmaril.Games.Sig.{0}} {X : Set FnName} (η : Host Y proxyImports)
    (σ : Strategy (nsig proxyImports) (nsig X)) : Exchange.Model httpIface :=
  {t | ∃ s ∈ η, ∃ u ∈ σ, ∃ p, Zip s u p ∧
    List.Forall₂ ObsB ((calls (wtrace u)).filter answered) t}

/-! ## Binaries -/

/-- **The strategy `σ` runs the body `h`**: every play of `σ` is a play of `ofBody h`. A
component binary whose denotation `σ` runs `h` inherits every specification proved of `h`
(`Silmaril.Servers.WasiHttp.Thms`). -/
def Runs {X : Set FnName} (σ : Strategy (nsig proxyImports) (nsig X))
    (h : Body proxyImports X) : Prop :=
  ∀ s ∈ σ, s ∈ ofBody h

/-- A `GET` request for an authority and a path-with-query, with no fields or content. -/
def getAt (authority path : Option (List UInt8)) : Request :=
  ⟨⟨.get, ⟨none, authority, path⟩⟩, [], [], []⟩

/-! ## Servers as webs of the outgoing theories -/

/-- **The web of a server** `f`, as the outgoing `wasi:http` theories see it
(`Silmaril.Wasi.Versions.Net.httpTh`, `httpTh3`): the status of `f`'s answer to a `GET` for the
authority and path-with-query of the outgoing request. -/
def webOf (f : Request → Response) : Silmaril.Wasi.Versions.Net.Web := fun a p =>
  .status (BitVec.ofNat 16 (f (getAt (pathOf (some [a])) (pathOf (some [p])))).status)

end Silmaril.Servers.WasiHttp
