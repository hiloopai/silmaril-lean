module

public import Silmaril.Servers.WasiExamples.Defs
public import Silmaril.Servers.Exchange.Thms
public import Silmaril.Servers.Calls.Thms
public import Silmaril.Servers.WasiHttp.Thms
public import Silmaril.Servers.Http.Defs
import Silmaril.Proofs.Servers.WasiExamples.Answer
import Silmaril.Proofs.Servers.WasiExamples.Echo

@[expose] public section

/-!
# Example `wasi:http` servers: correctness for every host

The specifications are sentences of the exchange servers (`Silmaril.Servers.Exchange`) over
`httpIface`, the core's HTTP interface `Http.sig` (`httpIface_eq`), satisfied by the components
read as servers (`wasiServer`). The imports of the
components are uninterpreted, so the statements hold for every host: a host can only make a
response unobservable (by failing an operation), never wrong.

* `answer_run`: a complete run of the shared response code `answer o resp` makes no response
  or the response `resp`, header lines included.
* **`hello_sat`**: every exchange of `hello` is answered `200 hello` with its
  `content-type: text/plain` header; `hello_refines`: `hello`
  refines the server of the constant function. `hello_answers`: every request answered
  `200 hello` is a trace of `hello` (the specification is not vacuous).
* **`route_sat`**: every exchange of `route` is answered from the route table on the request's
  path-with-query; `route_refines`: `route` refines the server of that function;
  `route_answers`: every request answered from the route table is a trace of `route`.
* **`echo_sat`**: over the reading with request bodies (`wasiServerB`), every exchange of `echo`
  answers `200` with the request's content, or `500` (when the host fails an operation or the
  reads run out).
* `serve_mem`: a response of a component over the reference host (`serveRef`) is a trace of
  the component read as a server.
* `answer_ok`: over a host whose answers to the response code succeed (`OkAns`), a complete
  run of `answer o resp` makes the response `resp`; `refHost_ok`: the reference host is such a
  host. `bytesOf_bytesV`, `map_ofBitVec_toBitVec`: byte lists back and forth.

Proofs in `Silmaril.Proofs.Servers.WasiExamples.Answer`.

**Checked** over the reference host (`serveRef`, evaluated by `decide`): `hello` on `/`,
`route` on `/`, `/hello` and `/missing`, and `echo` on a `POST` with content `abc`.
`hello_satB`: hello's specification over the reading with request bodies, by refinement.

**Linked systems**: `hello_link`, `route_link`, `echo_link`: the specifications hold of each
example linked over every host (`WasiHttp.linkServer`); `serve_link`: a response over the
reference host is a trace of the example linked over the concrete reference host.

**Binaries**: `Task.wasmRuns σh σr σe` (open) says that `σh`, `σr`, `σe`, the denotations of
the components built from `tests/servers/wasi-http/{hello,route,echo}.wat`, run the bodies
`hello`, `route`, `echo` (`WasiHttp.Runs`). No denotation of those binaries is defined here
yet; the evidence so far is the one-for-one correspondence of the WAT export functions to the
bodies and the conformance check against `wasmtime serve`. `wasm_sat`: given the task, the
components satisfy the specifications, alone and linked over every host.
`route_web_missing`: the web of the route table, as the outgoing `wasi:http` theories read it,
answers `404` for `/missing`.

**In the concurrent core** (`Silmaril.Servers.Core`), with a fresh instance per request
(`Exchange.fresh`, as `wasmtime serve` runs a 0.2 proxy component) and any overlap of requests:
`hello_fresh` and `route_fresh`: hello and route refine the core's function servers
(`Model.ofFun`); `echo_fresh_lin`: echo is linearizable for its specification. With one
instance used sequentially (`Exchange.seqUse`): `hello_seq_lin`.
-/

namespace Silmaril.Servers.WasiExamples

open Silmaril.Games Silmaril.Wasi Silmaril.Servers Silmaril.Servers.Exchange
open Silmaril.Servers.Calls Silmaril.Servers.WasiHttp
open Silmaril.Wasm.Component (Val)
open Silmaril.Net.Http (Request Response)

/-- **The shared response code**: for every host, no response or `resp` (when `resp` has no
trailers and a 16-bit status). -/
theorem answer_run {o : BitVec 32} {resp : Response} {u : List WEv} {r : Option (List Val)}
    (hr : resp.trailers = []) (hs : resp.status < 2 ^ 16)
    (hl : Leads (answer o resp) u (.pure r)) : respOf o u = none ∨ respOf o u = some resp :=
  Proofs.Servers.WasiExamples.answer_run hr hs hl

/-- **Over a host whose answers succeed**, the response code makes its response. -/
theorem answer_ok {o : BitVec 32} {resp : Response} {u : List WEv} {r : Option (List Val)}
    (hr : resp.trailers = []) (hs : resp.status < 2 ^ 16)
    (hl : Leads (answer o resp) u (.pure r)) (hok : ∀ f a n, WEv.imp f a n ∈ u → OkAns f n) :
    respOf o u = some resp :=
  Proofs.Servers.WasiExamples.answer_ok hr hs hl hok

/-- The reference host's answers succeed. -/
theorem refHost_ok (q : Request) (past : List WEv) (f : FnName) (a : List Val) :
    OkAns f (refHost q past f a) :=
  Proofs.Servers.WasiExamples.refHost_ok q past f a

theorem bytesOf_bytesV (bs : List (BitVec 8)) : bytesOf (bytesV bs) = bs :=
  Proofs.Servers.WasiExamples.bytesOf_bytesV bs

theorem map_ofBitVec_toBitVec (c : List UInt8) :
    (c.map UInt8.toBitVec).map UInt8.ofBitVec = c :=
  Proofs.Servers.WasiExamples.map_ofBitVec_toBitVec c

/-- **Hello answers `200 hello`**, for every host. -/
theorem hello_sat : Sat (wasiServer (ofBody hello)) (each fun _ resp => resp = helloResp) :=
  Proofs.Servers.WasiExamples.hello_sat

/-- Hello refines the server of the constant function `200 hello`. -/
theorem hello_refines : Refines (wasiServer (ofBody hello)) (ofFun fun _ => helloResp) :=
  fun t ht => hello_sat t ht

/-- **Hello is not vacuous**: every request answered `200 hello` is one of its traces. -/
theorem hello_answers (q : Request) : [(q, helloResp)] ∈ wasiServer (ofBody hello) :=
  Proofs.Servers.WasiExamples.hello_answers q

/-- **A response over the reference host is a trace** of the component read as a server. -/
theorem serve_mem {h : Body proxyImports proxyWorld.exports} {q : Request} {x : Response}
    (hx : serveRef h q = some x) : [(q, x)] ∈ wasiServer (ofBody h) :=
  Proofs.Servers.WasiExamples.serve_mem hx

/-- **Routing answers from the route table** on the request's path, for every host. -/
theorem route_sat :
    Sat (wasiServer (ofBody route)) (each fun q resp => resp = routeResp q.target.pathWithQuery) :=
  Proofs.Servers.WasiExamples.route_sat

/-- Routing refines the server of the route table. -/
theorem route_refines :
    Refines (wasiServer (ofBody route)) (ofFun fun q => routeResp q.target.pathWithQuery) :=
  fun t ht => route_sat t ht

/-- **Echo answers `200` with the request's content, or `500`**, for every host. -/
theorem echo_sat : Sat (wasiServerB (ofBody echo))
    (each fun q resp => resp = Response.simple 200 q.content ∨ resp = failResp) :=
  Proofs.Servers.WasiExamples.echo_sat

/-- **Routing is not vacuous**: every request answered from the route table is a trace. -/
theorem route_answers (q : Request) :
    [(q, routeResp q.target.pathWithQuery)] ∈ wasiServer (ofBody route) :=
  Proofs.Servers.WasiExamples.route_answers q

/-! ## Checked over the reference host -/

theorem hello_ref : serveRef hello (getAt none (some (ascii "/"))) = some helloResp :=
  Proofs.Servers.WasiExamples.hello_serveRef _

theorem echo_ref : serveRef echo (⟨⟨.post, ⟨none, none, some (ascii "/")⟩⟩, [], ascii "abc", []⟩) =
    some (Response.simple 200 (ascii "abc")) := by
  decide

/-- Hello over the reading with request bodies. -/
theorem hello_satB : Sat (wasiServerB (ofBody hello)) (each fun _ resp => resp = helloResp) :=
  (wasiServerB_refines _).sat hello_sat

theorem route_ref_root :
    serveRef route (getAt none (some (ascii "/"))) = some (Response.simple 200 (ascii "home")) := by
  rw [Proofs.Servers.WasiExamples.route_serveRef]
  decide

theorem route_ref_hello : serveRef route (getAt none (some (ascii "/hello"))) =
    some (Response.simple 200 (ascii "hello")) := by
  rw [Proofs.Servers.WasiExamples.route_serveRef]
  decide

theorem route_ref_missing : serveRef route (getAt none (some (ascii "/missing"))) =
    some (Response.simple 404 (ascii "not found")) := by
  rw [Proofs.Servers.WasiExamples.route_serveRef]
  decide

/-- The web of the route table answers `404` for `/missing`. -/
theorem route_web_missing :
    webOf (fun q => routeResp q.target.pathWithQuery) (pathV none) (pathV (some (ascii "/missing"))) =
      .status 404 := by
  rw [webOf_pathV]
  rfl

/-! ## In the concurrent core -/

/-- The interface of the `wasi:http` reading is the core's HTTP interface. -/
theorem httpIface_eq : httpIface = Http.sig := rfl

/-- **Hello, with a fresh instance per request, refines the core's function server** of the
constant `200 hello`, however requests overlap. -/
theorem hello_fresh : (Exchange.fresh (wasiServer (ofBody hello))).Refines
    (Servers.Model.ofFun fun _ => helloResp) :=
  Exchange.fresh_ofFun_refines hello_refines

/-- **Routing, with a fresh instance per request, refines the core's function server** of the
route table. -/
theorem route_fresh : (Exchange.fresh (wasiServer (ofBody route))).Refines
    (Servers.Model.ofFun fun q => routeResp q.target.pathWithQuery) :=
  Exchange.fresh_ofFun_refines route_refines

/-- **Echo, with a fresh instance per request, is linearizable** for its specification. -/
theorem echo_fresh_lin : (Exchange.fresh (wasiServerB (ofBody echo))).Sat
    (Servers.Sen.lin (SeqSpec.pointwise fun q resp =>
      resp = Response.simple 200 q.content ∨ resp = failResp)) :=
  Exchange.fresh_sat_lin echo_sat

/-- Hello, one instance used sequentially, is linearizable for its specification. -/
theorem hello_seq_lin : (Exchange.seqUse (wasiServer (ofBody hello))).Sat
    (Servers.Sen.lin (each fun _ resp => resp = helloResp)) :=
  Exchange.seqUse_sat_lin hello_sat

/-! ## Linked systems -/

section Link

variable {Y : Silmaril.Games.Sig.{0}}

/-- **Hello, linked over every host**, answers `200 hello`. -/
theorem hello_link (η : Host Y proxyImports) :
    Sat (linkServer η (ofBody hello)) (each fun _ resp => resp = helloResp) :=
  link_sat_of hello_sat η

/-- **Routing, linked over every host**, answers from the route table. -/
theorem route_link (η : Host Y proxyImports) :
    Sat (linkServer η (ofBody route)) (each fun q resp => resp = routeResp q.target.pathWithQuery) :=
  link_sat_of route_sat η

/-- **Echo, linked over every host**, answers `200` with the request's content, or `500`. -/
theorem echo_link (η : Host Y proxyImports) :
    Sat (linkServerB η (ofBody echo))
      (each fun q resp => resp = Response.simple 200 q.content ∨ resp = failResp) :=
  link_satB_of echo_sat η

/-- **A response over the reference host is a trace of the linked system** of the component and
the concrete reference host. -/
theorem serve_link {h : Body proxyImports proxyWorld.exports} {q : Request} {x : Response}
    (hx : serveRef h q = some x) : [(q, x)] ∈ linkServer (Y := Y) (concrete (refHost q)) (ofBody h) :=
  Proofs.Servers.WasiExamples.serve_link hx

/-- Hello over the linked reference host: `200 hello` for every request. -/
theorem hello_link_answers (q : Request) :
    [(q, helloResp)] ∈ linkServer (Y := Y) (concrete (refHost q)) (ofBody hello) :=
  Proofs.Servers.WasiExamples.serve_link (Proofs.Servers.WasiExamples.hello_serveRef q)

end Link

/-! ## Binaries -/

/-- **Open**: the denotations `σh`, `σr`, `σe` of the components built from
`tests/servers/wasi-http` run the bodies `hello`, `route` and `echo`. -/
def Task.wasmRuns (σh σr σe : Strategy (nsig proxyImports) (nsig proxyWorld.exports)) : Prop :=
  Runs σh hello ∧ Runs σr route ∧ Runs σe echo

/-- **Given `Task.wasmRuns`**, the components satisfy the examples' specifications, alone and
linked over every host. -/
theorem wasm_sat {σh σr σe : Strategy (nsig proxyImports) (nsig proxyWorld.exports)}
    (ht : Task.wasmRuns σh σr σe) :
    Sat (wasiServer σh) (each fun _ resp => resp = helloResp) ∧
      Sat (wasiServer σr) (each fun q resp => resp = routeResp q.target.pathWithQuery) ∧
      Sat (wasiServerB σe)
        (each fun q resp => resp = Response.simple 200 q.content ∨ resp = failResp) ∧
      ∀ {Y : Silmaril.Games.Sig.{0}} (η : Host Y proxyImports),
        Sat (linkServer η σh) (each fun _ resp => resp = helloResp) ∧
        Sat (linkServer η σr) (each fun q resp => resp = routeResp q.target.pathWithQuery) ∧
        Sat (linkServerB η σe)
          (each fun q resp => resp = Response.simple 200 q.content ∨ resp = failResp) := by
  obtain ⟨hh, hr, he⟩ := ht
  have h1 := (runs_refines hh).sat hello_sat
  have h2 := (runs_refines hr).sat route_sat
  have h3 := (runs_refinesB he).sat echo_sat
  exact ⟨h1, h2, h3, fun η => ⟨link_sat_of h1 η, link_sat_of h2 η, link_satB_of h3 η⟩⟩

end Silmaril.Servers.WasiExamples
