module

public import Silmaril.Servers.WasiExamples.Defs
public import Silmaril.Servers.Basic.Thms
public import Silmaril.Servers.Calls.Thms
public import Silmaril.Servers.WasiHttp.Thms
import Silmaril.Proofs.Servers.WasiExamples.Answer

@[expose] public section

/-!
# Example `wasi:http` servers: correctness for every host

The specifications are sentences of the atomic server interface (`Silmaril.Servers.Basic`) over
`httpIface`, satisfied by the components read as servers (`wasiServer`). The imports of the
components are uninterpreted, so the statements hold for every host: a host can only make a
response unobservable (by failing an operation), never wrong.

* `answer_run`: a complete run of the shared response code `answer o resp` makes no response
  or the response `resp`.
* **`hello_sat`**: every exchange of `hello` is answered `200 hello`; `hello_refines`: `hello`
  refines the server of the constant function. `hello_answers`: every request answered
  `200 hello` is a trace of `hello` (the specification is not vacuous).
* **`route_sat`**: every exchange of `route` is answered from the route table on the request's
  path-with-query; `route_refines`: `route` refines the server of that function;
  `route_answers`: every request answered from the route table is a trace of `route`.
* `serve_mem`: a response of a component over the reference host (`serveRef`) is a trace of
  the component read as a server.

Proofs in `Silmaril.Proofs.Servers.WasiExamples.Answer`.

**Checked** over the reference host (`serveRef`, evaluated by `decide`): `hello` on `/`,
`route` on `/`, `/hello` and `/missing`, and `echo` on a `POST` with content `abc`.
`hello_satB`: hello's specification over the reading with request bodies, by refinement.
**Open**: `Task.echo_sat`, the specification of `echo` for every host. `route_web_missing`: the web of the route table, as
the outgoing `wasi:http` theories read it, answers `404` for `/missing`.
-/

namespace Silmaril.Servers.WasiExamples

open Silmaril.Games Silmaril.Wasi Silmaril.Servers Silmaril.Servers.Calls Silmaril.Servers.WasiHttp
open Silmaril.Wasm.Component (Val)
open Silmaril.Net.Http (Request Response)

/-- **The shared response code**: for every host, no response or `resp` (when `resp` has no
fields and a 16-bit status). -/
theorem answer_run {o : BitVec 32} {resp : Response} {u : List WEv} {r : Option (List Val)}
    (hr : Response.simple resp.status resp.content = resp) (hs : resp.status < 2 ^ 16)
    (hl : Leads (answer o resp) u (.pure r)) : respOf o u = none ∨ respOf o u = some resp :=
  Proofs.Servers.WasiExamples.answer_run hr hs hl

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

/-- **Routing is not vacuous**: every request answered from the route table is a trace. -/
theorem route_answers (q : Request) :
    [(q, routeResp q.target.pathWithQuery)] ∈ wasiServer (ofBody route) :=
  Proofs.Servers.WasiExamples.route_answers q

/-! ## Checked over the reference host -/

theorem hello_ref : serveRef hello (getAt none (some (ascii "/"))) = some helloResp := by decide

theorem echo_ref : serveRef echo (⟨⟨.post, ⟨none, none, some (ascii "/")⟩⟩, [], ascii "abc", []⟩) =
    some (Response.simple 200 (ascii "abc")) := by
  decide

/-- Hello over the reading with request bodies. -/
theorem hello_satB : Sat (wasiServerB (ofBody hello)) (each fun _ resp => resp = helloResp) :=
  (wasiServerB_refines _).sat hello_sat

theorem route_ref_root :
    serveRef route (getAt none (some (ascii "/"))) = some (Response.simple 200 (ascii "home")) := by
  decide

theorem route_ref_hello : serveRef route (getAt none (some (ascii "/hello"))) =
    some (Response.simple 200 (ascii "hello")) := by
  decide

theorem route_ref_missing : serveRef route (getAt none (some (ascii "/missing"))) =
    some (Response.simple 404 (ascii "not found")) := by
  decide

/-- The web of the route table answers `404` for `/missing`. -/
theorem route_web_missing :
    webOf (fun q => routeResp q.target.pathWithQuery) (pathV none) (pathV (some (ascii "/missing"))) =
      .status 404 := by
  rw [webOf_pathV]
  rfl

end Silmaril.Servers.WasiExamples
