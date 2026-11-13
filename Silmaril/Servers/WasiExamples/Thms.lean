module

public import Silmaril.Servers.WasiExamples.Defs
public import Silmaril.Servers.Basic.Thms
public import Silmaril.Servers.Calls.Thms
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
  path-with-query; `route_refines`: `route` refines the server of that function.

Proofs in `Silmaril.Proofs.Servers.WasiExamples.Answer`.
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

/-- **Routing answers from the route table** on the request's path, for every host. -/
theorem route_sat :
    Sat (wasiServer (ofBody route)) (each fun q resp => resp = routeResp q.target.pathWithQuery) :=
  Proofs.Servers.WasiExamples.route_sat

/-- Routing refines the server of the route table. -/
theorem route_refines :
    Refines (wasiServer (ofBody route)) (ofFun fun q => routeResp q.target.pathWithQuery) :=
  fun t ht => route_sat t ht

end Silmaril.Servers.WasiExamples
