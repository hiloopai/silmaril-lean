module

public import Silmaril.Servers.WasiHttp.Defs

@[expose] public section

/-!
# Example `wasi:http` servers

Two components of the proxy world slice (`Silmaril.Servers.WasiHttp`), given by their bodies
(`Silmaril.Wasi.Comp`): programs over the imports for each call of `handle(r, o)`. They are
written directly as programs over the imports, not compiled from Wasm modules.

* `answer o resp`: the shared response code. It creates the header fields and an outgoing
  response, sets the status of `resp`, takes the response's body, passes the response to
  `response-outparam.set(o, ok(_))`, writes the content of `resp` to the body's output stream
  with `blocking-write-and-flush`, drops the stream and finishes the body. It does not inspect
  the host's answers beyond reading handles (`hOf`): whether they make a response is decided
  by the reading of the trace (`respOf`). The order (`set` before writing the body) is the one
  the `wasi:http` documentation recommends, so that a host may stream the body.
* `hello`: every request is answered `200` with the content `hello` (`helloResp`).
* `route`: the response depends on the path-with-query (`routeResp`): `/` gives `200 home`,
  `/hello` gives `200 hello`, any other path (or none) gives `404 not found`.

A Silmaril addition.
-/

namespace Silmaril.Servers.WasiExamples

open Silmaril.Games Silmaril.Wasi Silmaril.Servers.WasiHttp
open Silmaril.Wasm.Component (Val)
open Silmaril.Net.Http (Request Response Method)

/-- An import call of the slice. -/
def pop (f : FnName) (hf : f ∈ proxyList := by simp [proxyList]) (a : List Val) :
    (nsig proxyImports).Op :=
  (⟨f, hf⟩, a)

/-- The octets of an ASCII string. -/
abbrev ascii : String → List UInt8 := Method.ascii

/-- **The shared response code**: answer the outparam `o` with the status and content of `resp`. -/
def answer (o : BitVec 32) (resp : Response) : BProg proxyImports :=
  .call (pop newFields (a := [])) fun n1 =>
  .call (pop newResp (a := [.u32 (hOf n1)])) fun n2 =>
  .call (pop setStatus (a := [.u32 (hOf n2), .u16 (BitVec.ofNat 16 resp.status)])) fun _ =>
  .call (pop respBody (a := [.u32 (hOf n2)])) fun n4 =>
  .call (pop outSet (a := [.u32 o, okV (some (.u32 (hOf n2)))])) fun _ =>
  .call (pop bodyWrite (a := [.u32 (hOf n4)])) fun n6 =>
  .call (pop streamWrite (a := [.u32 (hOf n6), bytesV (resp.content.map UInt8.toBitVec)])) fun _ =>
  .call (pop streamDrop (a := [.u32 (hOf n6)])) fun _ =>
  .call (pop bodyFinish (a := [.u32 (hOf n4), .variant 0 none])) fun _ =>
  .pure (some [])

/-! ## Hello -/

/-- `200 hello`. -/
def helloResp : Response := Response.simple 200 (ascii "hello")

/-- **Hello**: every request is answered `200 hello`. -/
def hello : Body proxyImports proxyWorld.exports := fun q => answer (outOf q.2) helloResp

/-! ## Routing -/

/-- The route table: `/` and `/hello`, else `404`. -/
def routeResp (p : Option (List UInt8)) : Response :=
  if p = some (ascii "/") then Response.simple 200 (ascii "home")
  else if p = some (ascii "/hello") then Response.simple 200 (ascii "hello")
  else Response.simple 404 (ascii "not found")

/-- **Routing**: read the path-with-query of the request and answer from the route table. -/
def route : Body proxyImports proxyWorld.exports := fun q =>
  .call (pop reqPath (a := [.u32 (reqOf q.2)])) fun n => answer (outOf q.2) (routeResp (pathOf n))

end Silmaril.Servers.WasiExamples
