module

public import Silmaril.Servers.Wire1.Defs
public import Silmaril.Servers.WasiExamples.Defs

/-!
# Comparing a `wasi:http` component with a Linux process: hello

The first cross-platform refinement with HTTP/1.1 on the wire. Two platforms with sequential
logs (`Silmaril.Servers.Platform`):

* `wasi`: a `wasi:http` proxy component (`Silmaril.Servers.WasiHttp`), run as `wasmtime serve`
  runs a 0.2 component, a fresh instance per request: every exchange of the log is a
  one-exchange trace of the component read as a server (`wasiServer`);
* `linux1`: a Linux process serving HTTP/1.1 over sockets (`Platform.linux`), its connections
  framed by `Wire1.framing` and their logs merged into sequential logs (`Platform.merged`).

The Linux side is a hypothesis about a program's socket semantics, not a binary:

* `ServesHello L inp`: for every sequence of wire requests that read back, some run of `L`
  accepts one connection, receives them back to back and sends `helloWire` (`200 OK`,
  `Content-Length: 5`, `hello`) once for each;
* `OnlyHello L inp`: every exchange of every connection of every run is answered with
  `helloResp`;
* `helloSock`: the reference hello server at the socket level, which satisfies both.

A component's log may contain requests that HTTP/1.1 cannot carry (invalid tokens, framing
fields in the header section), and the hello component answers `HEAD` with content, which an
HTTP/1.1 reader takes as no body (RFC 9112 §6.3 rule 1; RFC 9110 §9.3.2). So the component
refines the process on logs whose requests are on the wire (`wireLog`, `OnWire`: the reading of
a wire request that reads back, with a method other than `HEAD` and `CONNECT`), with
`restrict` cutting a platform down to such traces.

The theorems are in `Thms` (`wasi_refines_linux`, `linux_refines_wasi`, `hello_equiv`, and
the same in the server institution, `wasi_refines_linux_model`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Servers.Compare

open Silmaril.Games Silmaril.Wasi Silmaril.Servers.WasiHttp Silmaril.Servers.WasiExamples
open Silmaril.Servers.Platform Silmaril.Servers.Wire1 Silmaril.Servers.Reuse
open Silmaril.Net.Http (Request Response)
open Silmaril.Cli (Input)

/-- **A `wasi:http` proxy component, a fresh instance per request**: the log of exchanges, in
the order they complete, each a one-exchange trace of the component. -/
def wasi : Platform Log where
  Impl := Body proxyImports proxyWorld.exports
  Obs := Log
  runs b l := ∀ p ∈ l, [p] ∈ wasiServer (ofBody b)
  reads := Eq

/-- **A Linux process serving HTTP/1.1**, its connections' logs merged. -/
def linux1 : Platform Log := merged (linux framing)

/-- A platform cut down to the traces satisfying `D`. -/
def restrict {T : Type} (P : Platform T) (D : T → Prop) : Platform T :=
  { P with reads := fun o t => P.reads o t ∧ D t }

/-- A wire request that reads back, whose method is neither `HEAD` nor `CONNECT`. -/
def WireOk (m : WireReq) : Prop :=
  ReqOk m ∧ m.1.line.method ≠ Net.Http1.methodHEAD ∧ m.1.line.method ≠ Net.Http1.methodCONNECT

/-- **A request on the wire**: the reading of a wire request that reads back, whose method is
neither `HEAD` nor `CONNECT`. -/
def OnWire (q : Request) : Prop := ∃ m : WireReq, WireOk m ∧ toRequest m = q

/-- Every request of the log is on the wire. -/
def wireLog (l : Log) : Prop := ∀ p ∈ l, OnWire p.1

/-- The header section of the hello response on the wire. -/
def helloFields : List Net.Http1.FieldLine := [⟨Net.Http1.contentLengthName, Net.Http1.ascii "5"⟩]

/-- **The hello response on the wire**: `HTTP/1.1 200 OK`, `content-length: 5`, `hello`. -/
def helloWire : WireResp :=
  (⟨⟨⟨1, 1⟩, 200, Net.Http1.ascii "OK"⟩, helloFields⟩, .content helloResp.content)

/-- **A Linux hello server on one connection**: any requests on the wire, received back to
back on one accepted connection, are answered with `helloWire` each, in some run. -/
def ServesHello (L : SockSem) (inp : Input) : Prop :=
  ∀ ms : List WireReq, (∀ m ∈ ms, WireOk m) →
    ∃ tr, L inp tr ∧ accepted tr = [0] ∧ received 0 tr = encRequests ms ∧
      sent 0 tr = encResponses (ms.map fun _ => helloWire)

/-- **A Linux server that only says hello**: every exchange of every connection of every run is
answered `helloResp`. -/
def OnlyHello (L : SockSem) (inp : Input) : Prop :=
  ∀ tr, L inp tr → ∀ c, ∀ p ∈ connLog framing tr c, p.2 = helloResp

/-- **The reference Linux hello server**, as a socket semantics: one connection is accepted,
requests on the wire arrive back to back, and each is answered `helloWire`. It satisfies both
hypotheses (`Thms.helloSock_serves`, `Thms.helloSock_only`). -/
def helloSock : SockSem := fun _ tr =>
  ∃ ms : List WireReq, (∀ m ∈ ms, WireOk m) ∧
    tr = [.accept 0, .recv 0 (encRequests ms), .send 0 (encResponses (ms.map fun _ => helloWire))]

end Silmaril.Servers.Compare
