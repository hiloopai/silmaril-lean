module

public import Silmaril.Servers.Core.Defs
public import Silmaril.Net.Http.Exchange.Defs

/-!
# HTTP interfaces of the server institution

The HTTP instance of `Silmaril.Servers.Core`: the interfaces whose requests and responses are
the RFC 9110 messages of `Silmaril.Net.Http` (`Http.sig`), with coarser and finer views related
by morphisms:

| interface | request | response | morphism |
|---|---|---|---|
| `Http.statusSig` | `Request` | the status code | `Http.status : statusSig ⟶ sig` |
| `Http.pathSig` | the path and query | `Response` | `Http.path : pathSig ⟶ sig` |
| `Http.sig` | `Request` | `Response` (the final response) | |
| `Http.exchSig` | `Request` | interim responses and the final one (§15.2) | `Http.final : sig ⟶ exchSig` |

A sentence of a coarser view translates to the finer one (`Hom.sen`): "every response is 404"
at `statusSig` is a sentence about full responses; a sentence about final responses is one about
exchanges.

An origin server of `Silmaril.Net.Http` (`Origin σ`, a relation between resource states,
requests, responses and next states) is a machine of `Http.sig` (`Http.machine`); its
linearizability sentence (`Http.originSen`) is the trace reading of the origin: the responses on
all connections are explained by one sequential run of the origin. A web (`Origin.Web`, the
response for each target) gives the atomic sentence `Http.webSen`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Servers.Http

open Silmaril.Net.Http

/-- **The HTTP interface**: RFC 9110 requests and (final) responses. -/
def sig : Sig := ⟨Request, Response⟩

/-- The status view: requests and status codes. -/
def statusSig : Sig := ⟨Request, Status⟩

/-- The routing view: the path and query of a request, and the response. -/
def pathSig : Sig := ⟨Option (List UInt8), Response⟩

/-- The exchange view: requests, and the interim responses with the final response (§15.2). -/
def exchSig : Sig := ⟨Request, List Response × Response⟩

/-- The status view of the HTTP interface. -/
def status : statusSig ⟶ sig := (⟨id, Response.status⟩ : Hom statusSig sig)

/-- The routing view of the HTTP interface. -/
def path : pathSig ⟶ sig := (⟨fun r => r.target.pathWithQuery, id⟩ : Hom pathSig sig)

/-- The final response of an exchange. -/
def final : sig ⟶ exchSig := (⟨id, Prod.snd⟩ : Hom sig exchSig)

/-- **An origin server as a machine** of the HTTP interface. -/
def machine {σ : Type} (O : Origin σ) : Machine sig σ := O

/-- **The trace sentence of an origin** from a resource state: linearizable with respect to it. -/
def originSen {σ : Type} (O : Origin σ) (s₀ : σ) : Sen sig := Sen.lin ((machine O).Hist s₀)

/-- **The atomic sentence of a web**: every response is the web's answer to its request
(`HEAD` without content). -/
def webSen (W : Origin.Web) : Sen sig := Sen.atomic fun (r : Request) (s : Response) =>
  s = Origin.webAnswer W r

/-- Every response has status `c` (a sentence of the status view). -/
def allStatus (c : Status) : Sen statusSig := Sen.atomic fun _ (s : Status) => s = c

end Silmaril.Servers.Http
