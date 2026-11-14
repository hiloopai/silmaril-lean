module

public import Silmaril.Servers.Core.Defs
public import Silmaril.Servers.Exchange.Defs

@[expose] public section

/-!
# A fresh instance per request

The one model of a host that handles every request with a fresh instance of the server (CGI,
RFC 3875; `wasmtime serve` for a `wasi:http` 0.2 component; Spin; Fastly Compute). The server
is a core machine `M` with initial state `q₀` (`Silmaril.Servers.Core`); its state does not
survive a request.

* `Machine.fresh M q₀`: the stateless machine answering every request as `M` does from `q₀`;
* **`Machine.perRequest M q₀`**: the core model of the host: the atomic-handler server of
  `M.fresh q₀`. Requests may overlap in any way; every response is an answer of `M` from `q₀`
  to its request.

The earlier per-request readings are instances of it (`Silmaril.Servers.PerRequest.Thms`):
`Exchange.fresh` (the `wasi:http` exchange servers, through `Exchange.machine`),
`State.Server.perRequest` (the state models' host, on traces with one connection per request)
and `Reuse.Fresh` (the sequential logs of instance reuse, as the histories of
`Machine.fresh`).

A Silmaril addition.
-/

namespace Silmaril.Servers

variable {A : Sig} {σ : Type}

/-- **The stateless machine of a fresh instance per request**: every request is answered as
`M` answers it from `q₀`. -/
def Machine.fresh (M : Machine A σ) (q₀ : σ) : Machine A Unit := fun _ r s _ => ∃ q', M q₀ r s q'

/-- **A fresh instance per request**: the atomic-handler server of `M.fresh q₀`. -/
def Machine.perRequest (M : Machine A σ) (q₀ : σ) : Model A := (M.fresh q₀).server ()

/-- The machine of an exchange server: a request may be answered as a one-exchange trace of `M`
allows. -/
def Exchange.machine {I : Exchange.Iface} (M : Exchange.Model I) : Machine I Unit :=
  fun _ r s _ => [(r, s)] ∈ M

end Silmaril.Servers
