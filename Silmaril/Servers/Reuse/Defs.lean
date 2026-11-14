module

public import Silmaril.Net.Http.Exchange.Defs

@[expose] public section

/-!
# Instance reuse: how a host runs a stateful handler

A server whose state lives in its instance (a Wasm component instance, a CGI process, a
long-running Linux process) is an origin `O : Origin σ` (`Silmaril.Net.Http.Origin`): in state
`s`, the request `r` may be answered `resp` with next state `s'`. What a client sees depends on
how the host maps requests to instances:

* `Seq O s`: **one instance, reused sequentially**: each request is handled by the same
  instance, from the state the previous one left (a long-running process; `wasmtime serve` with
  reuse; WAGI-style hosts that keep a module instance);
* `Fresh O s₀`: **a fresh instance per request**: every request is handled from the initial
  state `s₀` (CGI, which runs the script once per request, RFC 3875; the default of
  `wasmtime serve` for WASI 0.2 components, of Spin and of Fastly Compute);
* `HostRuns O s₀`: **arbitrary reuse**: the host keeps a pool of instances and hands each
  request to an idle instance of its choice or to a new one. This is what the `wasi:http`
  worlds promise a component: "A host may arbitrarily reuse or not reuse component instance
  when delivering incoming HTTP requests and thus a component must be able to handle 0..N calls
  to `handle`" (`specs/wasi/0.3.2/http/worlds.wit`, world `service`).

The logs (`Log`) are sequential: one exchange at a time, each request/response pair an atomic
event. Concurrent reuse (the 0.3 `service` world lets a host call `handle` again before an
earlier call has returned) is not modelled here.

The theorems (`Servers.Reuse.Thms`) show that `Seq` and `Fresh` are special cases of
`HostRuns`, and that a property every reachable instance state guarantees holds of every
exchange whatever the host does (`hostRuns_of_inv`): the reason the platform docs ask for
stateless handlers. The counter (`counter`) shows the converse failure: a server that counts
its requests in instance state is answered differently under `Fresh` and `Seq`.

A Silmaril addition.
-/

namespace Silmaril.Servers.Reuse

open Silmaril.Net.Http

/-- A sequential log of exchanges, oldest first. -/
abbrev Log : Type := List (Request × Response)

variable {σ : Type}

/-- **One instance, reused**: the runs of `O` from `s`. -/
inductive Seq (O : Origin σ) : σ → Log → Prop where
  | nil (s : σ) : Seq O s []
  | cons {s s' : σ} {r : Request} {resp : Response} {l : Log} :
      O s r resp s' → Seq O s' l → Seq O s ((r, resp) :: l)

/-- **A fresh instance per request**: every exchange is a run of `O` from `s₀`. -/
def Fresh (O : Origin σ) (s₀ : σ) (l : Log) : Prop :=
  ∀ p ∈ l, ∃ s', O s₀ p.1 p.2 s'

/-- **A pool of instances**, as their states. The host hands the next request to an idle
instance of the pool (`reuse`) or to a new instance started in `s₀` (`new`). -/
inductive Pooled (O : Origin σ) (s₀ : σ) : List σ → Log → Prop where
  | nil (pool : List σ) : Pooled O s₀ pool []
  | reuse {a b : List σ} {s s' : σ} {r : Request} {resp : Response} {l : Log} :
      O s r resp s' → Pooled O s₀ (a ++ s' :: b) l → Pooled O s₀ (a ++ s :: b) ((r, resp) :: l)
  | new {pool : List σ} {s' : σ} {r : Request} {resp : Response} {l : Log} :
      O s₀ r resp s' → Pooled O s₀ (s' :: pool) l → Pooled O s₀ pool ((r, resp) :: l)

/-- **Arbitrary reuse**: the logs of some pooling policy, starting with no instance. -/
def HostRuns (O : Origin σ) (s₀ : σ) (l : Log) : Prop := Pooled O s₀ [] l

/-- The response a counter gives: status 200, its count as one octet. -/
def countResponse (n : Nat) : Response := Response.simple Status.ok [n.toUInt8]

/-- **A counter**: answers every request with the number of requests its instance handled
before. -/
def counter : Origin Nat := Origin.ofFun fun n _ => (countResponse n, n + 1)

end Silmaril.Servers.Reuse
