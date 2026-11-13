module

public import Silmaril.Http.State.Defs
public import Silmaril.Net.Http.Exchange.Defs

@[expose] public section

/-!
# State model (a): state inside the component

See `docs/projects/http-servers.md` (section "State models"). The server's state lives in
the component instance (its linear memory and globals), and nobody else changes it: the
server is `Server.closed`, and its histories are linearizable with respect to its own
handler (`closed_linearizable`). Two examples:

* **a counter** (`counterBy f`): the `n`-th request (from `0`) is answered `f n`. `counter`
  answers the count itself; `httpCounter render` answers `200` with content `render n` (for
  instance the decimal digits, `decimal`);
* **a key-value store** (`kv`): `Silmaril.Net.Http.storeStep` (a representation per target,
  with `GET`, `HEAD`, `PUT`, `DELETE`, `OPTIONS` as RFC 9110 §9.3 gives them) read as an
  atomic handler, `kvServer S₀` the server whose component starts with the store `S₀`.

Component state survives between requests only when the host keeps the instance. `wasmtime
serve` (and Spin) instantiate per request: that host is `Server.perRequest`, whose state is
reset for every request, so a counter there answers `f 0` every time and a store answers
every `GET` from `S₀` (`perRequest_counter`, `perRequest_kv_get`).

A Silmaril addition.
-/

namespace Silmaril.Http.State.Component

open Silmaril.Net.Http

/-- **A counter**: in state `n`, every request is answered `f n`, and the state becomes
`n + 1`. -/
def counterBy {Req Resp : Type} (f : Nat → Resp) : Atomic Nat Req Resp :=
  fun n _ k n' => k = f n ∧ n' = n + 1

/-- The counter that answers the count. -/
abbrev counter {Req : Type} : Atomic Nat Req Nat := counterBy id

/-- The decimal digits of `n`, as ASCII octets. -/
def decimal (n : Nat) : List UInt8 := Method.ascii (toString n)

/-- **An HTTP counter**: `200` with content `render n`. -/
def httpCounter (render : Nat → List UInt8) : Atomic Nat Request Response :=
  counterBy fun n => Response.simple Status.ok (render n)

/-- The counter server with component state, from `0`. -/
def counterServer {Req Resp : Type} (f : Nat → Resp) : Server Req Resp :=
  Server.closed (counterBy f) 0

/-- **The key-value store** as an atomic handler: `storeStep`. -/
def kv : Atomic Store Request Response := Atomic.ofFun storeStep

/-- The key-value server with component state, from the store `S₀`. -/
def kvServer (S₀ : Store) : Server Request Response := Server.closed kv S₀

end Silmaril.Http.State.Component
