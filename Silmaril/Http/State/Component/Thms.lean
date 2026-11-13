module

public import Silmaril.Http.State.Component.Defs
public import Silmaril.Http.State.Thms
import Silmaril.Proofs.Http.State.Component

@[expose] public section

/-!
# State model (a), component state: theorems (header)

PROVED (standard axioms), namespace `Silmaril.Http.State.Component`. Proofs in
`Silmaril.Proofs.Http.State.Component`.

* `counter_linearizable`, `kv_linearizable`: the component-state counter and key-value
  servers are linearizable with respect to their handlers (instances of
  `closed_linearizable`);
* **`counter_distinct`**: when `f` is injective, two different requests to a counter server
  are never answered the same, however they overlap and in whatever order the host runs them;
* `httpCounter_distinct`: the same for the HTTP counter with an injective rendering;
* **`perRequest_counter`**, **`perRequest_kv_get`**: with a fresh instance per request (as
  `wasmtime serve` runs a component) the counter always answers `f 0` and the store answers
  every `GET` from its initial contents: component state does not persist.
-/

namespace Silmaril.Http.State.Component

open Silmaril.Net.Http

variable {Req Resp : Type}

theorem counter_linearizable (f : Nat → Resp) :
    (counterServer (Req := Req) f).Sat (Linearizable (counterBy f) 0) :=
  closed_linearizable _ _

theorem kv_linearizable (S₀ : Store) : (kvServer S₀).Sat (Linearizable kv S₀) :=
  closed_linearizable _ _

theorem counter_distinct {f : Nat → Resp} (hf : Function.Injective f) {H : Hist Req Resp}
    (hH : (counterServer f).Hists H) {i j : Nat} {a b : Resp} (hi : Ev.ret i a ∈ H)
    (hj : Ev.ret j b ∈ H) (hij : i ≠ j) : a ≠ b :=
  Proofs.Http.State.Component.counter_distinct hf hH hi hj hij

theorem httpCounter_distinct {render : Nat → List UInt8} (hf : Function.Injective render)
    {H : Hist Request Response} (hH : (Server.closed (httpCounter render) 0).Hists H)
    {i j : Nat} {a b : Response} (hi : Ev.ret i a ∈ H) (hj : Ev.ret j b ∈ H) (hij : i ≠ j) :
    a ≠ b :=
  counter_distinct (f := fun n => Response.simple Status.ok (render n))
    (fun _ _ e => hf (congrArg Message.content e)) hH hi hj hij

theorem perRequest_counter {f : Nat → Resp} {H : Hist Req Resp}
    (hH : (Server.perRequest (counterBy f) 0).Hists H) {i : Nat} {r : Req} {s : Resp}
    (hc : Ev.call i r ∈ H) (hr : Ev.ret i s ∈ H) : s = f 0 :=
  Proofs.Http.State.Component.perRequest_counter hH hc hr

theorem perRequest_kv_get {S₀ : Store} {H : Hist Request Response}
    (hH : (Server.perRequest kv S₀).Hists H) {i : Nat} {r : Request} {s : Response}
    (hc : Ev.call i r ∈ H) (hr : Ev.ret i s ∈ H) (hm : r.method = .get) :
    s = S₀.get r.target :=
  Proofs.Http.State.Component.perRequest_kv_get hH hc hr hm

end Silmaril.Http.State.Component
