module

public import Silmaril.Servers.State.Defs
public import Silmaril.Servers.Core.Defs

@[expose] public section

/-!
# State histories as core traces

The state models (`Silmaril.Servers.State`) were written with their own trace vocabulary:
histories of `Ev.call i r` and `Ev.ret i s` events, atomic handlers, hosts, Herlihy and Wing
linearizability. This module reads that vocabulary in the server core
(`Silmaril.Servers.Core`), so that the core is the one vocabulary:

* `sig Req Resp`: the core interface of a request and a response type;
* `Ev.toEvent`, `toTrace`: a history is a core trace with **one connection per request**: the
  request `i` is the first (and only) request on connection `i` (`ReqId ⟨i, 0⟩`). The state
  histories do not model connections, so this is the reading that adds no order;
* `OnePerConn`: the core traces of that shape (every identity is at position `0`);
* `Atomic σ Req Resp` **is** `Machine (sig Req Resp) σ`, by definition (`Atomic.machine`);
* `Server.model M`: the core model of a state server, the core traces of its histories;
* `Orderly`: the shape of a history whose core trace is well formed, event by event (every
  request identity fresh when it arrives; every response to a request that arrived and is not
  answered yet).

The theorems (`Silmaril.Servers.State.Traces.Thms`): linearizability of a history in the sense
of Herlihy and Wing (`Linearizable`) is the core's linearization-point sentence (`Sen.lin`) of
its trace; the host of a closed server is the core's atomic-handler server, restricted to
traces with one connection per request; an abstraction gives refinement of the core's
atomic-handler server.

A Silmaril addition.
-/

namespace Silmaril.Servers.State

variable {σ Req Resp : Type}

/-- The core interface of a request and a response type. -/
abbrev sig (Req Resp : Type) : Sig := ⟨Req, Resp⟩

/-- **An event of a history as a core event**: the request `i` is the only request on
connection `i`. -/
def Ev.toEvent : Ev Req Resp → Event (sig Req Resp)
  | .call i r => .recv ⟨i, 0⟩ r
  | .ret i s => .send ⟨i, 0⟩ s

/-- **A history as a core trace**, one connection per request. -/
def toTrace (H : Hist Req Resp) : Trace (sig Req Resp) := H.map Ev.toEvent

/-- A core trace with one connection per request: every identity is at position `0`. -/
def OnePerConn {A : Sig} (t : Trace A) : Prop := ∀ e ∈ t, e.id.seq = 0

/-- **An atomic handler is a core machine** (the same definition). -/
abbrev Atomic.machine (A : Atomic σ Req Resp) : Machine (sig Req Resp) σ := A

/-- The core history of a sequential run. -/
def opsHistory (L : List (Op Req Resp)) : History (sig Req Resp) := L.map fun o => (o.req, o.resp)

/-- **The core model of a state server**: the core traces of its histories. -/
def Server.model (M : Server Req Resp) : Model (sig Req Resp) :=
  ⟨fun t => ∃ H, M.Hists H ∧ toTrace H = t⟩

/-- `Orderly P Q`: the events `Q`, after the history `P`, each have a fresh request identity
(`call`) or answer a request that arrived and is not answered yet (`ret`). -/
def Orderly : Hist Req Resp → Hist Req Resp → Prop
  | _, [] => True
  | P, .call i r :: Q => ¬ Called P i ∧ Orderly (P ++ [.call i r]) Q
  | P, .ret i s :: Q => Called P i ∧ ¬ Returned P i ∧ Orderly (P ++ [.ret i s]) Q

end Silmaril.Servers.State
