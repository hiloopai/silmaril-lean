module

public import Silmaril.Servers.State.Traces.Defs
public import Silmaril.Servers.Conn.Defs

@[expose] public section

/-!
# State histories read per connection

See `docs/projects/http-servers.md` (sections "Server core" and "State models"). The state
models' histories are core traces with one connection per request (`toTrace`,
`Silmaril.Servers.State.Traces`). This module reads the core's per-connection notions
(`Silmaril.Servers.Conn`: `Sen.perConn`, `Model.perConn`, `Sen.sc`) on those traces:

* `Ev.id`, `Hist.onId i H`: the events of the request `i` in `H` (the events of connection
  `i` of `toTrace H`);
* `ofEvent`: a core event read back as a history event (request `⟨c, n⟩` as request `c`);
* `Task.serializable_sc`: **open**, the converse of `sc_serializable` (`Thms`): a serializable
  history whose trace is well formed has a sequentially consistent trace. A reordering that
  puts every request of the sequential run next to its response, and the requests that did
  not run at the end, should witness it; not proved.

A Silmaril addition.
-/

namespace Silmaril.Servers.State

variable {σ Req Resp : Type}

/-- The request identity of an event. -/
def Ev.id : Ev Req Resp → Nat
  | .call i _ => i
  | .ret i _ => i

/-- **The events of the request `i`** in a history. -/
def Hist.onId (i : Nat) (H : Hist Req Resp) : Hist Req Resp := H.filter (·.id == i)

/-- A core event as a history event: the request `⟨c, n⟩` is the request `c`. -/
def ofEvent : Event (sig Req Resp) → Ev Req Resp
  | .recv i r => .call i.conn r
  | .send i s => .ret i.conn s

/-- **Open**: the converse of `sc_serializable`. -/
def Task.serializable_sc : Prop :=
  ∀ (σ Req Resp : Type) (A : Atomic σ Req Resp) (s₀ : σ) (H : Hist Req Resp),
    Sen.WF (toTrace H) → Serializable A s₀ H → Sen.sc (A.machine.Hist s₀) (toTrace H)

end Silmaril.Servers.State
