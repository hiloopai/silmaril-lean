module

public import Silmaril.Servers.Core.Defs

/-!
# Connections: per-connection readings and sequential consistency

See `docs/projects/http-servers.md` (section "Server core"). The core's traces carry the
connection of every request (`ReqId.conn`). This module adds the readings that look at one
connection at a time:

* `Sen.perConn φ`: the events of every connection, on their own, satisfy `φ`;
* `Sen.connSeq`: every connection is used sequentially (an HTTP/1.1 client that does not
  pipeline: it waits for each response before sending the next request), while requests on
  different connections may overlap;
* `Model.perConn N`: **an instance per connection**: the well-formed traces whose events on
  each connection are a trace of `N` (a process forked per connection, a keep-alive connection
  bound to one Wasm instance). The instances share no state, so nothing relates the
  connections.

`Sen.sc S` (the core) is Lamport's sequential consistency: some reordering that keeps the
events of each connection in order is linearizable. The theorems (`Thms`) give its simplest
sufficient condition (a sequential merge of the connections allowed by `S`), show that it is
strictly weaker than linearizability (`counterTrace`: sequentially consistent for a counter,
not linearizable), and relate the per-connection readings to the core ones.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Servers

variable {A : Sig}

/-- **Per connection**: the events of every connection satisfy `φ`. -/
def Sen.perConn (φ : Sen A) : Sen A := fun t => ∀ c, φ (t.onConn c)

/-- **Sequential use of each connection**: on every connection each request is answered before
the next arrives. -/
def Sen.connSeq : Sen A := Sen.perConn Sen.Sequential

/-- **An instance per connection**: the well-formed traces whose events on each connection
are a trace of `N`. -/
def Model.perConn (N : Model A) : Model A := ⟨fun t => Sen.WF t ∧ ∀ c, N.Tr (t.onConn c)⟩

/-! ## A counter, to separate sequential consistency from linearizability -/

/-- Requests without content, responses numbers. -/
abbrev counterSig : Sig := ⟨Unit, Nat⟩

/-- **A counter**: the `n`-th request (from `0`) is answered `n`. -/
def counterM : Machine counterSig Nat := fun n _ k n' => k = n ∧ n' = n + 1

/-- Request `0` on connection `0` is answered `1`, and only then request `0` of connection `1`
arrives and is answered `0`. -/
def counterTrace : Trace counterSig :=
  Trace.seq [(⟨0, 0⟩, (), (1 : Nat)), (⟨1, 0⟩, (), (0 : Nat))]

end Silmaril.Servers
