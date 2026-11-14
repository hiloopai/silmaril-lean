module

public import Silmaril.Servers.Core.Defs

/-!
# Connection events: traces with connections opened and closed

The core's traces (`Silmaril.Servers.Core`) carry the connection of every request
(`ReqId.conn`) but not the connections themselves. This module adds them:

* `CEvent A`: a connection is opened (`connect c`), closed (`close c`, by either side), or a
  core event happens on it (`ev e`); `CTrace A` is a list of them, and `CTrace.erase` forgets
  the connection events;
* **`CSen.WF`**: a trace is well formed when it is a run of the monitor `CMon`: each connection
  is opened once, then may be closed once (`Phase`: `fresh`, `live`, `closed`); requests are
  received and answered only on live connections, as the core's well-formedness monitor
  (`WMon`) allows. A request still open when its connection closes is never answered;
* `CSen.lift φ`: a core sentence, about the trace without its connection events;
  `CSen.graceful`: a connection is closed only once every request received on it has been
  answered; `CSen.allClosed`: every connection opened is closed;
* `CModel A`, `CModel.Sat`, `CModel.Refines`: models of connection traces;
  **`Model.withConns M`**: a core model with connections: the well-formed connection traces
  whose core trace is a trace of `M`; `Model.graceful M`: those that close gracefully.

The theorems (`Silmaril.Servers.Sessions.Thms`): forgetting the connection events of a
well-formed trace gives a well-formed core trace, and every well-formed core trace is so
obtained, so core sentences and core refinement mean the same with and without connection
events; and a graceful trace whose connections are all closed answers every request.

The socket events of `Silmaril.Servers.Platform` (`SockEv.accept`, `SockEv.close`) are the
same events at the level of octets.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Servers

variable {A : Sig}

/-- **An event with connections**: a connection is opened or closed, or a core event happens. -/
inductive CEvent (A : Sig) : Type where
  /-- The connection `c` is opened. -/
  | connect (c : Nat)
  /-- The connection `c` is closed (by either side). -/
  | close (c : Nat)
  /-- A core event. -/
  | ev (e : Event A)

/-- **A trace with connections.** -/
abbrev CTrace (A : Sig) : Type := List (CEvent A)

/-- The core trace: the core events, without the connection events. -/
def CTrace.erase (t : CTrace A) : Trace A :=
  t.filterMap fun
    | .ev e => some e
    | _ => none

/-- The phase of a connection. -/
inductive Phase where
  | fresh
  | live
  | closed
  deriving DecidableEq

/-- **The monitor of connection traces**: the phase of every connection, and the core's
well-formedness monitor. -/
structure CMon (A : Sig) : Type where
  phase : Nat → Phase
  w : WMon A

/-- The initial monitor: no connection opened, nothing received. -/
def CMon.init (A : Sig) : CMon A := ⟨fun _ => .fresh, WMon.init A⟩

/-- A step of the monitor: a fresh connection opens; a live connection closes; a core event
happens on a live connection, as the core monitor allows. -/
inductive CMon.Step {A : Sig} : CMon A → CEvent A → CMon A → Prop where
  | connect {m : CMon A} {c : Nat} : m.phase c = .fresh →
      CMon.Step m (.connect c) ⟨Function.update m.phase c .live, m.w⟩
  | close {m : CMon A} {c : Nat} : m.phase c = .live →
      CMon.Step m (.close c) ⟨Function.update m.phase c .closed, m.w⟩
  | ev {m : CMon A} {e : Event A} {w' : WMon A} : m.phase e.id.conn = .live →
      WMon.Step m.w e w' → CMon.Step m (.ev e) ⟨m.phase, w'⟩

/-- **A sentence about traces with connections.** -/
abbrev CSen (A : Sig) : Type := CTrace A → Prop

namespace CSen

/-- **Well formed**: a run of the monitor. -/
def WF : CSen A := fun t => ∃ m, Steps CMon.Step (CMon.init A) t m

/-- A core sentence, of the core trace. -/
def lift (φ : Sen A) : CSen A := fun t => φ t.erase

/-- **Graceful close**: when a connection closes, every request received on it has been
answered. -/
def graceful : CSen A :=
  fun t => ∀ pre post c, t = pre ++ .close c :: post →
    ∀ i r, Event.recv i r ∈ CTrace.erase pre → i.conn = c → ∃ s, Event.send i s ∈ CTrace.erase pre

/-- Every connection opened is closed. -/
def allClosed : CSen A := fun t => ∀ c, CEvent.connect c ∈ t → CEvent.close c ∈ t

end CSen

/-- **A model of traces with connections.** -/
structure CModel (A : Sig) : Type where
  Tr : CTrace A → Prop

/-- Satisfaction: every trace satisfies the sentence. -/
def CModel.Sat (M : CModel A) (φ : CSen A) : Prop := ∀ t, M.Tr t → φ t

/-- Refinement: trace inclusion. -/
def CModel.Refines (M N : CModel A) : Prop := ∀ t, M.Tr t → N.Tr t

/-- **A core model with connections**: the well-formed connection traces whose core trace is a
trace of `M`. -/
def Model.withConns (M : Model A) : CModel A := ⟨fun t => CSen.WF t ∧ M.Tr t.erase⟩

/-- The traces of `M.withConns` that close gracefully. -/
def Model.graceful (M : Model A) : CModel A :=
  ⟨fun t => CSen.WF t ∧ CSen.graceful t ∧ M.Tr t.erase⟩

end Silmaril.Servers
