module

public import Silmaril.Net.Http2.Stream.Defs
public import Silmaril.Automata.Shapes.Thms
public import Silmaril.Automata.Graph.Thms
import Silmaril.Proofs.Net.Http2.Stream

@[expose] public section

/-!
# HTTP/2 stream states: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Http2/Stream.lean`), RFC 9113 §5.1:

* `step_send_dual`: **the two endpoints agree.** Whatever one endpoint may legally send in a
  state, the peer, in the dual state (local and remote exchanged), accepts without error and
  moves to the dual of the sender's next state. So Figure 2 read by the sender and by the
  receiver describe the same stream;
* `step_recv_dual`: conversely, every frame accepted outside *closed* could have been sent by
  the peer in the dual state;
* `step_closed`: *closed* is terminal; `step_rank`, `run_rank`: streams only progress towards
  closed (no transition goes back, e.g. from half-closed to open);
* `step_rst`: RST_STREAM closes every non-idle stream (§6.4);
* `step_recv_data`, `step_send_data`: DATA is accepted only on open or half-closed (local)
  streams (or ignored when closed), and sent only on open or half-closed (remote) streams;
* **as a finite machine** (`Silmaril.Automata`, decided by the verified procedures of
  `Silmaril.Automata.Decide`): every state is reachable from idle (`all_reachable`), closed
  reaches only closed (`closed_final`), and without END_STREAM or RST_STREAM a stream never
  closes (`quiet_never_closes`); `machine_step_iff` relates the machine to `step`;
* `idom_table`: the immediate dominators of the stream graph from idle (all idle);
* `openRemote_ok`: an accepted new peer stream identifier has the peer's parity and exceeds
  every earlier one (§5.1.1).
-/

namespace Silmaril.Net.Http2

theorem step_closed {e : Event} {s : StreamState} (h : step .closed e = .ok s) : s = .closed :=
  Silmaril.Proofs.Net.Http2.step_closed h

theorem step_send_dual {s s' : StreamState} {g : Signal} (h : step s ⟨.send, g⟩ = .ok s') :
    step s.dual ⟨.recv, g⟩ = .ok s'.dual :=
  Silmaril.Proofs.Net.Http2.step_send_dual h

theorem step_recv_dual {s s' : StreamState} {g : Signal} (h : step s ⟨.recv, g⟩ = .ok s') :
    step s.dual ⟨.send, g⟩ = .ok s'.dual ∨ s = .closed :=
  Silmaril.Proofs.Net.Http2.step_recv_dual h

theorem step_rank {s s' : StreamState} {e : Event} (h : step s e = .ok s') : s.rank ≤ s'.rank :=
  Silmaril.Proofs.Net.Http2.step_rank h

theorem run_rank {s s' : StreamState} {es : List Event} (h : run s es = .ok s') :
    s.rank ≤ s'.rank :=
  Silmaril.Proofs.Net.Http2.run_rank h

theorem step_rst {s : StreamState} {d : Dir} (hi : s ≠ .idle) (hc : d = .send → s ≠ .closed) :
    step s ⟨d, .rstStream⟩ = .ok .closed :=
  Silmaril.Proofs.Net.Http2.step_rst hi hc

theorem step_recv_data {s s' : StreamState} {es : Bool} (h : step s ⟨.recv, .data es⟩ = .ok s') :
    s = .open ∨ s = .halfClosedLocal ∨ s = .closed :=
  Silmaril.Proofs.Net.Http2.step_recv_data h

theorem step_send_data {s s' : StreamState} {es : Bool} (h : step s ⟨.send, .data es⟩ = .ok s') :
    s = .open ∨ s = .halfClosedRemote :=
  Silmaril.Proofs.Net.Http2.step_send_data h

theorem openRemote_ok {peerIsClient : Bool} {last id id' : Nat}
    (h : openRemote peerIsClient last id = .ok id') :
    id' = id ∧ id ≠ 0 ∧ clientInitiated id = peerIsClient ∧ last < id := by
  unfold openRemote at h; split at h <;> simp_all

/-! ## The stream machine -/

open Silmaril.Automata.Shapes in
theorem machine_step_iff (s s' : StreamState) (e : Event) :
    machine.step s e = some s' ↔ step s e = .ok s' := by
  simp only [machine, Silmaril.Automata.DMachine.ofExcept]
  cases step s e <;> simp [Except.toOption]

open Silmaril.Automata.Shapes in
/-- Every stream state is reachable from idle. -/
theorem all_reachable : ∀ s, Reach machine (fun _ => true) .idle s := by decide

open Silmaril.Automata.Shapes in
/-- Closed is final: nothing but closed is reachable from it. -/
theorem closed_final : ∀ s, Reach machine (fun _ => true) .closed s → s = .closed := by decide

/-- Events that neither end the stream nor reset it. -/
def quiet (e : Event) : Bool :=
  match e.signal with
  | .headers es | .data es => !es
  | .rstStream => false
  | _ => true

open Silmaril.Automata.Shapes in
/-- Without END_STREAM or RST_STREAM, a stream never closes (§5.1). -/
theorem quiet_never_closes : ¬ Reach machine quiet .idle .closed := by decide

/-- **No state but idle dominates another**: in the stream graph from idle (labels forgotten), the
immediate dominator of every other state is idle (node `0`). So the exact dominator tree is the
star from idle (`Graph.exact_unique`): every state can be reached avoiding any other given state. -/
theorem idom_table :
    Silmaril.Automata.Graph.idomTable (machine.toDigraph .idle) =
      [none, some 0, some 0, some 0, some 0, some 0, some 0] := by decide +kernel

/-! A request/response exchange, from the client's side (§8.1). -/

/-- The client sends HEADERS and DATA with END_STREAM, then receives the response headers and
its final DATA: the stream is closed. -/
example : run .idle [⟨.send, .headers false⟩, ⟨.send, .data true⟩, ⟨.recv, .headers false⟩,
    ⟨.recv, .data true⟩] = .ok .closed := rfl

/-- After the peer ends its side, more DATA from it is a stream error (§5.1). -/
example : run .idle [⟨.recv, .headers true⟩, ⟨.recv, .data false⟩] =
    .error (.stream .streamClosed) := rfl

/-- DATA on an idle stream is a connection error (§5.1). -/
example : step .idle ⟨.recv, .data false⟩ = .error (.connection .protocolError) := rfl

end Silmaril.Net.Http2
