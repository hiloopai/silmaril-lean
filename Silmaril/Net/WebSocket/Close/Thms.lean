module

public import Silmaril.Net.WebSocket.Close.Defs
public import Silmaril.Automata.Shapes.Thms

@[expose] public section

/-!
# The WebSocket connection lifecycle: theorems

PROVED by the verified decision procedures of `Silmaril.Automata` (`decide` over the finite
machine; standard axioms):

* `conn_all_reachable`: every state is reachable from `connecting`;
* `conn_closed_final`: `closed` is final;
* `no_data_after_close_sent`: once this endpoint has sent its Close, no reachable state lets
  it send a data frame (§5.5.1);
* `clean_close_needs_both`: without a transport close, an open connection reaches `closed`
  only through both a sent and a received Close frame (§7.1.2–§7.1.4: the closing handshake
  is two Close frames);
* `peer_data_after_close_fails`: after the peer's Close, a data frame from the peer is a
  protocol error.
-/

namespace Silmaril.Net.WebSocket

open Silmaril.Automata.Shapes

theorem connMachine_step_iff (s s' : ConnState) (e : ConnEvent) :
    connMachine.step s e = some s' ↔ connStep s e = .ok s' := by
  simp only [connMachine, Silmaril.Automata.DMachine.ofExcept]
  cases connStep s e <;> simp [Except.toOption]

theorem conn_all_reachable : ∀ s, Reach connMachine (fun _ => true) .connecting s := by decide

theorem conn_closed_final : ∀ s, Reach connMachine (fun _ => true) .closed s → s = .closed := by
  decide

theorem no_data_after_close_sent :
    ∀ s, Reach connMachine (fun _ => true) .closeSent s →
      connMachine.step s (.frame .send .data) = none := by
  decide

/-- Without a transport close, `closed` is unreachable from `open` if this endpoint never sends a
Close, and unreachable if it never receives one. -/
theorem clean_close_needs_both :
    ¬ Reach connMachine (fun e => e.clean && e != .frame .send .close) .open .closed ∧
      ¬ Reach connMachine (fun e => e.clean && e != .frame .recv .close) .open .closed := by
  decide

theorem peer_data_after_close_fails :
    connStep .closeReceived (.frame .recv .data) = .error .protocol := rfl

end Silmaril.Net.WebSocket
