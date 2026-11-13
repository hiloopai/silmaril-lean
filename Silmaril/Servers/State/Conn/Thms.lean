module

public import Silmaril.Servers.State.Conn.Defs
public import Silmaril.Servers.State.Traces.Thms
public import Silmaril.Servers.Conn.Thms
import Silmaril.Proofs.Servers.State.Conn

@[expose] public section

/-!
# State histories read per connection: theorems (header)

PROVED (standard axioms), namespace `Silmaril.Servers.State`. Proofs in
`Silmaril.Proofs.Servers.State.Conn`.

* `onConn_toTrace`, `perConn_toTrace`: connection `i` of the trace of `H` is the trace of the
  events of request `i`; a per-connection sentence holds of `toTrace H` when it holds of
  every request's events;
* **`sc_serializable`**: with one connection per request, sequential consistency of the trace
  (`Sen.sc`) gives serializability of the history (`Serializable`): sequential consistency
  may reorder the connections freely, and here every request is its own connection;
* `linearizable_sc`: a linearizable history with a well-formed trace has a sequentially
  consistent trace; with `sc_serializable`, `sc` sits between the two State notions;
* **`perRequest_perConn`**: a fresh instance per request (`Server.perRequest`) refines an
  instance per connection of the component-state server (`Model.perConn`); **`perConn_perRequest`**:
  conversely, on traces with one request per connection, an instance per connection is a
  fresh instance per request (`perRequest_model_iff`).

Open: `Task.serializable_sc` (the converse of `sc_serializable`).
-/

namespace Silmaril.Servers.State

variable {σ Req Resp : Type}

theorem onConn_toTrace (c : Nat) (H : Hist Req Resp) :
    (toTrace H).onConn c = toTrace (H.onId c) :=
  Proofs.Servers.State.Conn.onConn_toTrace c H

theorem perConn_toTrace {φ : Servers.Sen (sig Req Resp)} {H : Hist Req Resp} :
    Servers.Sen.perConn φ (toTrace H) ↔ ∀ c, φ (toTrace (H.onId c)) := by
  simp only [Servers.Sen.perConn, onConn_toTrace]

/-- **Sequential consistency, one connection per request, is serializability.** -/
theorem sc_serializable {A : Atomic σ Req Resp} {s₀ : σ} {H : Hist Req Resp}
    (h : Servers.Sen.sc (A.machine.Hist s₀) (toTrace H)) : Serializable A s₀ H :=
  Proofs.Servers.State.Conn.sc_serializable h

theorem linearizable_sc {A : Atomic σ Req Resp} {s₀ : σ} {H : Hist Req Resp}
    (hw : Servers.Sen.WF (toTrace H)) (h : Linearizable A s₀ H) :
    Servers.Sen.sc (A.machine.Hist s₀) (toTrace H) :=
  Servers.Sen.sc_of_lin ((linearizable_iff_lin hw).1 h)

/-- **A fresh instance per request is an instance per connection.** -/
theorem perRequest_perConn (A : Atomic σ Req Resp) (s₀ : σ) :
    (Server.perRequest A s₀).model.Refines (Model.perConn (Server.closed A s₀).model) :=
  Proofs.Servers.State.Conn.perRequest_perConn A s₀

theorem perConn_perRequest {A : Atomic σ Req Resp} {s₀ : σ} {t : Trace (sig Req Resp)}
    (h : (Model.perConn (Server.closed A s₀).model).Tr t) (hone : OnePerConn t) :
    (Server.perRequest A s₀).model.Tr t :=
  Proofs.Servers.State.Conn.perConn_perRequest h hone

/-- **On one request per connection, an instance per connection is a fresh instance per
request.** -/
theorem perRequest_model_iff (A : Atomic σ Req Resp) (s₀ : σ) (t : Trace (sig Req Resp)) :
    (Server.perRequest A s₀).model.Tr t ↔
      (Model.perConn (Server.closed A s₀).model).Tr t ∧ OnePerConn t :=
  ⟨fun h => ⟨perRequest_perConn A s₀ t h,
      let ⟨H, _, he⟩ := h; he ▸ toTrace_onePerConn H⟩,
    fun ⟨h, hone⟩ => perConn_perRequest h hone⟩

end Silmaril.Servers.State
