module

public import Silmaril.Net.Quic.Flow.Defs
import Silmaril.Proofs.Net.Quic.Flow

@[expose] public section

/-!
# QUIC flow control: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Quic/Flow.lean`):

* `Credit.onMax_mono`, `Credit.onMax_ignored`: MAX_DATA / MAX_STREAM_DATA only ever raise a
  limit, and "frames that do not increase flow control limits" are ignored (§4.1);
* `SendFlow.send_ok`: a sender never exceeds either credit ("Senders MUST NOT send data in
  excess of either limit"); `SendFlow.send_none`: sending is refused exactly when one limit
  would be exceeded;
* `RecvFlow.onData_error`: FLOW_CONTROL_ERROR exactly when the stream limit or the connection
  limit is exceeded; `RecvFlow.onData_ok`, `raiseMaxData_ok`, `raiseStreamMax_ok`: the
  receiver's accounting stays within what it advertised;
* `sync_send`: **a sender that respects its credit never causes FLOW_CONTROL_ERROR**: when the
  sender's view is in `Sync` with the receiver and `send` succeeds, the receiver accepts the
  data and the views stay in `Sync`; `sync_onMaxData`, `sync_onMaxStreamData`,
  `sync_raiseMaxData`, `sync_raiseStreamMax`: advertising limits and receiving them (possibly
  late or reordered, so possibly stale) keeps the views in `Sync`.

CHECKED: a blocked sender and an over-limit receiver.
-/

namespace Silmaril.Net.Quic

namespace Credit

theorem onMax_mono (c : Credit) (m : Nat) :
    c.limit ≤ (c.onMax m).limit ∧ m ≤ (c.onMax m).limit := by
  simp only [onMax]; omega

theorem onMax_ignored {c : Credit} {m : Nat} (h : m ≤ c.limit) : c.onMax m = c := by
  simp only [onMax, Nat.max_eq_left h]

theorem consume_ok {c c' : Credit} {n : Nat} (h : c.consume n = some c') :
    c'.Ok ∧ c'.used = c.used + n := by
  obtain ⟨h1, rfl⟩ := Silmaril.Proofs.Net.Quic.Flow.consume_spec.1 h
  exact ⟨h1, rfl⟩

end Credit

namespace SendFlow

theorem send_ok {f f' : SendFlow} {id n : Nat} (hf : f.Ok) (h : f.send id n = some f') :
    f'.Ok :=
  Silmaril.Proofs.Net.Quic.Flow.send_ok hf h

theorem send_none {f : SendFlow} {id n : Nat} :
    f.send id n = none ↔
      f.conn.limit < f.conn.used + n ∨ (f.streams id).limit < (f.streams id).used + n :=
  Silmaril.Proofs.Net.Quic.Flow.send_none

theorem send_spec {f f' : SendFlow} {id n : Nat} (h : f.send id n = some f') :
    f.conn.used + n ≤ f.conn.limit ∧ (f.streams id).used + n ≤ (f.streams id).limit ∧
      f'.conn = { f.conn with used := f.conn.used + n } ∧
      f'.streams = update f.streams id { f.streams id with used := (f.streams id).used + n } :=
  Silmaril.Proofs.Net.Quic.Flow.send_spec h

end SendFlow

namespace RecvFlow

theorem onData_error {f : RecvFlow} {id e : Nat} :
    f.onData id e = .error .flowControlError ↔
      f.streamMax id < e ∨ f.maxData < f.received + (e - f.highest id) :=
  Silmaril.Proofs.Net.Quic.Flow.onData_error

theorem onData_ok {f f' : RecvFlow} {id e : Nat} (hf : f.Ok) (h : f.onData id e = .ok f') :
    f'.Ok :=
  Silmaril.Proofs.Net.Quic.Flow.onData_ok hf h

theorem raiseMaxData_ok {f : RecvFlow} (hf : f.Ok) (m : Nat) : (f.raiseMaxData m).Ok :=
  Silmaril.Proofs.Net.Quic.Flow.raiseMaxData_ok hf m

theorem raiseStreamMax_ok {f : RecvFlow} (hf : f.Ok) (id m : Nat) :
    (f.raiseStreamMax id m).Ok :=
  Silmaril.Proofs.Net.Quic.Flow.raiseStreamMax_ok hf id m

end RecvFlow

theorem sync_send {snd snd' : SendFlow} {rcv : RecvFlow} {id n : Nat} (hs : Sync snd rcv)
    (h : snd.send id n = some snd') :
    ∃ rcv', rcv.onData id ((snd.streams id).used + n) = .ok rcv' ∧ Sync snd' rcv' :=
  Silmaril.Proofs.Net.Quic.Flow.sync_send hs h

theorem sync_onMaxData {snd : SendFlow} {rcv : RecvFlow} {m : Nat} (hs : Sync snd rcv)
    (hm : m ≤ rcv.maxData) : Sync (snd.onMaxData m) rcv :=
  Silmaril.Proofs.Net.Quic.Flow.sync_onMaxData hs hm

theorem sync_onMaxStreamData {snd : SendFlow} {rcv : RecvFlow} {id m : Nat} (hs : Sync snd rcv)
    (hm : m ≤ rcv.streamMax id) : Sync (snd.onMaxStreamData id m) rcv :=
  Silmaril.Proofs.Net.Quic.Flow.sync_onMaxStreamData hs hm

theorem sync_raiseMaxData {snd : SendFlow} {rcv : RecvFlow} (hs : Sync snd rcv) (m : Nat) :
    Sync snd (rcv.raiseMaxData m) :=
  Silmaril.Proofs.Net.Quic.Flow.sync_raiseMaxData hs m

theorem sync_raiseStreamMax {snd : SendFlow} {rcv : RecvFlow} (hs : Sync snd rcv) (id m : Nat) :
    Sync snd (rcv.raiseStreamMax id m) :=
  Silmaril.Proofs.Net.Quic.Flow.sync_raiseStreamMax hs id m

/-! ## Examples -/

/-- With a stream limit of 10, sending 6 then 5 bytes is refused (the sender is blocked at 6;
4 more fit). -/
example : (do
    let f ← SendFlow.send ⟨⟨100, 0⟩, fun _ => ⟨10, 0⟩⟩ 0 6
    pure ((f.send 0 5).isNone, (f.streams 0).available, (f.send 0 4).isSome)) =
    some (true, 4, true) := by decide

/-- A receiver that advertised 10 bytes on stream 0 rejects data reaching offset 11. -/
example : (match RecvFlow.onData { maxData := 100, streamMax := fun _ => 10 } 0 11 with
    | .error e => e == .flowControlError | .ok _ => false) = true := by decide

/-- A retransmission below the highest offset consumes no new connection credit. -/
example : (match (RecvFlow.onData { maxData := 8, streamMax := fun _ => 10 } 0 8).bind
      (·.onData 0 5) with
    | .ok f => f.received == 8 | .error _ => false) = true := by decide

end Silmaril.Net.Quic
