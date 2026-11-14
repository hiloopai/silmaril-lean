module

public import Silmaril.Net.WebTransport.Flow.Defs
import Silmaril.Proofs.Net.WebTransport.Flow

@[expose] public section

/-!
# WebTransport session flow control: theorems (draft-ietf-webtrans-http3-17 §5)

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/WebTransport/Flow.lean`):

* `onCapsule_mono`: limits only increase at the sender, whatever capsule it accepts (§5.6.2,
  §5.6.4: a non-increasing WT_MAX_STREAMS / WT_MAX_DATA is a `WT_FLOW_CONTROL_ERROR`,
  `onCapsule_maxStreams_stale`, `onCapsule_maxData_stale`); `raiseStreams_mono`,
  `raiseData_mono`: the receiver only raises them;
* `tryOpen_within`, `trySend_within`, `onCapsule_within`: a compliant sender stays within the
  limits its peer granted;
* `onOpen_of_tryOpen`, `onData_of_trySend`: what a compliant sender does is accepted by a
  receiver whose limits are at least the sender's view of them (true while limit capsules are
  in flight, since limits only increase); `onOpen_exceed`, `onData_exceed`: a stream or data
  beyond the limits is `WT_FLOW_CONTROL_ERROR`;
* `onCapsule_of_raiseStreams`, `onCapsule_of_raiseData`: the capsules of a compliant receiver
  never cause a `WT_FLOW_CONTROL_ERROR` at a sender whose view is at most the receiver's limits;
* `run_inv` (with `init_inv`): in the lockstep model, from the SETTINGS-initialised state, any
  sequence of opening, sending and limit-raising events by compliant endpoints never errors,
  and the sender's usage stays within the limits.

CHECKED: the "limit of 3" example of §5.6.2 on stream counts, and stale capsules.
-/

namespace Silmaril.Net.WebTransport

theorem SendState.onCapsule_mono {s s' : SendState} {c : WtCapsule} (h : s.onCapsule c = .ok s') :
    s.limits.Le s'.limits ∧ s'.used = s.used :=
  Silmaril.Proofs.Net.WebTransport.Flow.onCapsule_mono h

theorem SendState.onCapsule_maxStreams_stale {s : SendState} {d : Dir} {n : Nat}
    (h : n ≤ s.limits.streams d) : s.onCapsule (.maxStreams d n) = .error .flowControlError := by
  simp [SendState.onCapsule, h]

theorem SendState.onCapsule_maxData_stale {s : SendState} {n : Nat} (h : n ≤ s.limits.maxData) :
    s.onCapsule (.maxData n) = .error .flowControlError := by
  simp [SendState.onCapsule, h]

theorem SendState.tryOpen_within {s s' : SendState} {d : Dir} (hs : s.used.Within s.limits)
    (h : s.tryOpen d = some s') : s'.used.Within s'.limits :=
  Silmaril.Proofs.Net.WebTransport.Flow.tryOpen_within hs h

theorem SendState.trySend_within {s s' : SendState} {n : Nat} (hs : s.used.Within s.limits)
    (h : s.trySend n = some s') : s'.used.Within s'.limits :=
  Silmaril.Proofs.Net.WebTransport.Flow.trySend_within hs h

theorem SendState.onCapsule_within {s s' : SendState} {c : WtCapsule}
    (hs : s.used.Within s.limits) (h : s.onCapsule c = .ok s') : s'.used.Within s'.limits :=
  Silmaril.Proofs.Net.WebTransport.Flow.onCapsule_within hs h

theorem RecvState.onOpen_of_tryOpen {s s' : SendState} {r : RecvState} {d : Dir}
    (h : s.tryOpen d = some s') (hl : s.limits.Le r.limits) (hu : s.used = r.used) :
    ∃ r', r.onOpen d = .ok r' ∧ r'.used = s'.used ∧ r'.limits = r.limits :=
  Silmaril.Proofs.Net.WebTransport.Flow.onOpen_of_tryOpen h hl hu

theorem RecvState.onData_of_trySend {s s' : SendState} {r : RecvState} {n : Nat}
    (h : s.trySend n = some s') (hl : s.limits.Le r.limits) (hu : s.used = r.used) :
    ∃ r', r.onData n = .ok r' ∧ r'.used = s'.used ∧ r'.limits = r.limits :=
  Silmaril.Proofs.Net.WebTransport.Flow.onData_of_trySend h hl hu

theorem RecvState.onOpen_exceed {r : RecvState} {d : Dir} (h : r.limits.streams d ≤ r.used.opened d) :
    r.onOpen d = .error .flowControlError :=
  Silmaril.Proofs.Net.WebTransport.Flow.onOpen_exceed h

theorem RecvState.onData_exceed {r : RecvState} {n : Nat}
    (h : r.limits.maxData < r.used.dataBytes + n) : r.onData n = .error .flowControlError :=
  Silmaril.Proofs.Net.WebTransport.Flow.onData_exceed h

theorem RecvState.raiseStreams_mono {r r' : RecvState} {d : Dir} {n : Nat} {c : WtCapsule}
    (h : r.raiseStreams d n = some (r', c)) : r.limits.Le r'.limits ∧ r'.used = r.used :=
  Silmaril.Proofs.Net.WebTransport.Flow.raiseStreams_mono h

theorem RecvState.raiseData_mono {r r' : RecvState} {n : Nat} {c : WtCapsule}
    (h : r.raiseData n = some (r', c)) : r.limits.Le r'.limits ∧ r'.used = r.used :=
  Silmaril.Proofs.Net.WebTransport.Flow.raiseData_mono h

theorem SendState.onCapsule_of_raiseStreams {s : SendState} {r r' : RecvState} {d : Dir} {n : Nat}
    {c : WtCapsule} (h : r.raiseStreams d n = some (r', c)) (hl : s.limits.Le r.limits) :
    ∃ s', s.onCapsule c = .ok s' ∧ s'.used = s.used ∧ s'.limits.Le r'.limits :=
  Silmaril.Proofs.Net.WebTransport.Flow.onCapsule_of_raiseStreams h hl

theorem SendState.onCapsule_of_raiseData {s : SendState} {r r' : RecvState} {n : Nat}
    {c : WtCapsule} (h : r.raiseData n = some (r', c)) (hl : s.limits.Le r.limits) :
    ∃ s', s.onCapsule c = .ok s' ∧ s'.used = s.used ∧ s'.limits.Le r'.limits :=
  Silmaril.Proofs.Net.WebTransport.Flow.onCapsule_of_raiseData h hl

theorem System.step_inv {S : System} (hS : S.Inv) (e : Event) :
    ∃ S', S.step e = .ok S' ∧ S'.Inv :=
  Silmaril.Proofs.Net.WebTransport.Flow.step_inv hS e

theorem System.run_inv {S : System} (hS : S.Inv) (es : List Event) :
    ∃ S', S.run es = .ok S' ∧ S'.Inv :=
  Silmaril.Proofs.Net.WebTransport.Flow.run_inv hS es

theorem System.init_inv (w : WtSettings) : (System.init w).Inv :=
  Silmaril.Proofs.Net.WebTransport.Flow.init_inv w

/-- Any event sequence from the start of a session runs without a flow control error and keeps
the sender within its limits. -/
theorem System.run_init (w : WtSettings) (es : List Event) :
    ∃ S', (System.init w).run es = .ok S' ∧ S'.send.used.Within S'.send.limits :=
  let ⟨S', h, hi⟩ := System.run_inv (System.init_inv w) es
  ⟨S', h, hi.2.2⟩

/-! ## Known answers -/

/-- §5.6.2: with a unidirectional limit of 3, the sender opens three streams and is then
blocked; it can say so with WT_STREAMS_BLOCKED carrying 3. -/
example :
    let s : SendState := { limits := ⟨0, 3, 0⟩ }
    (do let s ← s.tryOpen .uni; let s ← s.tryOpen .uni; let s ← s.tryOpen .uni; s.tryOpen .uni) =
      none ∧
    (do let s ← s.tryOpen .uni; let s ← s.tryOpen .uni; s.tryOpen .uni).map
      (fun t : SendState => t.used.openedUni) =
      some 3 ∧
    s.blockedStreams .uni = .streamsBlocked .uni 3 := by decide

/-- A fourth incoming stream against a limit of 3 is `WT_FLOW_CONTROL_ERROR`. -/
example : RecvState.onOpen { limits := ⟨0, 3, 0⟩, used := { openedUni := 3 } } .uni =
    .error .flowControlError := rfl

/-- A WT_MAX_DATA that does not increase the limit is `WT_FLOW_CONTROL_ERROR` (§5.6.4). -/
example : SendState.onCapsule { limits := ⟨0, 0, 100⟩ } (.maxData 100) =
    .error .flowControlError := rfl

/-- Flow control capsules are ignored without flow control (§5.1). -/
example : SendState.onCapsuleIf false { limits := ⟨0, 0, 100⟩ } (.maxData 100) =
    .ok { limits := ⟨0, 0, 100⟩ } := rfl

end Silmaril.Net.WebTransport
