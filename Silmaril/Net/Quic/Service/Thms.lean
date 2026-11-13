module

public import Silmaril.Net.Quic.Service.Defs
import Silmaril.Proofs.Net.Quic.Service

@[expose] public section

/-!
# The QUIC stream service: theorems and the reference implementation

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Quic/Service.lean`):

* `halfStep_ok`, `connStep_ok`, `connSteps_ok`: the service keeps `Conn.Ok`: on every stream
  direction what the receiver read is a prefix of what the sender wrote, end of stream comes
  only after FIN with everything read, reset/stop signals carry the other side's codes, a
  stream never both ends and reports a reset, unopened streams and the non-sending direction of
  unidirectional streams carry nothing, at most the granted number of streams is opened, and
  no datagram is received more often than it was sent;
* `StreamService.reachable_spec`, `StreamService.reachable_ok`: **every implementation
  satisfying the `StreamService` assumption shows its applications only service runs, so the
  above holds in every reachable state**;
* `HalfImpl.step_sound`, `HalfImpl.transmit_sound`, `ConnImpl.step_sound`,
  `ConnImpl.internal_sound`: the reference implementation (sender buffers, `RecvBuffer`
  reassembly fed by arbitrary retransmitted slices, a lossy reordering datagram network)
  refines the service, so `reference` is a `StreamService` without further assumptions;
* `HalfImpl.transmit_all`: once every written byte has been transmitted, everything written is
  deliverable (the reference implementation is not vacuous).

CHECKED: a run of the reference half with out-of-order transmission.
-/

namespace Silmaril.Net.Quic.Service

theorem halfStep_ok {h h' : Half} {e : HalfEv} (hok : h.Ok) (hs : HalfStep h e h') : h'.Ok :=
  Silmaril.Proofs.Net.Quic.Service.halfStep_ok hok hs

theorem connStep_ok {c c' : Conn} {e : ConnEv} (hok : c.Ok) (hs : ConnStep c e c') : c'.Ok :=
  Silmaril.Proofs.Net.Quic.Service.connStep_ok hok hs

theorem connSteps_ok {c c' : Conn} {es : List ConnEv} (hok : c.Ok) (hs : ConnSteps c es c') :
    c'.Ok :=
  Silmaril.Proofs.Net.Quic.Service.connSteps_ok hok hs

theorem Conn.initial_ok (limit : StreamType → Nat) (dg : Bool) : (Conn.initial limit dg).Ok :=
  Silmaril.Proofs.Net.Quic.Service.initial_ok limit dg

theorem StreamService.reachable_spec (S : StreamService) {s : S.State} (h : S.Reachable s) :
    S.Inv s ∧ ∃ es, ConnSteps (S.view S.init) es (S.view s) :=
  Silmaril.Proofs.Net.Quic.Service.reachable_spec S h

theorem StreamService.reachable_ok (S : StreamService) {s : S.State} (h : S.Reachable s) :
    (S.view s).Ok :=
  Silmaril.Proofs.Net.Quic.Service.reachable_ok S h

theorem HalfImpl.step_sound {h h' : HalfImpl} {e : HalfEv} (hi : h.Inv)
    (hs : h.step e = some h') : HalfStep h.view e h'.view ∧ h'.Inv :=
  Silmaril.Proofs.Net.Quic.Service.halfImpl_step hi hs

theorem HalfImpl.transmit_sound {h h' : HalfImpl} {off len : Nat} (hi : h.Inv)
    (hs : h.transmit off len = some h') : h'.view = h.view ∧ h'.Inv :=
  Silmaril.Proofs.Net.Quic.Service.halfImpl_transmit hi hs

theorem HalfImpl.transmit_all {h h' : HalfImpl} (hi : h.Inv)
    (hs : h.transmit 0 h.written.length = some h') : contiguous h'.buf.segs = h.written :=
  Silmaril.Proofs.Net.Quic.Service.halfImpl_transmit_all hi hs

theorem ConnImpl.step_sound {c c' : ConnImpl} {e : ConnEv} (hi : c.Inv)
    (hs : c.step e = some c') : ConnStep c.view e c'.view ∧ c'.Inv :=
  Silmaril.Proofs.Net.Quic.Service.connImpl_step hi hs

theorem ConnImpl.internal_sound {c c' : ConnImpl} (hi : c.Inv) (hs : ConnImpl.Internal c c') :
    c'.view = c.view ∧ c'.Inv :=
  Silmaril.Proofs.Net.Quic.Service.connImpl_internal hi hs

theorem ConnImpl.initial_inv (limit : StreamType → Nat) (dg : Bool) :
    (ConnImpl.initial limit dg).Inv :=
  Silmaril.Proofs.Net.Quic.Service.connImpl_initial_inv limit dg

/-- **The reference implementation of the stream service**, for the given initial stream
limits and datagram support. -/
def reference (limit : StreamType → Nat) (datagrams : Bool) : StreamService where
  State := ConnImpl
  init := ConnImpl.initial limit datagrams
  Inv := ConnImpl.Inv
  view := ConnImpl.view
  step := ConnImpl.step
  internal := ConnImpl.Internal
  init_inv := ConnImpl.initial_inv limit datagrams
  init_ok := Conn.initial_ok limit datagrams
  step_inv hi hs := (ConnImpl.step_sound hi hs).2
  step_sound hi hs := (ConnImpl.step_sound hi hs).1
  internal_inv hi hs := (ConnImpl.internal_sound hi hs).2
  internal_view hi hs := (ConnImpl.internal_sound hi hs).1

/-! ## A run of the reference half -/

/-- Write "abc", the network delivers "bc" first: nothing can be read; then "a" arrives and the
application reads "abc" in one piece. -/
example : (do
    let h ← HalfImpl.step {} (.write [97, 98, 99])
    let h ← h.transmit 1 2
    let blocked := (h.step (.read [98, 99])).isNone
    let h ← h.transmit 0 1
    let h ← h.step (.read [97, 98, 99])
    let h ← h.step .finish
    let h ← h.step .eof
    pure (blocked, h.view.read, h.view.eof)) = some (true, [97, 98, 99], true) := by decide

/-- End of stream is not reported while data is missing. -/
example : (do
    let h ← HalfImpl.step {} (.write [97])
    let h ← h.step .finish
    pure (h.step .eof).isNone) = some true := by decide

/-- A reset is reported with the sender's code, and only then. -/
example : (do
    let h ← HalfImpl.step {} (.reset 0x010c)
    pure ((h.step (.resetSeen 0x010c)).isSome, (h.step (.resetSeen 7)).isNone)) =
    some (true, true) := by decide

end Silmaril.Net.Quic.Service
