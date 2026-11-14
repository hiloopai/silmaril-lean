module

public import Silmaril.Net.WebTransport.Session.Defs
public import Silmaril.Net.WebTransport.Stream.Thms
import Silmaril.Proofs.Net.WebTransport.Session

@[expose] public section

/-!
# WebTransport session state machine: theorems (draft-ietf-webtrans-http3-17)

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/WebTransport/Session.lean`, or inline
when short):

* `step_closed`, `run_closed`: closed is terminal — no event, and no sequence of events, leaves
  it (§6);
* `run_closed_noStreams`: after termination no new stream is opened and no datagram is sent,
  whatever happens next (§6: "it MUST NOT send any new datagrams or open any new streams");
* `step_terminates`: every transition that terminates a session resets all its streams with
  WT_SESSION_GONE (§6);
* `step_closeSent_fin`: sending WT_CLOSE_SESSION closes the session and sends a FIN on the
  CONNECT stream (§6);
* `step_finReceived`: a clean FIN is exactly a WT_CLOSE_SESSION with code 0 and an empty
  message (§6);
* `closed_connectData`: data after the close on the CONNECT stream is `H3_MESSAGE_ERROR` (§6);
* `rank_step`, `rank_run`, `run_not_establishing`: the phases only move forward
  (establishing → established → draining → closed);
* `ofConnect_id`: a session's ID is its CONNECT stream's ID, a client-initiated bidirectional
  stream (§4); its datagrams name that stream (`sessionDatagram_spec` in `Stream.Thms`).

CHECKED: a session's life, a rejected session, and the §4.6 buffering rules.
-/

namespace Silmaril.Net.WebTransport

namespace SessionState

theorem step_closed (r : CloseReason) (e : SessionEvent) : (step (.closed r) e).1 = .closed r :=
  Silmaril.Proofs.Net.WebTransport.Session.step_closed r e

theorem run_closed (r : CloseReason) (es : List SessionEvent) :
    (run (.closed r) es).1 = .closed r :=
  Silmaril.Proofs.Net.WebTransport.Session.run_closed r es

theorem run_closed_noStreams (r : CloseReason) (es : List SessionEvent) :
    (run (.closed r) es).1.canOpenStream = false ∧ (run (.closed r) es).1.canSendDatagram = false := by
  rw [run_closed]; exact ⟨rfl, rfl⟩

theorem step_terminates (s : SessionState) (e : SessionEvent) (hs : s.isClosed = false)
    (h : (step s e).1.isClosed = true) : Action.resetStreams .sessionGone ∈ (step s e).2 :=
  Silmaril.Proofs.Net.WebTransport.Session.step_terminates s e hs h

theorem step_closeSent_fin (s : SessionState) (hs : s.isClosed = false) (code : Nat)
    (msg : List UInt8) :
    (step s (.closeSent code msg)).1 = .closed (.closed code msg) ∧
      Action.finConnect ∈ (step s (.closeSent code msg)).2 :=
  Silmaril.Proofs.Net.WebTransport.Session.step_closeSent_fin s hs code msg

theorem step_finReceived (s : SessionState) :
    step s .finReceived = step s (.closeReceived 0 []) :=
  Silmaril.Proofs.Net.WebTransport.Session.step_finReceived s

theorem closed_connectData (r : CloseReason) :
    step (.closed r) .connectData = (.closed r, [.resetConnect .messageError]) := rfl

theorem rank_step (s : SessionState) (e : SessionEvent) : s.rank ≤ (step s e).1.rank :=
  Silmaril.Proofs.Net.WebTransport.Session.rank_step s e

theorem rank_run (s : SessionState) (es : List SessionEvent) : s.rank ≤ (run s es).1.rank :=
  Silmaril.Proofs.Net.WebTransport.Session.rank_run s es

/-- Once past establishing, a session never returns to it. -/
theorem run_not_establishing {s : SessionState} (hs : s ≠ .establishing)
    (es : List SessionEvent) : (run s es).1 ≠ .establishing := by
  have := rank_run s es
  intro h; rw [h] at this; cases s <;> simp_all [rank]

/-- Capsules are not processed before the session is accepted (§3.2). -/
theorem establishing_noCapsules : establishing.processesCapsules = false := rfl

end SessionState

theorem Session.ofConnect_id {sid : Nat} {s : Session} (h : Session.ofConnect sid = some s) :
    s.id = sid ∧ validSessionId sid = true ∧ s.state = .establishing := by
  unfold Session.ofConnect at h; split at h <;> simp_all; exact h ▸ ⟨rfl, rfl⟩

/-! ## Examples, checked by evaluation -/

open SessionState in
/-- A session accepted with 200, drained, then closed by the peer with code 5 and "bye". -/
example : run .establishing [.response 200, .drain, .closeReceived 5 [0x62, 0x79, 0x65],
    .connectData] =
    (.closed (.closed 5 [0x62, 0x79, 0x65]),
     [.closeConnect, .resetStreams .sessionGone, .resetConnect .messageError]) := rfl

open SessionState in
/-- A 403 (failed origin check) ends the attempt; the optimistic streams are reset. -/
example : (step .establishing (.response 403)) =
    (.closed (.rejected 403), [.resetStreams .sessionGone]) := rfl

open SessionState in
/-- Streams and datagrams are allowed while draining (§4.7). -/
example : draining.canOpenStream ∧ draining.canSendDatagram := by decide

example : incomingStream none false = .buffer ∧
    incomingStream none true = .reject .bufferedStreamRejected ∧
    incomingStream (some (.closed .aborted)) false = .reject .sessionGone ∧
    incomingDatagram none true = none := by decide

example : Session.ofConnect 4 = some ⟨4, .establishing⟩ ∧ Session.ofConnect 2 = none := by decide

end Silmaril.Net.WebTransport
