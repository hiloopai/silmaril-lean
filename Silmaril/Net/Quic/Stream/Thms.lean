module

public import Silmaril.Net.Quic.Stream.Defs
import Silmaril.Proofs.Net.Quic.Stream

@[expose] public section

/-!
# QUIC stream states and final sizes: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Quic/Stream.lean`):

Sending part (§3.1, §3.3, §4.5):

* `sendStep_terminal`: "Data Recvd" and "Reset Recvd" are terminal: every permitted event
  leaves the stream unchanged;
* `sendStep_ok`, `sendSteps_ok`: the final size is known exactly after FIN or RESET_STREAM and
  then equals the number of bytes sent;
* `sendStep_finalSize`, `sendSteps_finalSize`: once known, the final size never changes;
* `sendStep_no_data`: once the final size is known, no STREAM data, STREAM_DATA_BLOCKED or
  second FIN can be sent ("An endpoint MUST NOT send data on a stream at or beyond the final
  size", §4.5; "MUST NOT send a STREAM or STREAM_DATA_BLOCKED frame for a stream in the "Reset
  Sent" state or any terminal state", §3.3);
* `sendStep_sent`: only STREAM data advances the send offset.

Receiving part (§3.2, §4.5):

* `recvStep_terminal`, `recvSteps_terminal`: "Data Read" and "Reset Read" are terminal;
* `recvStep_finalSize`, `recvSteps_finalSize`: "Once a final size for a stream is known, it
  cannot change";
* `recvStep_beyond`: data beyond the final size is FINAL_SIZE_ERROR, in every state;
* `recvStep_fin_change`, `recvStep_reset_change`: a STREAM+FIN or RESET_STREAM indicating a
  different final size is FINAL_SIZE_ERROR;
* `recvStep_fin_lower`, `recvStep_reset_lower`: a final size below data already received is
  FINAL_SIZE_ERROR;
* `recvStep_ok`, `recvSteps_ok`: the final size is known exactly outside "Recv", and the
  highest received offset never exceeds it.

CHECKED: sample runs of both machines through Figures 2 and 3.
-/

namespace Silmaril.Net.Quic

theorem sendStep_terminal {s s' : SendStream} {e : SendEvent} (ht : s.state.terminal = true)
    (h : sendStep s e = some s') : s' = s :=
  Silmaril.Proofs.Net.Quic.Stream.sendStep_terminal ht h

theorem sendStep_ok {s s' : SendStream} {e : SendEvent} (hs : s.Ok)
    (h : sendStep s e = some s') : s'.Ok :=
  Silmaril.Proofs.Net.Quic.Stream.sendStep_ok hs h

theorem sendSteps_ok {s s' : SendStream} {es : List SendEvent} (hs : s.Ok)
    (h : sendSteps s es = some s') : s'.Ok :=
  Silmaril.Proofs.Net.Quic.Stream.sendSteps_ok hs h

theorem sendStep_finalSize {s s' : SendStream} {e : SendEvent} {n : Nat} (hs : s.Ok)
    (hn : s.finalSize = some n) (h : sendStep s e = some s') : s'.finalSize = some n :=
  Silmaril.Proofs.Net.Quic.Stream.sendStep_finalSize hs hn h

theorem sendSteps_finalSize {s s' : SendStream} {es : List SendEvent} {n : Nat} (hs : s.Ok)
    (hn : s.finalSize = some n) (h : sendSteps s es = some s') : s'.finalSize = some n :=
  Silmaril.Proofs.Net.Quic.Stream.sendSteps_finalSize hs hn h

theorem sendStep_no_data {s : SendStream} {n k : Nat} (hs : s.Ok)
    (hn : s.finalSize = some n) : sendStep s (.data k) = none ∧ sendStep s .blocked = none ∧
      sendStep s .fin = none :=
  Silmaril.Proofs.Net.Quic.Stream.sendStep_no_data hs hn

theorem sendStep_sent {s s' : SendStream} {e : SendEvent} (h : sendStep s e = some s') :
    s'.sent = s.sent + (match e with | .data n => n | _ => 0) :=
  Silmaril.Proofs.Net.Quic.Stream.sendStep_sent h

theorem SendStream.ok_empty : ({} : SendStream).Ok := by
  simp [SendStream.Ok]

theorem recvStep_terminal {s s' : RecvStream} {e : RecvEvent} (ht : s.state.terminal = true)
    (h : recvStep s e = .ok s') : s'.state = s.state :=
  Silmaril.Proofs.Net.Quic.Stream.recvStep_terminal ht h

theorem recvSteps_terminal {s s' : RecvStream} {es : List RecvEvent}
    (ht : s.state.terminal = true) (h : recvSteps s es = .ok s') : s'.state = s.state :=
  Silmaril.Proofs.Net.Quic.Stream.recvSteps_terminal ht h

theorem recvStep_finalSize {s s' : RecvStream} {e : RecvEvent} {n : Nat}
    (hn : s.finalSize = some n) (h : recvStep s e = .ok s') : s'.finalSize = some n :=
  Silmaril.Proofs.Net.Quic.Stream.recvStep_finalSize hn h

theorem recvSteps_finalSize {s s' : RecvStream} {es : List RecvEvent} {n : Nat}
    (hn : s.finalSize = some n) (h : recvSteps s es = .ok s') : s'.finalSize = some n :=
  Silmaril.Proofs.Net.Quic.Stream.recvSteps_finalSize hn h

theorem recvStep_beyond {s : RecvStream} {n off len : Nat} (fin : Bool)
    (hn : s.finalSize = some n) (hb : n < off + len) :
    recvStep s (.stream off len fin) = .error .finalSizeError :=
  Silmaril.Proofs.Net.Quic.Stream.recvStep_beyond fin hn hb

theorem recvStep_fin_change {s : RecvStream} {n off len : Nat}
    (hn : s.finalSize = some n) (hb : off + len ≠ n) :
    recvStep s (.stream off len true) = .error .finalSizeError :=
  Silmaril.Proofs.Net.Quic.Stream.recvStep_fin_change hn hb

theorem recvStep_reset_change {s : RecvStream} {m n c : Nat}
    (hn : s.finalSize = some m) (hb : m ≠ n) :
    recvStep s (.resetStream c n) = .error .finalSizeError :=
  Silmaril.Proofs.Net.Quic.Stream.recvStep_reset_change hn hb

theorem recvStep_fin_lower {s : RecvStream} {off len : Nat} (hn : s.finalSize = none)
    (hb : off + len < s.highest) : recvStep s (.stream off len true) = .error .finalSizeError :=
  Silmaril.Proofs.Net.Quic.Stream.recvStep_fin_lower hn hb

theorem recvStep_reset_lower {s : RecvStream} {c n : Nat} (hn : s.finalSize = none)
    (hb : n < s.highest) : recvStep s (.resetStream c n) = .error .finalSizeError :=
  Silmaril.Proofs.Net.Quic.Stream.recvStep_reset_lower hn hb

theorem recvStep_ok {s s' : RecvStream} {e : RecvEvent} (hs : s.Ok)
    (h : recvStep s e = .ok s') : s'.Ok :=
  Silmaril.Proofs.Net.Quic.Stream.recvStep_ok hs h

theorem recvSteps_ok {s s' : RecvStream} {es : List RecvEvent} (hs : s.Ok)
    (h : recvSteps s es = .ok s') : s'.Ok :=
  Silmaril.Proofs.Net.Quic.Stream.recvSteps_ok hs h

theorem RecvStream.ok_empty : ({} : RecvStream).Ok := by
  simp [RecvStream.Ok]

/-! ## Sample runs -/

/-- Ready → Send → Data Sent → Data Recvd, 10 bytes. -/
example : sendSteps {} [.data 4, .data 6, .fin, .allAcked] =
    some { state := .dataRecvd, sent := 10, finalSize := some 10 } := by decide

/-- STOP_SENDING in "Send" forces RESET_STREAM with the peer's code (§3.5). -/
example : sendSteps {} [.data 3, .recvStopSending 0x010c, .resetAcked] =
    some { state := .resetRecvd, sent := 3, finalSize := some 3, resetCode := some 0x010c } := by
  decide

/-- No data after FIN (§4.5). -/
example : sendSteps {} [.fin, .data 1] = none := by decide

/-- Out-of-order STREAM frames, the last with FIN, then all data and the read. -/
example : recvSteps {} [.stream 5 5 true, .stream 0 5 false, .allData, .readAll] =
    .ok { state := .dataRead, highest := 10, finalSize := some 10 } := by rfl

/-- Data beyond the final size, even after the stream was read (§4.5). -/
example : recvSteps {} [.stream 0 10 true, .allData, .readAll, .stream 8 3 false] =
    .error .finalSizeError := by rfl

/-- A RESET_STREAM whose final size is below data already received. -/
example : recvSteps {} [.stream 0 10 false, .resetStream 0 5] = .error .finalSizeError := by rfl

/-- RESET_STREAM in "Recv", then the application is told. -/
example : recvSteps {} [.stream 0 3 false, .resetStream 7 3, .readReset] =
    .ok { state := .resetRead, highest := 3, finalSize := some 3, resetCode := some 7 } := by rfl

end Silmaril.Net.Quic
