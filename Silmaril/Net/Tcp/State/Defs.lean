module

/-!
# TCP: the connection state machine (RFC 9293 §3.3.2, Figure 5)

RFC 9293 §3.3.2: "A connection progresses through a series of states during its lifetime. The
states are: LISTEN, SYN-SENT, SYN-RECEIVED, ESTABLISHED, FIN-WAIT-1, FIN-WAIT-2, CLOSE-WAIT,
CLOSING, LAST-ACK, TIME-WAIT, and the fictional state CLOSED." "The events are the user calls,
OPEN, SEND, RECEIVE, CLOSE, ABORT, and STATUS; the incoming segments, particularly those
containing the SYN, ACK, RST, and FIN flags; and timeouts."

* `State`: the eleven states. SYN-RECEIVED records whether it was reached from LISTEN (a
  passive OPEN): Note 1 of Figure 5 makes the RST transition depend on it.
* `Event`: the events of Figure 5 (user calls, segment arrivals, the 2 MSL timeout).
* `Action`: what the transition sends (`snd SYN`, `snd SYN,ACK`, `snd ACK`, `snd FIN`,
  `snd RST`) or nothing.
* **`Step s e a s'`**: the transitions of Figure 5, one constructor per arrow, plus its notes:
  Note 1 (SYN-RECEIVED → LISTEN on RST after a passive OPEN), Note 2 (FIN-WAIT-1 → TIME-WAIT
  when a FIN arrives that also acknowledges ours), Note 3 (receipt of a RST leads to LISTEN or
  CLOSED; a RST may be sent from any state with a transition to TIME-WAIT), and the ABORT call
  (§3.10.5: a RST is sent in the synchronized states, the TCB is deleted). LISTEN ignores an
  incoming RST (§3.10.7.2). The diagram "is only a summary and must not be taken as the total
  specification": the segment-arrival processing of §3.10.7 refines it, and is the next step of
  the formalization (`docs/projects/wasm-wasi.md`).
* `next s e`: the deterministic part (every arrow of the figure, not the RST and ABORT
  alternatives), as a function; `Tcp.State.Thms` proves `Step` contains it.
* `Steps`: runs of transitions.
* State classes: `synchronized` (ESTABLISHED and later, §3.5.2), `finSent` (our FIN is sent),
  `finRcvd` (the peer's FIN is received), `canSend` (SEND is accepted on a connection,
  §3.10.2), `canRecvData` (new data from the peer can still arrive).

A Silmaril addition (region `Net`, see `docs/projects/wasm-wasi.md`).
-/

@[expose] public section

namespace Silmaril.Net.Tcp

/-- **The connection states** (RFC 9293 §3.3.2). -/
inductive State where
  | closed
  | listen
  | synSent
  /-- SYN-RECEIVED; `passive`: reached from LISTEN (Figure 5, Note 1). -/
  | synRcvd (passive : Bool)
  | established
  | finWait1
  | finWait2
  | closeWait
  | closing
  | lastAck
  | timeWait
  deriving DecidableEq, Repr

/-- **The events of Figure 5.** -/
inductive Event where
  | passiveOpen
  | activeOpen
  | send
  | close
  | abort
  | rcvSyn
  | rcvSynAck
  | rcvAckOfSyn
  | rcvFin
  | rcvAckOfFin
  /-- A FIN that also acknowledges our FIN (Note 2). -/
  | rcvFinAckOfFin
  | rcvRst
  | timeout2Msl
  deriving DecidableEq, Repr

/-- **What a transition sends.** -/
inductive Action where
  | none
  | sndSyn
  | sndSynAck
  | sndAck
  | sndFin
  | sndRst
  deriving DecidableEq, Repr

/-- The synchronized states (RFC 9293 §3.5.2: ESTABLISHED, FIN-WAIT-1, FIN-WAIT-2,
CLOSE-WAIT, CLOSING, LAST-ACK, TIME-WAIT). -/
def State.synchronized : State → Bool
  | .established | .finWait1 | .finWait2 | .closeWait | .closing | .lastAck | .timeWait => true
  | _ => false

/-- **The arrows of Figure 5**, as a partial function. -/
def next : State → Event → Option (Action × State)
  | .closed, .passiveOpen => some (.none, .listen)
  | .closed, .activeOpen => some (.sndSyn, .synSent)
  | .listen, .rcvSyn => some (.sndSynAck, .synRcvd true)
  | .listen, .send => some (.sndSyn, .synSent)
  | .listen, .close => some (.none, .closed)
  | .synSent, .rcvSyn => some (.sndSynAck, .synRcvd false)
  | .synSent, .rcvSynAck => some (.sndAck, .established)
  | .synSent, .close => some (.none, .closed)
  | .synRcvd _, .rcvAckOfSyn => some (.none, .established)
  | .synRcvd _, .close => some (.sndFin, .finWait1)
  | .established, .close => some (.sndFin, .finWait1)
  | .established, .rcvFin => some (.sndAck, .closeWait)
  | .finWait1, .rcvAckOfFin => some (.none, .finWait2)
  | .finWait1, .rcvFin => some (.sndAck, .closing)
  | .finWait1, .rcvFinAckOfFin => some (.sndAck, .timeWait)
  | .finWait2, .rcvFin => some (.sndAck, .timeWait)
  | .closeWait, .close => some (.sndFin, .lastAck)
  | .closing, .rcvAckOfFin => some (.none, .timeWait)
  | .lastAck, .rcvAckOfFin => some (.none, .closed)
  | .timeWait, .timeout2Msl => some (.none, .closed)
  | _, _ => none

/-- **The transitions** of Figure 5 with its notes and the ABORT call. -/
inductive Step : State → Event → Action → State → Prop where
  /-- An arrow of the figure. -/
  | arrow {s e a s'} : next s e = some (a, s') → Step s e a s'
  /-- Note 1: SYN-RECEIVED after a passive OPEN returns to LISTEN on a RST. -/
  | rstPassive : Step (.synRcvd true) .rcvRst .none .listen
  /-- Note 3: a RST received in any state other than CLOSED and LISTEN leads to CLOSED. -/
  | rstClosed {s} : s ≠ .closed → s ≠ .listen → Step s .rcvRst .none .closed
  /-- §3.10.7.2: in LISTEN an incoming RST is ignored. -/
  | rstListen : Step .listen .rcvRst .none .listen
  /-- ABORT (§3.10.5) in a synchronized state or SYN-RECEIVED: send a RST, delete the TCB. -/
  | abortRst {s} : (s.synchronized ∨ ∃ p, s = .synRcvd p) → Step s .abort .sndRst .closed
  /-- ABORT in LISTEN or SYN-SENT: delete the TCB, nothing is sent. -/
  | abortQuiet {s} : (s = .listen ∨ s = .synSent) → Step s .abort .none .closed
  /-- Note 3: a RST can be sent from any state, with a transition to TIME-WAIT. -/
  | rstTimeWait {s} : s ≠ .closed → Step s .abort .sndRst .timeWait

/-- **Runs** of transitions, with their events and actions. -/
inductive Steps : State → List (Event × Action) → State → Prop where
  | refl (s) : Steps s [] s
  | cons {s e a s' l s''} : Step s e a s' → Steps s' l s'' → Steps s ((e, a) :: l) s''

/-- Our FIN has been sent. -/
def State.finSent : State → Bool
  | .finWait1 | .finWait2 | .closing | .lastAck | .timeWait => true
  | _ => false

/-- The peer's FIN has been received. -/
def State.finRcvd : State → Bool
  | .closeWait | .closing | .lastAck | .timeWait => true
  | _ => false

/-- SEND is accepted on an open connection (§3.10.2: ESTABLISHED and CLOSE-WAIT; it is queued in
LISTEN, SYN-SENT and SYN-RECEIVED). -/
def State.canSend : State → Bool
  | .established | .closeWait => true
  | _ => false

/-- New data from the peer can still arrive and be delivered. -/
def State.canRecvData : State → Bool
  | .synRcvd _ | .established | .finWait1 | .finWait2 => true
  | _ => false

end Silmaril.Net.Tcp
