module

public import Silmaril.Net.Tcp.Seq.Defs
public import Silmaril.Net.Tcp.State.Defs
public import Silmaril.Net.Tcp.Service.Defs
public import Silmaril.Net.Tcp.Header.Defs

/-!
# TCP: a connection transferring one stream, over a loose network

A model of one connection between an active opener `A`, which sends a stream of octets, and a
passive opener `B`, which receives it, following RFC 9293: the three-way handshake (§3.5),
data transfer with sequence numbers (§3.4, §3.8), and the close in both directions (§3.6).
The network between them is the loose channel of `Silmaril.Net.Channel`: a segment once sent may
be received any number of times, in any order, or never (§3.8: TCP "must recover from data
that is damaged, lost, duplicated, or delivered out of order"). In the state of the system,
`ab` and `ba` are the segments ever sent in each direction; receiving does not remove them.

* `Seg`: the fields of a segment the model uses (sequence and acknowledgment numbers, SYN, ACK,
  FIN, data); `Seg.toSegment` puts them in the wire format of `Tcp.Header`.
* `Snd` (endpoint `A`): its state (`State`), initial send sequence number `iss`, the octets
  its user wrote (`buf`), whether its user closed, and its RCV.NXT for `B`'s sequence space.
  Sequence number `iss` is the SYN, `iss + 1 + i` the `i`-th octet of `buf`, and
  `iss + 1 + |buf|` the FIN (§3.4: "the SYN is considered to occur before the first actual
  data octet", "the FIN is considered to occur after the last actual data octet").
* `Rcv` (endpoint `B`): its state, initial sequence number, RCV.NXT, the octets delivered to its
  user and whether it reported end of stream.
* **`TStep s l s'`**: one transition of `A`, of `B` or of nobody else, labelled by the service
  events `l` it performs (`Tcp.Service`). The rules follow Figure 5 (open, handshake, close,
  TIME-WAIT) and §3.10.7.4 for data: `B` accepts a segment whose sequence number is RCV.NXT,
  delivers its data, advances RCV.NXT by its length (data and FIN) and acknowledges. `A` may
  (re)transmit any slice of its stream at any time while connected (retransmission, §3.8.1,
  with no timer: any schedule is allowed).
* `writeOk`: the stream of `A` stays shorter than `2^32 - 2` octets, so that sequence numbers
  of one connection never wrap around onto older ones. This replaces the bound on segment
  lifetime and the quiet time of §3.4.2-§3.4.3 (see `Tcp.Transfer.Thms`: without it the
  receiver can accept stale data, `wrap_unsafe`).

Simplifications (each a legal implementation choice or a restriction of the model, recorded in
`docs/projects/wasm-wasi.md`): `B` sends no data (the other direction is the same model with roles
swapped); segments that do not start at RCV.NXT are ignored rather than trimmed or queued
(§3.10.7.4 says they SHOULD be held: a performance matter); windows, RST, urgent data and
options are not modelled; an ACK from `B` does not shorten `A`'s retransmissions.

A Silmaril addition (region `Net`, see `docs/projects/wasm-wasi.md`).
-/

@[expose] public section

namespace Silmaril.Net.Tcp

open Silmaril.Net.Ip

/-- **A segment**, the fields this model uses. -/
structure Seg where
  seq : SeqNum
  ack : SeqNum := 0
  syn : Bool := false
  ackf : Bool := false
  fin : Bool := false
  data : List UInt8 := []
  deriving DecidableEq, Repr

/-- The wire format of a segment, between the given ports, with the given window. -/
def Seg.toSegment (g : Seg) (sp dp : Port) (window : UInt16) : Segment :=
  ⟨⟨sp, dp, g.seq, g.ack, 0, { syn := g.syn, ack := g.ackf, fin := g.fin }, window, 0, 0, []⟩,
   g.data⟩

/-- **The sending endpoint `A`.** -/
structure Snd where
  st : State := .closed
  iss : SeqNum
  buf : List UInt8 := []
  closed : Bool := false
  rnxt : SeqNum := 0
  deriving DecidableEq, Repr

/-- **The receiving endpoint `B`.** -/
structure Rcv where
  st : State := .listen
  iss : SeqNum
  nxt : SeqNum := 0
  delivered : List UInt8 := []
  eof : Bool := false
  deriving DecidableEq, Repr

/-- **The system**: both endpoints and the segments ever sent each way. -/
structure Sys where
  a : Snd
  b : Rcv
  ab : List Seg := []
  ba : List Seg := []
  deriving DecidableEq, Repr

/-- The initial system: `A` CLOSED with initial sequence number `issA`, `B` in LISTEN (after a
passive OPEN) with `issB`. -/
def Sys.init (issA issB : SeqNum) : Sys := ⟨{ iss := issA }, { iss := issB }, [], []⟩

namespace Snd

/-- `A`'s SYN. -/
def synSeg (a : Snd) : Seg := { seq := a.iss, syn := true }

/-- `A`'s pure acknowledgment. -/
def ackSeg (a : Snd) : Seg := { seq := SeqNum.adv a.iss (1 + a.buf.length), ack := a.rnxt, ackf := true }

/-- `A`'s segment carrying the `n` octets of its stream from offset `o`. -/
def dataSeg (a : Snd) (o n : Nat) : Seg :=
  { seq := SeqNum.adv a.iss (1 + o), ack := a.rnxt, ackf := true, data := (a.buf.drop o).take n }

/-- `A`'s FIN, after the last octet of its stream. -/
def finSeg (a : Snd) : Seg :=
  { seq := SeqNum.adv a.iss (1 + a.buf.length), ack := a.rnxt, ackf := true, fin := true }

end Snd

namespace Rcv

/-- `B`'s SYN,ACK. -/
def synAckSeg (b : Rcv) : Seg := { seq := b.iss, ack := b.nxt, syn := true, ackf := true }

/-- `B`'s acknowledgment of everything received. -/
def ackSeg (b : Rcv) : Seg := { seq := SeqNum.adv b.iss 1, ack := b.nxt, ackf := true }

/-- `B`'s FIN (it sends no data). -/
def finSeg (b : Rcv) : Seg := { seq := SeqNum.adv b.iss 1, ack := b.nxt, ackf := true, fin := true }

end Rcv

/-- How far a segment advances RCV.NXT: its data, and one for a FIN (§3.4, SEG.LEN). -/
def Seg.len (g : Seg) : Nat := g.data.length + (if g.fin then 1 else 0)

/-- A write that keeps the stream within the sequence space of one connection. -/
def writeOk (a : Snd) (bs : List UInt8) : Prop := a.buf.length + bs.length + 2 < 2 ^ 32

/-- **The transitions of the connection**, labelled by the service events they perform. -/
inductive TStep : Sys → List SvcEv → Sys → Prop where
  /-- `A`: active OPEN, snd SYN (Figure 5). -/
  | aOpen {s : Sys} : s.a.st = .closed →
      TStep s [] { s with a := { s.a with st := State.synSent }, ab := s.a.synSeg :: s.ab }
  /-- `A`: retransmit the SYN. -/
  | aResendSyn {s : Sys} : s.a.st = .synSent → TStep s [] { s with ab := s.a.synSeg :: s.ab }
  /-- `A`'s user writes (SEND; queued in any state before CLOSE). -/
  | aWrite {s : Sys} (bs : List UInt8) : s.a.closed = false → writeOk s.a bs →
      TStep s [.write bs] { s with a := { s.a with buf := s.a.buf ++ bs } }
  /-- `A`: rcv SYN,ACK acknowledging its SYN, snd ACK, ESTABLISHED. -/
  | aSynAck {s : Sys} {g : Seg} : s.a.st = .synSent → g ∈ s.ba → g.syn = true → g.ackf = true →
      g.ack = SeqNum.adv s.a.iss 1 →
      TStep s []
        { s with
          a := { s.a with st := State.established, rnxt := SeqNum.adv g.seq 1 }
          ab := ({ s.a with rnxt := SeqNum.adv g.seq 1 } : Snd).ackSeg :: s.ab }
  /-- `A`: (re)transmit `n` octets from offset `o`. -/
  | aSend {s : Sys} (o n : Nat) : (s.a.st = .established ∨ s.a.st = .finWait1) →
      o + n ≤ s.a.buf.length → TStep s [] { s with ab := s.a.dataSeg o n :: s.ab }
  /-- `A`'s user closes: snd FIN, FIN-WAIT-1. -/
  | aClose {s : Sys} : s.a.st = .established → s.a.closed = false →
      TStep s [.close]
        { s with
          a := { s.a with st := State.finWait1, closed := true }
          ab := s.a.finSeg :: s.ab }
  /-- `A`: retransmit the FIN. -/
  | aResendFin {s : Sys} : s.a.st = .finWait1 → TStep s [] { s with ab := s.a.finSeg :: s.ab }
  /-- `A`: rcv ACK of FIN, FIN-WAIT-2. -/
  | aAckOfFin {s : Sys} {g : Seg} : s.a.st = .finWait1 → g ∈ s.ba → g.ackf = true →
      g.fin = false → g.ack = SeqNum.adv s.a.iss (2 + s.a.buf.length) →
      TStep s [] { s with a := { s.a with st := State.finWait2 } }
  /-- `A`: rcv FIN (in FIN-WAIT-2, or in FIN-WAIT-1 when it also acknowledges `A`'s FIN,
  Note 2), snd ACK, TIME-WAIT. -/
  | aFin {s : Sys} {g : Seg} :
      (s.a.st = .finWait2 ∨
        (s.a.st = .finWait1 ∧ g.ackf = true ∧ g.ack = SeqNum.adv s.a.iss (2 + s.a.buf.length))) →
      g ∈ s.ba → g.fin = true → g.seq = s.a.rnxt →
      TStep s []
        { s with
          a := { s.a with st := State.timeWait, rnxt := SeqNum.adv s.a.rnxt 1 }
          ab := ({ s.a with rnxt := SeqNum.adv s.a.rnxt 1 } : Snd).ackSeg :: s.ab }
  /-- `A`: the 2 MSL timeout, CLOSED. -/
  | aTimeout {s : Sys} : s.a.st = .timeWait → TStep s [] { s with a := { s.a with st := State.closed } }
  /-- `B`: rcv SYN in LISTEN, snd SYN,ACK, SYN-RECEIVED. -/
  | bSyn {s : Sys} {g : Seg} : s.b.st = .listen → g ∈ s.ab → g.syn = true →
      TStep s []
        { s with
          b := { s.b with st := .synRcvd true, nxt := SeqNum.adv g.seq 1 }
          ba := ({ s.b with nxt := SeqNum.adv g.seq 1 } : Rcv).synAckSeg :: s.ba }
  /-- `B`: retransmit the SYN,ACK. -/
  | bResendSynAck {s : Sys} : s.b.st = .synRcvd true →
      TStep s [] { s with ba := s.b.synAckSeg :: s.ba }
  /-- `B`: rcv ACK of SYN, ESTABLISHED. -/
  | bAck {s : Sys} {g : Seg} : s.b.st = .synRcvd true → g ∈ s.ab → g.syn = false →
      g.ackf = true → g.ack = SeqNum.adv s.b.iss 1 →
      TStep s [] { s with b := { s.b with st := State.established } }
  /-- `B`: rcv the segment starting at RCV.NXT: deliver its data, advance RCV.NXT, snd ACK;
  on a FIN report end of stream and go to CLOSE-WAIT. -/
  | bData {s : Sys} {g : Seg} : s.b.st = .established → g ∈ s.ab → g.syn = false →
      g.seq = s.b.nxt → (g.data ≠ [] ∨ g.fin = true) →
      TStep s (readEv g.data ++ (if g.fin then [.eof] else []))
        { s with
          b := { s.b with
            st := if g.fin then .closeWait else .established
            nxt := SeqNum.adv s.b.nxt g.len
            delivered := s.b.delivered ++ g.data
            eof := g.fin }
          ba := ({ s.b with nxt := SeqNum.adv s.b.nxt g.len } : Rcv).ackSeg :: s.ba }
  /-- `B`: retransmit its ACK. -/
  | bSendAck {s : Sys} : s.b.st = .established ∨ s.b.st = .closeWait →
      TStep s [] { s with ba := s.b.ackSeg :: s.ba }
  /-- `B`'s user closes: snd FIN, LAST-ACK. -/
  | bClose {s : Sys} : s.b.st = .closeWait →
      TStep s [] { s with b := { s.b with st := State.lastAck }, ba := s.b.finSeg :: s.ba }
  /-- `B`: retransmit its FIN. -/
  | bResendFin {s : Sys} : s.b.st = .lastAck → TStep s [] { s with ba := s.b.finSeg :: s.ba }
  /-- `B`: rcv ACK of FIN, CLOSED. -/
  | bAckOfFin {s : Sys} {g : Seg} : s.b.st = .lastAck → g ∈ s.ab → g.syn = false →
      g.ackf = true → g.ack = SeqNum.adv s.b.iss 2 →
      TStep s [] { s with b := { s.b with st := State.closed } }

/-- **Runs** of the connection, with the concatenation of their service events. -/
inductive TSteps : Sys → List SvcEv → Sys → Prop where
  | refl (s : Sys) : TSteps s [] s
  | cons {s l s' m s''} : TStep s l s' → TSteps s' m s'' → TSteps s (l ++ m) s''

/-- **What the users see**: the service state of the stream from `A` to `B`. -/
def Sys.svc (s : Sys) : Svc := ⟨s.a.buf, s.a.closed, s.b.delivered, s.b.eof⟩

/-! ## Actions and the liveness target -/

/-- **The actions of the connection**: the rules of `TStep` with their parameters. -/
inductive Act where
  | aOpen
  | aResendSyn
  | aWrite (bs : List UInt8)
  | aSynAck (g : Seg)
  | aSend (o n : Nat)
  | aClose
  | aResendFin
  | aAckOfFin
  | aFin (g : Seg)
  | aTimeout
  | bSyn (g : Seg)
  | bResendSynAck
  | bAck
  | bData (g : Seg)
  | bSendAck
  | bClose
  | bResendFin
  | bAckOfFin
  deriving DecidableEq, Repr

/-- The state an action leads to (its guard is that of the `TStep` rule: `Act.Enabled`). -/
def Act.result (s : Sys) : Act → Sys
  | .aOpen => { s with a := { s.a with st := State.synSent }, ab := s.a.synSeg :: s.ab }
  | .aResendSyn => { s with ab := s.a.synSeg :: s.ab }
  | .aWrite bs => { s with a := { s.a with buf := s.a.buf ++ bs } }
  | .aSynAck g =>
    { s with
      a := { s.a with st := State.established, rnxt := SeqNum.adv g.seq 1 }
      ab := ({ s.a with rnxt := SeqNum.adv g.seq 1 } : Snd).ackSeg :: s.ab }
  | .aSend o n => { s with ab := s.a.dataSeg o n :: s.ab }
  | .aClose =>
    { s with
      a := { s.a with st := State.finWait1, closed := true }
      ab := s.a.finSeg :: s.ab }
  | .aResendFin => { s with ab := s.a.finSeg :: s.ab }
  | .aAckOfFin => { s with a := { s.a with st := State.finWait2 } }
  | .aFin _ =>
    { s with
      a := { s.a with st := State.timeWait, rnxt := SeqNum.adv s.a.rnxt 1 }
      ab := ({ s.a with rnxt := SeqNum.adv s.a.rnxt 1 } : Snd).ackSeg :: s.ab }
  | .aTimeout => { s with a := { s.a with st := State.closed } }
  | .bSyn g =>
    { s with
      b := { s.b with st := State.synRcvd true, nxt := SeqNum.adv g.seq 1 }
      ba := ({ s.b with nxt := SeqNum.adv g.seq 1 } : Rcv).synAckSeg :: s.ba }
  | .bResendSynAck => { s with ba := s.b.synAckSeg :: s.ba }
  | .bAck => { s with b := { s.b with st := State.established } }
  | .bData g =>
    { s with
      b := { s.b with
        st := if g.fin then .closeWait else .established
        nxt := SeqNum.adv s.b.nxt g.len
        delivered := s.b.delivered ++ g.data
        eof := g.fin }
      ba := ({ s.b with nxt := SeqNum.adv s.b.nxt g.len } : Rcv).ackSeg :: s.ba }
  | .bSendAck => { s with ba := s.b.ackSeg :: s.ba }
  | .bClose => { s with b := { s.b with st := State.lastAck }, ba := s.b.finSeg :: s.ba }
  | .bResendFin => { s with ba := s.b.finSeg :: s.ba }
  | .bAckOfFin => { s with b := { s.b with st := State.closed } }

/-- An action is enabled when its rule allows the transition to its result. -/
def Act.Enabled (x : Act) (s : Sys) : Prop := ∃ l, TStep s l (x.result s)

/-- The actions of the users (SEND and CLOSE): not subject to fairness. -/
def Act.user : Act → Bool
  | .aWrite _ | .aClose | .bClose => true
  | _ => false

/-- An execution: each state is the last one, or the result of an enabled action on it. -/
def Exec (σ : Nat → Sys) : Prop :=
  ∀ i, σ (i + 1) = σ i ∨ ∃ x : Act, x.Enabled (σ i) ∧ σ (i + 1) = x.result (σ i)

/-- **Weak fairness** of every protocol action (not the users'): an action enabled at every
state from some point on is eventually taken. Network fairness is part of it: receiving a
segment that stays in flight is the action `bData g` (or `aSynAck g`, …). -/
def Fair (σ : Nat → Sys) : Prop :=
  ∀ (x : Act), x.user = false → ∀ i, (∀ j ≥ i, x.Enabled (σ j)) →
    ∃ j ≥ i, σ (j + 1) = x.result (σ j)

/-- **OPEN TARGET (liveness of the byte stream)**: in every fair execution from the initial
state, every octet written is eventually delivered, and a CLOSE is eventually followed by end
of stream. Not proved; `Tcp.Transfer.Thms.can_deliver` proves the reachability core. -/
def Task.tcpStreamLive : Prop :=
  ∀ (σ : Nat → Sys) (issA issB : SeqNum), σ 0 = Sys.init issA issB → Exec σ → Fair σ →
    ∀ i, ∃ j ≥ i, (σ i).a.buf <+: (σ j).b.delivered ∧
      ((σ i).a.closed = true → (σ j).b.eof = true)

end Silmaril.Net.Tcp
