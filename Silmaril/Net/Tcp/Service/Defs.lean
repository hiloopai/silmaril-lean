module

/-!
# TCP: the reliable in-order byte-stream service

What TCP offers its users (RFC 9293 §2.2 "Key TCP Concepts": "TCP provides a reliable,
in-order, byte-stream service to applications"; §3.8 "Data Communication"; the SEND, RECEIVE
and CLOSE calls of §3.9.1). One direction of a connection is specified here; a connection is
two such streams (CLOSE ends only the local direction: "CLOSE means 'I have no more to send'",
§3.6, which also gives half-closed connections, §3.6.1).

* `Svc`: the state of one direction: the octets `written` by the sending user, whether it
  `closed`, the octets `read` by the receiving user so far, and whether it saw end of stream
  (`eof`).
* `SvcEv`: `write bs` (SEND), `close` (CLOSE), `read bs` (a RECEIVE returning `bs`), `eof`
  (RECEIVE reporting that the peer closed: "connection closing").
* **`SvcStep`**: a write appends while not closed; a read returns a nonempty continuation of
  what was read that is still a prefix of what was written (*in order, no loss, no
  duplication, no invention*; the chunking of reads is free); end of stream is reported only
  after the sender closed and everything written was read (*reliable*).
* `SvcSteps`: runs. `Svc.Ok s`: the safety invariant `read ≤ written` (prefix) and
  `eof → closed ∧ read = written`. `Tcp.Service.Thms` proves runs keep it and that the
  chunking of reads and writes does not matter.

The service is a safety specification; that every written octet is eventually read is a
liveness property, stated over executions of an implementation (`Tcp.Transfer`).

Not modelled yet: urgent data (§3.8.5), PUSH (§3.9.1), reset and error reports (a RST ends the
stream abnormally; ABORT), timeouts. These extend `SvcEv`.

A Silmaril addition (region `Net`, see `docs/projects/wasm-wasi.md`).
-/

@[expose] public section

namespace Silmaril.Net.Tcp

/-- **The state of one direction of a connection**, as its users see it. -/
structure Svc where
  written : List UInt8 := []
  closed : Bool := false
  read : List UInt8 := []
  eof : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- **Service events**: SEND, CLOSE, a RECEIVE returning octets, end of stream. -/
inductive SvcEv where
  | write (bs : List UInt8)
  | close
  | read (bs : List UInt8)
  | eof
  deriving DecidableEq, Repr

/-- **The byte-stream service** (one direction). -/
inductive SvcStep : Svc → SvcEv → Svc → Prop where
  | write {s : Svc} (bs : List UInt8) : s.closed = false →
      SvcStep s (.write bs) { s with written := s.written ++ bs }
  | close {s : Svc} : s.closed = false → SvcStep s .close { s with closed := true }
  | read {s : Svc} (bs : List UInt8) : bs ≠ [] → s.read ++ bs <+: s.written →
      SvcStep s (.read bs) { s with read := s.read ++ bs }
  | eof {s : Svc} : s.closed = true → s.read = s.written → s.eof = false →
      SvcStep s .eof { s with eof := true }

/-- Runs of the service. -/
inductive SvcSteps : Svc → List SvcEv → Svc → Prop where
  | refl (s : Svc) : SvcSteps s [] s
  | cons {s e s' l s''} : SvcStep s e s' → SvcSteps s' l s'' → SvcSteps s (e :: l) s''

/-- **The safety invariant**: what was read is a prefix of what was written, and end of stream
means everything written was read after a close. -/
def Svc.Ok (s : Svc) : Prop :=
  s.read <+: s.written ∧ (s.eof = true → s.closed = true ∧ s.read = s.written)

/-- A trace the service admits from the initial state. -/
def SvcAdmits (tr : List SvcEv) : Prop := ∃ s, SvcSteps {} tr s

/-- The read event of a list of octets: none for the empty list (a RECEIVE returns at least one
octet). -/
def readEv (bs : List UInt8) : List SvcEv := if bs = [] then [] else [.read bs]

end Silmaril.Net.Tcp
