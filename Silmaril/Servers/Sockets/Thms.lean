module

public import Silmaril.Servers.Sockets.Defs
import Silmaril.Proofs.Servers.Sockets.Basic

/-!
# Socket events of a Linux process: theorems

PROVED (standard axioms):

* `received_append`, `sent_append`: the octets of a connection in a concatenation.
* `received_ofEvents`, `sent_ofEvents`: the octets received (sent) on connection `c` are the
  bytes read (written) on its trace channel.
* **`received_ofRecords`**, **`sent_ofRecords`**, **`connLog_ofRecords`**: the accept events
  read from the system calls do not change the octets of any connection, so the exchanges of
  every connection under any framing depend only on the byte trace of the history.
* **`connLog_byteTrace`**: those exchanges, as a function of the bytes read and written on the
  connection's channel.
-/

@[expose] public section

namespace Silmaril.Servers.Sockets

open Silmaril.Process Silmaril.Servers.Platform

theorem received_append (c : ConnId) (a b : List SockEv) :
    received c (a ++ b) = received c a ++ received c b :=
  Proofs.Servers.Sockets.received_append c a b

theorem sent_append (c : ConnId) (a b : List SockEv) :
    sent c (a ++ b) = sent c a ++ sent c b :=
  Proofs.Servers.Sockets.sent_append c a b

theorem received_ofEvents (c : ConnId) (evs : List LPS.Event) :
    received c (ofEvents evs) = recvBytes c evs :=
  Proofs.Servers.Sockets.received_ofEvents c evs

theorem sent_ofEvents (c : ConnId) (evs : List LPS.Event) :
    sent c (ofEvents evs) = sentBytes c evs :=
  Proofs.Servers.Sockets.sent_ofEvents c evs

/-- The octets received on a connection depend only on the byte trace. -/
theorem received_ofRecords (isAccept : LPS.Word → Bool) (c : ConnId) (n : Nat)
    (h : List LPS.StepRecord) :
    received c (ofRecords isAccept n h) = recvBytes c (LPS.byteTrace h) := by
  rw [Proofs.Servers.Sockets.received_ofRecords, received_ofEvents]

/-- The octets sent on a connection depend only on the byte trace. -/
theorem sent_ofRecords (isAccept : LPS.Word → Bool) (c : ConnId) (n : Nat)
    (h : List LPS.StepRecord) :
    sent c (ofRecords isAccept n h) = sentBytes c (LPS.byteTrace h) := by
  rw [Proofs.Servers.Sockets.sent_ofRecords, sent_ofEvents]

/-- **The exchanges of a connection of a process run** are framed from the bytes read and
written on its trace channel. -/
theorem connLog_byteTrace (fr : Framing) (isAccept : LPS.Word → Bool) (n : Nat)
    (h : List LPS.StepRecord) (c : ConnId) :
    connLog fr (ofRecords isAccept n h) c =
      (fr.requests (recvBytes c (LPS.byteTrace h))).zip
        (fr.responses (fr.requests (recvBytes c (LPS.byteTrace h)))
          (sentBytes c (LPS.byteTrace h))) := by
  simp only [connLog, received_ofRecords, sent_ofRecords]

/-- The exchanges do not depend on the accept events. -/
theorem connLog_ofRecords (fr : Framing) (isAccept : LPS.Word → Bool) (n : Nat)
    (h : List LPS.StepRecord) :
    connLog fr (ofRecords isAccept n h) = connLog fr (ofEvents (LPS.byteTrace h)) := by
  funext c
  simp only [connLog, received_ofRecords, sent_ofRecords, received_ofEvents, sent_ofEvents]

end Silmaril.Servers.Sockets
