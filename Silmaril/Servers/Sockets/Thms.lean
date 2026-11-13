module

public import Silmaril.Servers.Sockets.Defs
public import Silmaril.Process.LPS.Sys.Socket
public import Silmaril.Process.LPS.Sys.Kernel
public import Silmaril.Process.LPS.Table
import Silmaril.Proofs.Servers.Sockets.Basic
import Silmaril.Proofs.Servers.Sockets.Run

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
* **`accept4Spec_ok`**: a successful `accept`/`accept4` of LPS advances the connection counter
  by one, takes the head of the network queue, emits nothing, and installs under the returned
  descriptor a connected socket on trace channel `connChannel ix = ix + 3`, `ix` the counter
  before the call.
* **`connIx_hstar`**: along every run of a table that counts connections (`CountsConns`), the
  counter after a history is the counter before plus the number of successful accepts in it
  (modulo `2^64`). With `accept4Spec_ok`: **the `k`-th successful accept of a run started
  with counter `0` installs the connection of channel `k + 3`** (`kth_accept_channel`). The
  ofRecords numbering of `accept` events is therefore LPS's channel numbering, for every table
  that counts connections; for LPS's whole table that is the open `Task.specTableCountsConns`.
* `closeSpec_ok`, `recvfromSpec_ok`, `recvmsgSpec_ok`: a `close` emits no byte event and
  changes no I/O state (a successful one removes the descriptor); a `recvfrom` or `recvmsg`
  that returns emits no byte event and changes nothing (on a socket LPS declines it; every
  return is an errno). So reading `recvfrom` records as nothing is exact for LPS, and the bytes
  of any call that does deliver them are read from its events.
* `received_ofRecordsC`, `sent_ofRecordsC`, **`connLog_ofRecordsC`**: reading `close` too
  (`ofRecordsC`) changes no connection's octets, hence no exchange.

OPEN (frozen): `Task.specTableCountsConns`, that LPS's generic table counts connections: every
arm other than `accept`/`accept4` leaves `IoState.connIx` alone. It needs a pass over the
table's arms; nothing here depends on it unconditionally.
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

/-! ## Accepts and channels -/

/-- **A successful accept installs the connection of channel `connIx + 3`.** -/
theorem accept4Spec_ok {fd addrp addrlenp flags : LPS.Word} {i : LPS.SyscallInput} {m : LPS.Model}
    {eff : LPS.SyscallEffect} {m' : LPS.Model} {evs : List LPS.Event}
    (h : LPS.accept4Spec fd addrp addrlenp flags i m (.ok eff m' evs)) (hr : 0 ≤ eff.ret.toInt) :
    m'.io.connIx = m.io.connIx + 1 ∧ evs = [] ∧ m'.io.net = LPS.nqRest m.io.net ∧
      LPS.fdLookup m'.fd.table eff.ret =
        some (.socket (.connected (LPS.nqPeer m.io.net) (LPS.connChannel m.io.connIx)
          (LPS.nqScript m.io.net))) :=
  Proofs.Servers.Sockets.accept4Spec_ok h hr

/-- **The connection counter counts the accepts of a run.** -/
theorem connIx_hstar {isa : LPS.UserIsa} {segs : List LPS.Segment}
    {spec : LPS.Sys LPS.SyscallEffect} {refused : LPS.RefusalFilter} {isAccept : LPS.Word → Bool}
    (hc : CountsConns spec isAccept) {c c' : LPS.Config isa} {h : List LPS.StepRecord}
    (s : LPS.HStar segs spec refused c h c') :
    c'.model.io.connIx.toNat = (c.model.io.connIx.toNat + acceptCount isAccept h) % 2 ^ 64 :=
  Proofs.Servers.Sockets.connIx_hstar hc s

/-- **The `k`-th accept is the connection of channel `k + 3`**: in a run started with the
counter at `0` under a table that counts connections, the counter before an accept is the
number of accepts before it (as a 64-bit word: the counter wraps where LPS's `accept` stops,
`connIxExhausted`). -/
theorem kth_accept_channel {isa : LPS.UserIsa} {segs : List LPS.Segment}
    {spec : LPS.Sys LPS.SyscallEffect} {refused : LPS.RefusalFilter} {isAccept : LPS.Word → Bool}
    (hc : CountsConns spec isAccept) {c c' : LPS.Config isa} {h : List LPS.StepRecord}
    (s : LPS.HStar segs spec refused c h c') (h0 : c.model.io.connIx = 0) :
    LPS.connChannel c'.model.io.connIx = LPS.connChannel (acceptCount isAccept h : LPS.Word) := by
  have := connIx_hstar hc s
  rw [h0] at this
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [this]

theorem closeSpec_ok {fd : LPS.Word} {i : LPS.SyscallInput} {m : LPS.Model}
    {eff : LPS.SyscallEffect} {m' : LPS.Model} {evs : List LPS.Event}
    (h : LPS.closeSpec fd i m (.ok eff m' evs)) :
    evs = [] ∧ m'.io = m.io ∧ (eff.ret = 0 → m'.fd.table = LPS.fdRemove m.fd.table fd) :=
  Proofs.Servers.Sockets.closeSpec_ok h

theorem recvfromSpec_ok {fd buf size : LPS.Word} {i : LPS.SyscallInput} {m : LPS.Model}
    {eff : LPS.SyscallEffect} {m' : LPS.Model} {evs : List LPS.Event}
    (h : LPS.recvfromSpec fd buf size i m (.ok eff m' evs)) : evs = [] ∧ m' = m :=
  Proofs.Servers.Sockets.recvfromSpec_ok h

theorem recvmsgSpec_ok {fd flags : LPS.Word} {i : LPS.SyscallInput} {m : LPS.Model}
    {eff : LPS.SyscallEffect} {m' : LPS.Model} {evs : List LPS.Event}
    (h : LPS.recvmsgSpec fd flags i m (.ok eff m' evs)) : evs = [] ∧ m' = m :=
  Proofs.Servers.Sockets.recvmsgSpec_ok h

/-! ## `close` read -/

theorem received_ofRecordsC (isAccept isClose : LPS.Word → Bool) (c : ConnId) (n : Nat)
    (fds : List (LPS.Word × ConnId)) (h : List LPS.StepRecord) :
    received c (ofRecordsC isAccept isClose n fds h) = recvBytes c (LPS.byteTrace h) := by
  rw [Proofs.Servers.Sockets.received_ofRecordsC, received_ofEvents]

theorem sent_ofRecordsC (isAccept isClose : LPS.Word → Bool) (c : ConnId) (n : Nat)
    (fds : List (LPS.Word × ConnId)) (h : List LPS.StepRecord) :
    sent c (ofRecordsC isAccept isClose n fds h) = sentBytes c (LPS.byteTrace h) := by
  rw [Proofs.Servers.Sockets.sent_ofRecordsC, sent_ofEvents]

/-- **Reading `close` changes no exchange.** -/
theorem connLog_ofRecordsC (fr : Framing) (isAccept isClose : LPS.Word → Bool) (n : Nat)
    (fds : List (LPS.Word × ConnId)) (h : List LPS.StepRecord) :
    connLog fr (ofRecordsC isAccept isClose n fds h) = connLog fr (ofRecords isAccept n h) := by
  funext c
  simp only [connLog, received_ofRecordsC, sent_ofRecordsC, received_ofRecords, sent_ofRecords]

/-- The trace of a run of `sockSem` and the same run read with `close` have the same exchanges;
so `sockSemNet` over the constant queue has the exchanges of `sockSem`. -/
theorem sockSemNet_const_connLog {isa : LPS.UserIsa} (launch : Cli.Input → LPS.Config isa)
    (segs : List LPS.Segment) (spec : LPS.Sys LPS.SyscallEffect) (refused : LPS.RefusalFilter)
    (isAccept isClose : LPS.Word → Bool) (fr : Framing) (inp : Cli.Input) (tr : List SockEv)
    (ht : sockSemNet (fun inp _ => launch inp) segs spec refused isAccept isClose inp tr) :
    ∃ tr', sockSem launch segs spec refused isAccept inp tr' ∧ connLog fr tr = connLog fr tr' :=
  let ⟨_, h, c, hs, e⟩ := ht
  ⟨_, ⟨h, c, hs, rfl⟩, by rw [e, connLog_ofRecordsC]⟩

end Silmaril.Servers.Sockets

namespace Silmaril.Servers.Sockets.Task

open Silmaril.Process

/-- **Open**: LPS's generic syscall table counts connections. -/
def specTableCountsConns : Prop := CountsConns LPS.syscallSpec genericAccept

end Silmaril.Servers.Sockets.Task
