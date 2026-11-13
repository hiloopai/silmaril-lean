module

public import Silmaril.Servers.Platform.Defs
public import Silmaril.Process.LPS.Behaviour

/-!
# Socket events of a Linux process, read off its system-call history

The Linux process model (`Silmaril.Process.LPS`, a Lean translation of the LPS specification
of Linux system calls) records a finite run as a raw history of steps (`StepRecord`): an
instruction, or a system call with its number, arguments, chosen effect and the byte events it
emitted (`LPS.Event`: `readEv ch b`, `writeEv ch b` on a trace channel). A connection handed
over by `accept` gets the trace channel `connChannel ix = ix + 3`, where `ix` counts the
connections accepted so far, past stdin, stdout and stderr; `read` on a connected socket emits
one `readEv` per byte received, and `write`/`sendto` one `writeEv` per byte the kernel took.

This module reads a raw history as the socket events of `Silmaril.Servers.Platform.SockEv`:

* `connOf ch`: the connection of a trace channel (`ch - 3` for `ch ≥ 3`);
* `ofEvents`: received and sent bytes on connection channels become `recv` and `send` events,
  one byte each;
* `ofRecords isAccept`: a successful call of an accept system call (`isAccept` its number,
  `genericAccept` for the generic Linux table that `Silmaril.Process.LPS.Table` follows,
  `x86Accept` for x86-64) is an `accept` of the next connection, numbered in accept order,
  as `connChannel` numbers them;
* `sockSem launch segs spec refused isAccept`: the socket semantics (`Platform.SockSem`) of a
  program whose initial process configuration for an invocation is `launch`: the socket
  traces of its finite runs (`HStar`).

The theorems (`Thms`) show that the octets received and sent on each connection, hence the
exchanges any framing reads (`connLog`), depend only on the byte trace (`byteTrace`).

Not read: `close` (a descriptor is closed, but the record does not name the connection),
`recvfrom`/`recvmsg`, which LPS leaves unmodelled on sockets, and connection-level errors.
That the `k`-th successful accept is the connection of channel `k + 3` is how LPS numbers
channels (`connChannel`, `accept4Spec`); it is assumed here, not proved from the process
semantics.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Servers.Sockets

open Silmaril.Process Silmaril.Servers.Platform

/-- The connection of a trace channel: channels `0`, `1`, `2` are the standard streams. -/
def connOf (ch : LPS.Word) : Option ConnId := if 3 ≤ ch.toNat then some (ch.toNat - 3) else none

/-- A byte of the process model as an octet. -/
def byte (b : LPS.Byte) : UInt8 := UInt8.ofBitVec b

/-- The socket events of one byte event. -/
def ofEvent : LPS.Event → List SockEv
  | .readEv ch b => match connOf ch with
    | some c => [.recv c [byte b]]
    | none => []
  | .writeEv ch b => match connOf ch with
    | some c => [.send c [byte b]]
    | none => []
  | _ => []

/-- The socket events of a byte trace. -/
def ofEvents (evs : List LPS.Event) : List SockEv := evs.flatMap ofEvent

/-- The bytes a byte trace received on connection `c`. -/
def recvBytes (c : ConnId) (evs : List LPS.Event) : List UInt8 :=
  evs.flatMap fun
    | .readEv ch b => if connOf ch = some c then [byte b] else []
    | _ => []

/-- The bytes a byte trace sent on connection `c`. -/
def sentBytes (c : ConnId) (evs : List LPS.Event) : List UInt8 :=
  evs.flatMap fun
    | .writeEv ch b => if connOf ch = some c then [byte b] else []
    | _ => []

/-- The accept system calls of the generic Linux table: `accept` (202), `accept4` (242). -/
def genericAccept (no : LPS.Word) : Bool := no == 202 || no == 242

/-- The accept system calls of x86-64: `accept` (43), `accept4` (288). -/
def x86Accept (no : LPS.Word) : Bool := no == 43 || no == 288

/-- A record is a successful accept: a call of an accept system call whose return value is
not an error (errors are the negative values). An `exit` or `killed` record of an accept number
counts too, so that counting accepts matches the kernel's connection counter on every record
(`CountsConns`); `accept` never halts the process, so such records do not arise from it. -/
def accepts (isAccept : LPS.Word → Bool) : LPS.StepRecord → Bool
  | .syscall no _ eff _ | .exit no _ eff _ _ | .killed no _ eff _ _ =>
    isAccept no && decide (0 ≤ eff.ret.toInt)
  | .instr => false

/-- **The socket events of a raw history**, the next connection to be accepted numbered `n`. -/
def ofRecords (isAccept : LPS.Word → Bool) : Nat → List LPS.StepRecord → List SockEv
  | _, [] => []
  | n, r :: rs =>
    if accepts isAccept r then .accept n :: (ofEvents r.events ++ ofRecords isAccept (n + 1) rs)
    else ofEvents r.events ++ ofRecords isAccept n rs

/-- **The socket semantics of a process**: started for an invocation in the configuration
`launch`, its socket traces are those of its finite runs. -/
def sockSem {isa : LPS.UserIsa} (launch : Cli.Input → LPS.Config isa) (segs : List LPS.Segment)
    (spec : LPS.Sys LPS.SyscallEffect) (refused : LPS.RefusalFilter)
    (isAccept : LPS.Word → Bool) : SockSem :=
  fun inp tr => ∃ h c, LPS.HStar segs spec refused (launch inp) h c ∧ tr = ofRecords isAccept 0 h

/-! ## Counting accepts: the `k`-th accept is the connection of channel `k + 3` -/

/-- The number of successful accepts in a raw history. -/
def acceptCount (isAccept : LPS.Word → Bool) (h : List LPS.StepRecord) : Nat :=
  (h.filter (accepts isAccept)).length

/-- **A syscall table counts connections** when every outcome it allows advances the model's
connection counter (`IoState.connIx`) by one for a successful accept and leaves it unchanged
otherwise. `Thms.accept4Spec_ok` proves the accept half for LPS's `accept4Spec`; that every
other arm of a table leaves the counter alone is the property of the table (for LPS's whole
table it is `Task.specTableCountsConns`). -/
def CountsConns (spec : LPS.Sys LPS.SyscallEffect) (isAccept : LPS.Word → Bool) : Prop :=
  ∀ i m eff m' evs, spec i m (.ok eff m' evs) →
    m'.io.connIx =
      if isAccept i.sysno && decide (0 ≤ eff.ret.toInt) then m.io.connIx + 1 else m.io.connIx

/-! ## Reading `close` -/

/-- The return value of a record that returned to the program. -/
def retOf : LPS.StepRecord → Option LPS.Word
  | .syscall _ _ eff _ => some eff.ret
  | _ => none

/-- The descriptor a record closed: a successful (`0`) call of a close system call
(`isClose` its number: `genericClose` or `x86Close`), the descriptor read as the kernel reads
it (`fd32`, the low 32 bits). -/
def closedFd (isClose : LPS.Word → Bool) : LPS.StepRecord → Option LPS.Word
  | .syscall no args eff _ =>
    if isClose no && eff.ret == 0 then some (LPS.fd32 (args.getD 0 0)) else none
  | _ => none

/-- `close` (57) in the generic Linux table. -/
def genericClose (no : LPS.Word) : Bool := no == 57

/-- `close` (3) on x86-64. -/
def x86Close (no : LPS.Word) : Bool := no == 3

/-- **The socket events of a raw history, `close` read too.** `fds` maps the descriptors that
accepts returned to their connections; a successful `close` of a mapped descriptor is a
`close` of its connection, and unmaps it. The bytes are read as by `ofRecords`. -/
def ofRecordsC (isAccept isClose : LPS.Word → Bool) :
    Nat → List (LPS.Word × ConnId) → List LPS.StepRecord → List SockEv
  | _, _, [] => []
  | n, fds, r :: rs =>
    if accepts isAccept r then
      .accept n :: (ofEvents r.events ++
        ofRecordsC isAccept isClose (n + 1) ((((retOf r).getD 0), n) :: fds) rs)
    else
      match (closedFd isClose r).bind fun fd => (fds.lookup fd).map (fd, ·) with
      | some (fd, c) =>
        ofEvents r.events ++ .close c :: ofRecordsC isAccept isClose n
          (fds.filter fun p => p.1 != fd) rs
      | none => ofEvents r.events ++ ofRecordsC isAccept isClose n fds rs

/-! ## The network as the environment's choice -/

/-- **The socket semantics of a process over every network.** `launch inp q` is the initial
configuration for an invocation with the queue `q` of incoming connections (LPS's
`ProcInput.net`); the network is the environment's choice, so the socket traces are those of
the finite runs from every queue. `close` is read (`ofRecordsC`).

`sockSem` fixes the queue with the invocation; a hypothesis such as
`Compare.ServesHello`, which asks for *every* sequence of requests to be served, cannot hold
of it, since one queue carries one sequence of octets per connection. -/
def sockSemNet {isa : LPS.UserIsa} (launch : Cli.Input → LPS.NetQueue → LPS.Config isa)
    (segs : List LPS.Segment) (spec : LPS.Sys LPS.SyscallEffect) (refused : LPS.RefusalFilter)
    (isAccept isClose : LPS.Word → Bool) : SockSem :=
  fun inp tr => ∃ q h c, LPS.HStar segs spec refused (launch inp q) h c ∧
    tr = ofRecordsC isAccept isClose 0 [] h

end Silmaril.Servers.Sockets
