module

public import Silmaril.Servers.Sockets.Defs
public import Silmaril.Servers.Compare.Defs
public import Silmaril.Process.LPS.Sys.Socket
public import Silmaril.Process.LPS.Sys.Kernel
public import Silmaril.Process.LPS.Sys.ReadWrite

/-!
# A Linux hello server loop over LPS's socket system calls

A concrete server loop run by the Linux process model (`Silmaril.Process.LPS`), with
LPS's own specifications of `accept`, `read`, `sendto` and `close` (generic numbers 202, 63,
206, 57):

```
loop:
  c := accept(3)                 -- 3: a listening socket handed over at start (socket activation)
  acc := []
  while (n := read(c, BUF, 4096)) > 0: acc := acc ++ BUF[0, n)
  if n = 0:                      -- the client finished sending (FIN)
    out := helloWire repeated k times, k = helloCount acc
    while out ≠ [] and (n := sendto(c, OUT, min(|out|, 4096), MSG_NOSIGNAL)) > 0:
      out := drop n out
  close(c)
```

`helloCount acc` frames `acc` as HTTP/1.1 requests (`Wire1.requests`, the reading
`Platform.connLog` uses) and counts the leading ones whose method is neither `HEAD` nor
`CONNECT`: those get `helloWire`; the server stops answering at the first other one. It
answers once the client has half-closed its side, a deliberately simple design: the decision
needs no reasoning about requests that are still arriving.

**The machine.** The loop is a `UserIsa` (`isa`) whose state is the loop's control point and
variables, not a binary: an instruction step is one transition of the loop in Lean, and the
memory the kernel sees is the two buffers, `BUF` (4096 writable bytes that `read` fills) and
`OUT` (4096 readable bytes holding the next chunk of pending output). The system calls,
their outcomes, the network (`IoState.net`, chosen by the environment) and the trace are LPS's.
So the theorems are about this loop under LPS's socket semantics, not about compiled code.

* `serverTable`: the four LPS arms the loop uses, with the arms of LPS's generic table
  (`Thms.serverTable_lookup`: they are the arms of `LPS.specTable`);
* `launch inp q`: the loop about to accept, with descriptor 3 a listening socket, the
  standard streams on 0–2, the connection queue `q` and the counter at `0`;
* `L`: its socket semantics over every network (`Sockets.sockSemNet`), reading `close`.

The theorems (`Thms`) discharge `Compare.ServesHello L inp` for every invocation, so the hello
component refines this process on logs on the wire (`Compare.wasi_refines_linux`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Servers.LinuxHello

open Silmaril.Process Silmaril.Process.LPS Silmaril.Servers.Platform Silmaril.Servers.Wire1
open Silmaril.Servers.Compare

/-! ## What the loop computes -/

/-- A request the loop answers: its method is neither `HEAD` nor `CONNECT`. -/
def answerable (r : Net.Http.Request) : Bool :=
  r.method.toToken != Net.Http1.methodHEAD && r.method.toToken != Net.Http1.methodCONNECT

/-- The number of `helloWire` answers for the octets received: the leading answerable
requests. -/
def helloCount (acc : List UInt8) : Nat := ((requests acc).takeWhile answerable).length

/-- `k` hello responses back to back. -/
def helloOut (k : Nat) : List UInt8 := encResponses (List.replicate k helloWire)

/-! ## The machine -/

/-- The listening descriptor handed over at start. -/
def LISTEN : Word := 3
/-- The input buffer. -/
def BUF : Word := 0x10000
/-- The output buffer. -/
def OUT : Word := 0x20000
/-- `MSG_NOSIGNAL`, the only `sendto` flag word LPS models. -/
def NOSIG : Word := 0x4000

/-- The loop's control points: a pending system call, or the transition after it returned. -/
inductive Pc where
  | accept | accepted | read | readDone | send | sent | close | closed
  deriving DecidableEq, Repr

/-- The loop's state. -/
structure St where
  pc : Pc
  conn : Word
  acc : List LPS.Byte
  out : List LPS.Byte
  ret : Word
  got : List LPS.Byte

/-- The pending system call. -/
def pending (s : St) : Option Word :=
  match s.pc with
  | .accept => some 202
  | .read => some 63
  | .send => some 206
  | .close => some 57
  | _ => none

/-- The argument registers. -/
def args (s : St) : List Word :=
  match s.pc with
  | .accept => [LISTEN, 0, 0, 0, 0, 0]
  | .read => [s.conn, BUF, BitVec.ofNat 64 4096, 0, 0, 0]
  | .send => [s.conn, OUT, BitVec.ofNat 64 (min s.out.length 4096), NOSIG, 0, 0]
  | .close => [s.conn, 0, 0, 0, 0, 0]
  | _ => [0, 0, 0, 0, 0, 0]

/-- The readable memory: the next chunk of pending output at `OUT`. -/
def readByte (s : St) (a : Word) : Option LPS.Byte :=
  if OUT.toNat ≤ a.toNat ∧ a.toNat < OUT.toNat + 4096 then
    (s.out.take 4096)[a.toNat - OUT.toNat]?
  else none

/-- The writable memory: the input buffer at `BUF`. -/
def writableByte (a : Word) : Option LPS.Byte :=
  if BUF.toNat ≤ a.toNat ∧ a.toNat < BUF.toNat + 4096 then some 0 else none

/-- The loop's transition after a system call returned. -/
def next (s : St) : St :=
  match s.pc with
  | .accepted =>
    if 0 ≤ s.ret.toInt then { s with pc := .read, conn := s.ret, acc := [], out := [] }
    else { s with pc := .accept }
  | .readDone =>
    if 0 < s.ret.toInt then { s with pc := .read, acc := s.acc ++ s.got }
    else if s.ret = 0 then
      let out := (helloOut (helloCount (s.acc.map UInt8.ofBitVec))).map UInt8.toBitVec
      { s with pc := if out = [] then .close else .send, out := out }
    else { s with pc := .close }
  | .sent =>
    if 0 < s.ret.toInt then
      let out := s.out.drop s.ret.toNat
      { s with pc := if out = [] then .close else .send, out := out }
    else { s with pc := .close }
  | .closed => { s with pc := .accept }
  | _ => s

/-- Past a system call: to the transition after it. -/
def advance (s : St) : St :=
  match s.pc with
  | .accept => { s with pc := .accepted }
  | .read => { s with pc := .readDone }
  | .send => { s with pc := .sent }
  | .close => { s with pc := .closed }
  | _ => s

/-- **The loop as a machine LPS can run.** -/
def isa : UserIsa where
  State := St
  step _ s := .ok ⟨next s, []⟩
  svcPending := pending
  syscallArgs := args
  readByte _ := readByte
  writableByte _ _ := writableByte
  applyEffect s eff := { s with ret := eff.ret, got := eff.writes.flatMap (·.2) }
  advancePastSvc := advance
  init _ _ _ _ := ⟨.accept, 0, [], [], 0, []⟩
  reportsAccesses := true
  entryFetchable _ _ := true

/-- The four arms the loop uses, as in LPS's generic table. -/
def serverTable : List SpecArm :=
  [arm 202 "accept" (fun i => accept4Spec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) 0),
   arm 63 "read" (fun i => readSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)),
   arm 206 "sendto" (fun i =>
     sendtoSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3) (i.arg 4) (i.arg 5)),
   arm 57 "close" (fun i => closeSpec (fd32 (i.arg 0)))]

/-- The system-call semantics of the loop. -/
def serverSpec : Sys SyscallEffect := dispatch serverTable

/-- The descriptors at start: the listening socket and the standard streams. -/
def baseFds : List (Word × FdEntry) :=
  [(3, .socket .listening), (0, .channel 0), (1, .channel 1), (2, .channel 2)]

/-- The kernel model at start, for the connection queue `q`. -/
def model0 (q : NetQueue) : LPS.Model :=
  (mkModel baseFds ⟨[], [], [], 0, 0, 0, 0, 0⟩ InputStream.eof [] none none none).withNet q

/-- **The loop launched**, for every invocation, on the connection queue `q`. -/
def launch (_ : Cli.Input) (q : NetQueue) : Config isa := ⟨⟨.accept, 0, [], [], 0, []⟩, model0 q⟩

/-- **The socket semantics of the loop**, over every network. -/
def L : SockSem :=
  Sockets.sockSemNet launch [] serverSpec noFilter Sockets.genericAccept Sockets.genericClose

end Silmaril.Servers.LinuxHello
