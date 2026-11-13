module

public import Silmaril.Servers.LinuxHello.Defs
public import Silmaril.Servers.Compare.Thms
public import Silmaril.Process.LPS.Table
import Silmaril.Proofs.Servers.LinuxHello.Serves
import Silmaril.Proofs.Servers.LinuxHello.Table
import Silmaril.Proofs.Servers.LinuxHello.Only

/-!
# A Linux hello server loop over LPS's socket system calls: theorems

PROVED (standard axioms):

* `serverSpec_iff`, **`L_eq_full`**: the loop's four arms are those of LPS's generic table,
  and the loop traps only with their numbers, so its socket semantics under `serverSpec` is its
  socket semantics under LPS's whole table `syscallSpec`.
* **`serves`**: `Compare.ServesHello L inp` for every invocation. For every sequence of
  requests on the wire (`Compare.WireOk`), the network whose first client sends them back to
  back and then `FIN` gives a run that accepts that one connection (on channel `3`, from
  `accept4Spec`), reads all the octets (in `read`s of at most 4096, LPS's socket `read`), and
  sends `helloWire` once per request (in `sendto`s of at most 4096 with `MSG_NOSIGNAL`). The
  octets come off the run's raw history (`Sockets.ofRecordsC`).
* **`wasi_refines_loop`**: so, on logs whose requests are on the wire, the `wasi:http` hello
  component refines this process: every such log of the component is the merged connection
  log of a run of the loop under LPS's semantics.

* `hello_prefix_err`: no strict prefix of `helloWire`'s octets frames as a response to a
  request whose method is neither `HEAD` nor `CONNECT`, after any octets; nothing frames at
  the end of the octets. (By the soundness and completeness of the head grammar: a head read
  inside a prefix of `helloWire` is `helloWire`'s head, read whole, and the 5 octets of body
  are then missing.)
* **`onlyHello_of_sentPrefix`**: for any socket semantics, if every connection's sent octets
  are a prefix of the hello responses its received octets call for (`SentPrefix`), then every
  exchange of every connection is answered `helloResp` (`Compare.OnlyHello`), short sends
  included.
* `only_of_task`, `hello_equiv_loop`: so, under the open task below, the loop only says
  hello, and it and the hello component are equivalent on logs on the wire.

OPEN (frozen): `Task.loopSentPrefix`, that the loop satisfies `SentPrefix` for every
invocation. It is an invariant over all runs under LPS's semantics: every outcome of `accept`,
`read` (short reads, `FIN`, resets) and `sendto` (short sends, `EPIPE`, resets) the loop can
meet, the descriptor table it keeps (`baseFds`, plus descriptor 4 during a connection), and
the channel of the `k`-th connection (`Sockets.kth_accept_channel`). Not done.
-/

@[expose] public section

namespace Silmaril.Servers.LinuxHello

open Silmaril.Process Silmaril.Process.LPS Silmaril.Servers.Platform Silmaril.Servers.Compare

theorem serverSpec_iff (i : SyscallInput) (m : LPS.Model) (o : Outcome SyscallEffect)
    (h : i.sysno.toNat = 202 ∨ i.sysno.toNat = 63 ∨ i.sysno.toNat = 206 ∨ i.sysno.toNat = 57) :
    serverSpec i m o ↔ syscallSpec i m o :=
  Proofs.Servers.LinuxHello.serverSpec_iff i m o h

/-- **The loop's socket semantics is the same under LPS's whole table.** -/
theorem L_eq_full :
    L = Sockets.sockSemNet launch [] syscallSpec noFilter Sockets.genericAccept
      Sockets.genericClose := by
  funext inp tr
  simp only [L, Sockets.sockSemNet, Proofs.Servers.LinuxHello.hstar_iff]

/-- **The loop serves hello on one connection**, for every invocation. -/
theorem serves (inp : Cli.Input) : ServesHello L inp :=
  Proofs.Servers.LinuxHello.serves inp

/-- **The hello component refines the loop** on logs on the wire. -/
theorem wasi_refines_loop (inp : Cli.Input) :
    Refines (restrict wasi wireLog) linux1 WasiExamples.hello (L, inp) :=
  wasi_refines_linux (serves inp)

/-- No strict prefix of `helloWire`'s octets frames as a response. -/
theorem hello_prefix_err {meth : List UInt8} (h1 : meth ≠ Net.Http1.methodHEAD)
    (h2 : meth ≠ Net.Http1.methodCONNECT) (pre p : List UInt8)
    (hp : p <+: Net.Http1.encResponse helloWire.1 helloWire.2)
    (hlt : p.length < (Net.Http1.encResponse helloWire.1 helloWire.2).length)
    (x : Wire1.WireResp) (k : Nat) :
    Net.Http1.parseResponseAt meth ⟨(pre ++ p).toArray⟩ pre.length ≠ .ok x k :=
  Proofs.Servers.LinuxHello.hello_prefix_err h1 h2 pre p hp hlt x k

/-- **Sent octets that are a prefix of the hello responses called for: only hello.** -/
theorem onlyHello_of_sentPrefix {L' : SockSem} {inp : Cli.Input} (h : SentPrefix L' inp) :
    OnlyHello L' inp :=
  fun tr htr c => Proofs.Servers.LinuxHello.connLog_hello (h tr htr c)

end Silmaril.Servers.LinuxHello

namespace Silmaril.Servers.LinuxHello.Task

/-- **Open**: the loop's sent octets are, on every connection of every run, a prefix of the
hello responses its received octets call for. -/
def loopSentPrefix : Prop := ∀ inp, SentPrefix L inp

end Silmaril.Servers.LinuxHello.Task

namespace Silmaril.Servers.LinuxHello

open Silmaril.Servers.Platform Silmaril.Servers.Compare

/-- Under `Task.loopSentPrefix`, the loop only says hello. -/
theorem only_of_task (ht : Task.loopSentPrefix) (inp : Cli.Input) : OnlyHello L inp :=
  onlyHello_of_sentPrefix (ht inp)

/-- Under `Task.loopSentPrefix`, the loop and the hello component are equivalent on logs on
the wire. -/
theorem hello_equiv_loop (ht : Task.loopSentPrefix) (inp : Cli.Input) :
    Refines (restrict wasi wireLog) (restrict linux1 wireLog) WasiExamples.hello (L, inp) ∧
      Refines (restrict linux1 wireLog) (restrict wasi wireLog) (L, inp) WasiExamples.hello :=
  hello_equiv (serves inp) (only_of_task ht inp)

end Silmaril.Servers.LinuxHello
